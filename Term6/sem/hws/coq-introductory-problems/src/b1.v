(********************)

(* The final goal of the exercise is to implement a dictionary (aka map).
   We'll do this incrementally by defining auxiliary functions and testing them. *)


Require Import List.
Import ListNotations. 

(* The mechanism of sections allows to modularize the proof in multiple ways.
   We'll see its applications along the way. *)
Section NatEq.

  (* Implement a function that checks the equality of two natural numbers. 
     Use pattern matching and recursion. *)
  Fixpoint nat_eq (x y: nat): bool
    := match x, y with
    | 0, 0 => true
    | S x1, S x2 => nat_eq x1 x2
    | _, _ => false
    end.
 (* Replace the previous line with ':= (your implementation) . ' *)

  (* We're not _proving_ that our implementations are correct yet,
     but we can still test them on some inputs. *)
  (* Do not modify these test suits. *)
  (* Try to understand the meaning of the 'nat_eq_tests' definition. *)
  (* To do that, you may want to investigate the 'forallb': *)
  Print forallb. 
  Let nat_eq_tests := forallb id
                       [ nat_eq 0 0;
                         negb (nat_eq 0 1);
                         negb (nat_eq 10 0);
                         nat_eq 10 10;
                         negb (nat_eq 10 13) ].

  (* Do not modify these '*_pass' definitions and proofs.  *)
  (* If your implementations are correct, the execution of them should proceed, *)
  (* otherwise an error should occur.  *)
  Let nat_eq_tests_pass: nat_eq_tests = true.
  Proof. tauto. Qed.

  (* Now try to remove one of 'negb' in 'nat_eq_tests' definitions *)
  (* and execute nat_eq_tests_pass. *)
  (* Don't forget to restore the initial state of 'nat_eq_tests'. *)
  
End NatEq.

(* The section hides 'Let' definitions. *)
Fail Print nat_eq_tests_pass. 
Print nat_eq.


Section Option. 

  (* A value of 'option' type instantiated with an arbitrary type A
     contains either a value of the type A or a special value None. *)
  Print option. 
  
  (* Implement a function that checks if an optional actually contains a value. *)
  (* Use 'if-then-else' syntax: *)
  (* For a value 't' of an inductive type T with exactly two constructors T1 and T2, 
     an expression 'if t then X1 else X2' is equivalent to  
     'match t with 
      | T1 => X1
      | T2 => X2
      end' *)
  Definition has_some {A: Type} (o: option A) : bool
  := if o then true else false.
 (* Replace the previous line with ':= (your implementation) . ' *)
    
  Let has_some_tests := forallb id
                       [
                         (* here A = nat is inferred because of (1: nat) *)
                         has_some (Some 1);
                       (* note that without an argument we can't automatically infer the type *)
                         negb (has_some (@None nat));
                         has_some (Some (@None bool))
                       ].
  
  Let has_some_tests_pass: has_some_tests = true.
  Proof. tauto. Qed.

  (* Implement a function that compares two optional natural numbers. *)
  (* Reuse the nat_eq you've defined before *)
  Definition option_nat_eq (o1 o2: option nat) : bool
  := match (o1, o2) with
     | (Some n1, Some n2) => nat_eq n1 n2
     | (None, None) => true
     | (_, _) => false
     end.
 (* Replace the previous line with ':= (your implementation) . ' *)

  Let option_nat_eq_tests := forallb id
                                     [option_nat_eq None None;
                                     negb (option_nat_eq (Some 5) None);
                                     option_nat_eq (Some 5) (Some 5)
                                     ]. 

  Let option_nat_eq_tests_pass: option_nat_eq_tests = true.
  Proof. tauto. Qed.
                                     
End Option.

Section FunUpd.
  
  (* A handy primitive we'll use below is the function update. *)
  (* Essentially, we'd like to take a function and override its value on a single input. *)
  (* Here we'll only concentrate on functions whose input type is nat, 
     but which are still polymorphic on the output type. *)
  (* Implement the function update using if-then-else expression and nat_eq. *)
  Definition upd {V: Type} (f: nat -> V) (x: nat) (y: V): nat -> V
  := fun a => if nat_eq x a then y else f a.
 (* Replace the previous line with ':= (your implementation) . ' *)
  
  Let upd_tests := forallb id
                           [
                             nat_eq ((upd id 5 3) 5) 3;
                             nat_eq ((upd (upd id 5 3) 5 7) 5) 7;
                             nat_eq ((upd id 5 3) 123) 123;
                             nat_eq ((upd (upd id 5 3) 7 10) 5) 3
                           ]. 

  Let upd_tests_pass: upd_tests = true.
  Proof. tauto. Qed.

End FunUpd.  

Section NatDict.
  (* Now we're ready to provide the first implementation of a dictionary. *)
  (* We'll work with dictionaries whose keys are natural numbers 
     and values have an arbitrary (but uniform) type. *)
  
  (* Remember that in previous sections we had to specify arguments like '{A: Type}' to keep the definitions polymorphic. *)
  (* Instead of repeating them, we can specify that a particular type is a common argument for all functions in this section. *)  
  Context {V: Type}. 

  (* The first implementation of dictionary is based on partial functions. *)
  (* Remember that in Coq all functions are total, 
     that is, the function should return a value for all inputs. *)
  (* If we're to implement a dictionary with a total function, it wont' be clear
     how to represent a missing value. *)
  (* But the absence of a value is naturally represented with None, 
     while a value 'v' contained in a dictionary can be wrapped in 'Some v' *)
  Definition nat_dict_fun := nat -> option V.
  Print nat_dict_fun. (* Note that here V is fixed *)
  
  (* Implement a function that creates an empty dictionary *)
  Definition new_dict' : nat_dict_fun
  := fun _ => None.
 (* Replace the previous line with ':= (your implementation) . ' *)
  
  (* Implement an insertion using the 'upd' construct. *)
  Definition insert' (d: nat_dict_fun) (k: nat) (v: V) : nat_dict_fun
  := upd d k (Some v).
 (* Replace the previous line with ':= (your implementation) . ' *)
  
  (* Implement a deletion similarly. *)
  Definition remove' (d: nat_dict_fun) (k: nat) : nat_dict_fun
  := upd d k None.
 (* Replace the previous line with ':= (your implementation) . ' *)
  
  (* Implement a function that retrieves a value by key. *)
  (* Note that here the usage of option as a return type 
     is not due to the partial function implementation,
     but rather due to a common sense: 
     if a dictionary (with an arbitrary implementation) doesn't contain a value,
     a retrieval method should somehow reflect it. *)
  Definition get' (d: nat_dict_fun) (k: nat) : option V
  := d k.
 (* Replace the previous line with ':= (your implementation) . ' *)
  
  (* Implement a function that checks the presence of a given key. *)
  (* You can either reuse existing dict methods or write an independent implementation. *)
  Definition contains' (d: nat_dict_fun) (k: nat): bool
  := has_some (get' d k).
 (* Replace the previous line with ':= (your implementation) . ' *)
  
End NatDict.

Section NatDictTests.

  Print nat_dict_fun. (* note that now nat_dict_fun is polymorphic on value type *)

  (* To save some space we'll define common terms and reuse them
     with 'let .. in ..' syntax. *)
  Let tests :=
    (* Note that we must specify the value type for an empty dictionary,
       since there are no arguments which can be used to infer it *)
    let new := @new_dict' nat in
    let ins5 := insert' new 5 10 in
    let ins5ins5 := insert' ins5 5 15 in
    let ins5rm5 := remove' ins5 5 in
    let ins5ins5rm5 := remove' ins5ins5 5 in
    forallb id
                       [ 
                         negb (contains' new 5);
                         contains' ins5 5;
                         contains' ins5ins5 5;
                         negb (contains' ins5rm5 5);
                         negb (contains' ins5ins5rm5 5);
                         option_nat_eq (get' new 5) None;
                         option_nat_eq (get' ins5 5) (Some 10);
                         option_nat_eq (get' ins5ins5 5) (Some 15);
                         option_nat_eq (get' ins5ins5rm5 5) None;
                         option_nat_eq (get' ins5 3) None
                       ].

  Let nat_dict_fun_tests_pass: tests = true.
  Proof. tauto. Qed.
  
End NatDictTests.


Section NatDict'.
  Context {V: Type}.

  (* The other implementation of a dictionary is based on a list
     that stores pairs of keys and values. *)
  (* If there are multiple pairs with the same key, 
     the one closer to the list head is used. *)
  
  (* '*' in context of types means the product (aka pair) type. *)
  Definition nat_dict_list := list (nat * V). 

  (* Since the functions below operate on list which is defined inductively, 
     some of them should also be inductively defined. *)
  
  (* Implement a function that creates an empty dictionary. *)
  Definition new_dict'' : nat_dict_list
  := [].
 (* Replace the previous line with ':= (your implementation) . ' *)
  
  (* Implement the insertion *)
  Definition insert'' (d: nat_dict_list) (k: nat) (v: V) : nat_dict_list
  := cons (k, v) d.
 (* Replace the previous line with ':= (your implementation) . ' *)
  
  
  (* Implement the deletion. *)
  (* Mind the case when the list contain multple occurences of the same key. *)
  (* You may find useful that a pattern to be matched can be complex: *)
  (*    '(k, v) :: d'     destructs the list into the head and tail (named d')
     and, additionally, destructs the head into the key 'k' and value 'v' *)  
  Fixpoint remove'' (d: nat_dict_list) (k: nat) : nat_dict_list
    := match d with
       | cons ((k', v) as e) r =>
           let r' := remove'' r k
           in if nat_eq k' k
              then r'
              else cons e r'
       | [] => []
       end.
 (* Replace the previous line with ':= (your implementation) . ' *)

  (* Implement the retrieval function. *)
  Fixpoint get'' (d: nat_dict_list) (k: nat) : option V
  := match d with
     | cons (k', v) r =>
         if nat_eq k' k
         then Some v
         else get'' r k
     | [] => None
     end.
 (* Replace the previous line with ':= (your implementation) . ' *)

  (* Implement the check for key presence. *)
  Fixpoint contains'' (d: nat_dict_list) (k: nat): bool
  := has_some (get'' d k).
 (* Replace the previous line with ':= (your implementation) . ' *)
     
End NatDict'.

Section NatDict'Tests.

  (* The tests here are the same as for the previous implementation. *)
  Let tests :=
    let new := @new_dict'' nat in
    let ins5 := insert'' new 5 10 in
    let ins5ins5 := insert'' ins5 5 15 in
    let ins5rm5 := remove'' ins5 5 in
    let ins5ins5rm5 := remove'' ins5ins5 5 in
    forallb id
                       [ 
                         negb (contains'' new 5);
                         contains'' ins5 5;
                         contains'' ins5ins5 5;
                         negb (contains'' ins5rm5 5);
                         negb (contains'' ins5ins5rm5 5);
                         option_nat_eq (get'' new 5) None;
                         option_nat_eq (get'' ins5 5) (Some 10);
                         option_nat_eq (get'' ins5ins5 5) (Some 15);
                         option_nat_eq (get'' ins5ins5rm5 5) None;
                         option_nat_eq (get'' ins5 3) None
                       ].

  Let nat_dict_list_tests_pass: tests = true.
  Proof. tauto. Qed.
  
End NatDict'Tests.



(* The tasks below are additional and not required. *)



(* As you can see, these two implementations comply to the same interface. *)
(* Yet, since their types are different, we had to write separate test suites, 
   despite they're essentially the same. *)
(* Functional languages allow to specify a general interface with typeclasses. *)
Section DictGeneral.

  (* General interface for a dict polymorphic on value type. *)
  (* This actually defines a type whose elements are interface implementations. *)
  Class Dict := {
    D: Type -> Type; 
    new_dict: forall (V: Type), D V;
    insert: forall {V: Type}, (D V) -> nat -> V -> (D V);
    remove: forall {V: Type}, (D V) -> nat -> (D V);
    get: forall {V: Type}, (D V) -> nat -> option V;
    contains: forall {V: Type}, (D V) -> nat -> bool;
  }.

  (* Now we can specify expected behavior on the level of this interface. *)
  (* The argument is an arbitrary dict implementation. *)
  Let dict_tests (DictImpl: Dict) : bool :=
    let new := @new_dict DictImpl nat in
    let ins5 := insert new 5 10 in
    let ins5ins5 := insert ins5 5 15 in
    let ins5rm5 := remove ins5 5 in
    let ins5ins5rm5 := remove ins5ins5 5 in
    forallb id
                       [
                         negb (contains new 5);
                         contains ins5 5;
                         contains ins5ins5 5;
                         negb (contains ins5rm5 5);
                         negb (contains ins5ins5rm5 5);
                         option_nat_eq (get new 5) None;
                         option_nat_eq (get ins5 5) (Some 10);
                         option_nat_eq (get ins5ins5 5) (Some 15);
                         option_nat_eq (get ins5ins5rm5 5) None;
                         option_nat_eq (get ins5 3) None
                       ].
            
  (* Now we can state that our function-based implementation 
     complies to Dict interface. *)
  Instance FunDict: Dict := {
    D := @nat_dict_fun;
    new_dict := @new_dict';
    insert := @insert';
    remove := @remove';
    get := @get';
    contains := @contains';
  }.                       
                       

  (* Define instance of Dict class for the list-based implementation. *)
   
      (* place your code here *)
  
  (* Then, state and prove 'fun_dict_tests' and 'list_dict_tests' lemmas
     by instantiating 'dict_tests' with instances you've just created. 
     These lemmas, as before, should be proved just by 'tauto'. *)

      (* place your code here *)
 
End DictGeneral.
