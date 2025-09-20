(* Here we'll prove properties of your function-based implementation of dictionary. *)
Require Import b1.
(* If you find out that your implementation is incorrect, 
   go back to the previous file, fix it, 
   then run 'make' and restart this proof to load the new implementation. *)

(* You can do the exercises in the order they appear
   or jump straight into the NatDictProofs section
   and prove the previous statements when needed. *)

(* Tacticts needed for this exercises:
   - General-purpose tactics usable both in goal and premises
     - rewrite
     - apply
     - destruct
     - unfold
   - Tactics working with the goal:
     - intros   
     - left / right
     - exfalso   
     - split
     - simpl
   - Tactics that finish the proof (besides 'apply'):
     - inversion
       this is a general tactic, but for now we just derive contradictions with it
     - reflexivity
 *)

(* Tactics cheatsheet:
   https://www.cs.cornell.edu/courses/cs3110/2018sp/a5/coq-tactics-cheatsheet.html
*)


Section IfProofs.

  (* Show the following helper lemmas. *)
  (* Use 'rewrite' tactic to simplify the 'if' expression *)
  
  Lemma if_true_helper {A: Type} (b: bool) (a1 a2: A) (TRUE: b = true):
    (if b then a1 else a2) = a1.
  Proof.
    rewrite TRUE.
    reflexivity.
  Qed. 

  Lemma if_false_helper {A: Type} (b: bool) (a1 a2: A) (FALSE: b = false):
    (if b then a1 else a2) = a2.
  Proof.
   rewrite FALSE. 
   reflexivity.
  Qed.

End IfProofs.

Section LogicProofs.

  Lemma neg_equiv (P Q: Prop) (EQUIV: P <-> Q):
    not P <-> not Q.
  Proof.
    Locate "<->".
    Print iff.
    unfold iff.
    unfold iff in EQUIV.

    Restart.

    unfold iff in *.
    destruct EQUIV as [pq qp].
    split.
    { intros np.
      Locate "~".
      Print not.
      unfold not in *. intros q.
      apply np. apply qp. apply q. }

    intros nq p. apply nq, pq, p.
  Qed.

  (* Show that boolean has only two values. 
     Use 'destruct' tactic to perform case splitting. 
     It will generate one goal per splitting result.
     To select the next goal, use '-' (see the proof above). *)
  Lemma bool_true_or_false (b: bool):
    b = true \/ b = false.
  Proof.
    destruct b.
    - left. reflexivity.
    - right. reflexivity.
  Qed.
  
  (* Show the equivalence of two notions of boolean being false. 
     An equivalence can be proven by showing two corresponding implications.
     To introduce the premise of an implication, use 'intros name' (picking the 'name' appropriately). 
     Remember that you can use general-purpose tactics with 'in' modifier
     which allows to perform the corresponding action in the proof context. 
*)
  Lemma false_is_not_true (b: bool):
    b = false <-> b <> true.
  Proof.
    unfold iff.
    split; intros b_false.

    { rewrite b_false. unfold not.
      intros f_eq_t. inversion f_eq_t. }

    unfold not in b_false.
    destruct b.
    { exfalso. apply b_false. reflexivity. }
    reflexivity.
  Qed.
  
End LogicProofs.   

Section NatEqProofs.

  (* This proof involves induction which we'll cover at the next seminar. *)
  Lemma nat_eq_refl (n: nat):
    nat_eq n n = true.
  Proof.
    induction n as [| n IHn].
    { simpl. reflexivity. }
    simpl. apply IHn. 
  Qed.
        
  (* Here we give the specification to the 'nat_eq' function.
     That is, we precisely relate the output of 'nat_eq' function 
     and properties of its arguments. *)

  (* So far we're only able to prove the half of the specification. *)
  Lemma eq_implies_nat_eq (n1 n2: nat):
    n1 = n2 -> nat_eq n1 n2 = true.
  Proof.
    intros eq_ns.
    rewrite eq_ns.
    apply nat_eq_refl.
  Qed.

  (* This part of the specification, again, involves induction. *)
  Lemma nat_eq_implies_eq (n1 n2: nat):
    nat_eq n1 n2 = true -> n1 = n2.
  Proof.
    generalize dependent n2. induction n1.
    { intros. simpl in H. destruct n2; auto. inversion H. }
    intros. destruct n2; simpl in H. 
    { inversion H. }
    apply IHn1 in H. rewrite H. reflexivity.
  Qed.

  (* Finally, this is the specification of 'nat_eq'. *)
  Lemma nat_eq_spec (n1 n2: nat):
    nat_eq n1 n2 = true <-> n1 = n2.
  Proof.
    unfold iff.
    split.
    - apply nat_eq_implies_eq.
    - apply eq_implies_nat_eq.
  Qed.

  (* This is an obvious reformulation of 'nat_eq' specification.
     The specification, however, cannot be directly applied to prove this version.
     Fortunately, by this moment we have auxiliary statements
     that will eventually allow to reuse the specification.
     One way to prove this will be to show equivalence 
     via an intermediate assertion.
     To do this, start with the 'iff_trans' lemma in this way:
     'apply (@iff_trans P Q R)' replacing P, Q and R with statements you need.
     To find out what Q should be, 
     look at negation-related lemmas we've proved before.
 *)
  Lemma nat_eq_neg_spec (n1 n2: nat):
    nat_eq n1 n2 = false <-> n1 <> n2.
  Proof.
    apply (@iff_trans (nat_eq n1 n2 = false) (nat_eq n1 n2 <> true) (n1 <> n2)).
    (* eapply iff_trans. *)

    apply false_is_not_true.

    apply neg_equiv.
    apply nat_eq_spec.
  Qed.
  (* After you've proved the statement above, read about the 'eapply' tactic.
     The usage of 'eapply' allows to avoid specifying 
     all the parameters of a lemma you've been applying.
     Replace the 'apply (@iff_trans P Q R)' with simply 'eapply iff_trans' 
     and analyze how the proof proceeds.
     You can use 'eapply' in the subsequent proofs as well. *)
  
End NatEqProofs. 

Section UpdProofs.
  Context {V: Type}. 

  (* Prove that the updated function applied to the changed key is the new value. *)
  (* To exploit the term definition, use 'unfold' tactic. *)
  Lemma update_latest (f: nat -> V) (n: nat) (v: V):
    (upd f n v) n = v.
  Proof.
    unfold upd.
    rewrite nat_eq_refl.
    reflexivity.
  Qed.

  (* Prove that update affect only one value *)
  (* Use the helper lemma for 'if'.  *)
  Lemma update_others (f: nat -> V) (n: nat) (v: V) (n': nat) (NEQ: n <> n'):
    (upd f n v) n' = f n'.
  Proof.
    unfold upd.
    eapply if_false_helper.

    eapply nat_eq_neg_spec.
    apply NEQ.
  Qed.
    
    

End UpdProofs. 

Section NatDictProofs.

  Context {V: Type}. 

  (* Prove that new dictionary actually contains nothing. *)
  Lemma new_dict_empty (n: nat):
    contains' (@new_dict' V) n = false.
  Proof.
    unfold contains'.
    simpl.
    reflexivity.
  Qed.

  (* Prove that the inserted value gets retrieved *)
  Lemma insert_latest (d: @nat_dict_fun V) (n: nat) (v: V):
    get' (insert' d n v) n = Some v.
  Proof.
    unfold get'.
    unfold insert'.
    unfold upd.

    rewrite nat_eq_refl.
    simpl.
    reflexivity.
  Qed.

  (* Prove that removed key is no more contained in the dict *)
  Lemma removed_not_contained (d: @nat_dict_fun V) (n: nat):
    contains' (remove' d n) n = false.
  Proof.
    unfold contains', remove', get', upd.

    rewrite nat_eq_refl.
    simpl.
    reflexivity.
  Qed.
    

  (* Prove that insert doesn't affect other values *)
  Lemma insert_others (d: @nat_dict_fun V) (n: nat) (v: V) (n': nat) (NEQ: n <> n'):
    get' (insert' d n v) n' = get' d n'. 
  Proof.
    unfold get'.
    unfold insert'.
    unfold upd.

    eapply if_false_helper.
    eapply nat_eq_neg_spec.
    apply NEQ.
  Qed.
    

  (* Prove that updating a dictionary with a value it already has yields the same dictionary *)
  (* You may want to prove an helper lemma beforehand. *)
  (* Also, remember that 'destruct' can be used not only on variables, 
     but also on an arbitrary term.
     It can be used to separate cases when insert does matter and doesn't. *)
  Lemma insert_same (d: @nat_dict_fun V) (n: nat) (v: V)
        (HAD_V: get' d n = Some v):
    forall n', get' (insert' d n v) n' = get' d n'. 
  Proof.
    intros.
    
    unfold insert'.
    unfold upd.
    unfold get'.

    destruct (bool_true_or_false (nat_eq n n')) as [n_eq_n' | n_neq_n'].

    { rewrite n_eq_n'. eapply nat_eq_implies_eq in n_eq_n'.
      rewrite n_eq_n' in HAD_V. unfold get' in HAD_V. rewrite HAD_V.
      reflexivity. }
    rewrite n_neq_n'. reflexivity.
  Qed.
      
  (* Prove that inserting a value twice is the same as inserting it once *)
  Lemma insert_twice (d: @nat_dict_fun V) (n: nat) (v: V):
    forall n', get' (insert' (insert' d n v) n v) n' = get' (insert' d n v) n'. 
  Proof.
    unfold insert' in *.
    unfold upd.
    unfold get'.

    intros.

    destruct (nat_eq n n').

    { reflexivity. }
    reflexivity.
  Qed.

End NatDictProofs. 
