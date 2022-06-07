(* Lambda calculus workout *)

Require Import List.
Import ListNotations.
Require Import Arith.
Require Import Id.

From hahn Require Import HahnBase.

Require Import Coq.Relations.Relation_Operators.

Section Lambda.

(* Lambda term in regular named representation *)
Inductive term : Type := 
  Var  : id -> term
| Abs  : id -> term -> term 
| App  : term -> term -> term.

(* Notations and some examples *)
Notation "\ x , .. , z --> t" := (Abs x .. (Abs z t) .. ) (at level 38, no associativity).
Notation "m @ n"              := (App m n) (at level 39, left associativity).

Definition f := 0.
Definition g := 1.
Definition h := 2.

Definition x := 3.
Definition y := 4.

Definition m := 5.
Definition n := 6.

Definition v i := Var i.
           
Definition i     := \ x --> v x.
Definition apply := \ f, x --> (v f @ v x).
Definition z     := \ f, x --> v x.
Definition s     := \ n, f, x --> (v f @ (v n @ v f @ v x)).
Definition add   := \ n, m, f, x --> (v m @ v f @ (v n @ v f @ v x)).
Definition mul   := \ n, m, f, x --> (v m @ (v n @ v f) @ v x).

(* Free variables*) 
Inductive fv : id -> term -> Prop :=
  fv_Var : forall x,  fv x (v x)
| fv_Abs : forall x y t,  fv y t -> x <> y -> fv y (\ x --> t)
| fv_App : forall x a b,  (fv x a) \/ (fv x b) -> fv x (a @ b).

Lemma fv_var: forall x y, fv x (v y) -> x = y.
Proof. admit. Admitted.

(* Capture-avoiding substitution *)
Reserved Notation "m [[ x <~ y ]] n" (at level 40, left associativity).

Inductive cas : term -> id -> id -> term -> Prop :=
  cas_Var : forall x y, (v x) [[x <~ y]] (v y)

| cas_Var_neq : forall x y z (NEQ : x <> z), (v z) [[x <~ y]] (v z)

| cas_App : forall m n m' n' x y 
                   (CASM : m [[ x <~ y ]] m')
                   (CASN : n [[ x <~ y ]] n'),
            (m @ n) [[ x<~ y ]] (m' @ n')

| cas_Lam : forall m x y, (\x --> m) [[ x <~ y ]] (\x --> m)

| cas_Lam_neq : forall m m' x y z
                       (NEQX : z <> x) (NEQY : z <> y)
                       (CASM : m [[ x<~ y ]] m'),
                (\ z --> m) [[ x <~ y ]] (\z --> m')
                
| cas_Lam_ren : forall m m' m'' x y z
                       (NFV : ~ fv z m)
                       (CASM  : m [[ y <~ z ]] m')
                       (CASM' : m' [[ x <~ y ]] m''),
                (\y --> m) [[ x <~ y ]] (\z --> m'')
where "m [[ x <~ y ]] n" := (cas m x y n).

#[local]
Hint Constructors cas : ll.

(* Some lemmas about CAS *)
Lemma cas_reflexive s x : s [[ x <~ x ]] s.
Proof. admit. Admitted.

Lemma cas_preserves x y z s s' (NEQX : z <> x) (NEQY : z <> y)
      (CAS : s [[x <~ y ]] s') (FV : fv z s'):
  fv z s.
Proof. admit. Admitted.

Lemma cas_renames_free s s' x y (NEQ : x <> y)
      (CAS : s [[ x <~ y ]] s') :
  ~ fv x s'.
Proof. admit. Admitted.

(* Renaming of variables *)
Reserved Notation "m [[ x <~ y ]]" (at level 37, left associativity).

Fixpoint rename t x y :=
  match t with
  | Var z     => if id_eq_dec z x then v y else t
  | \ z --> m => if id_eq_dec z x then t else \ z --> m [[x <~ y]]
  | m @ n     => m [[x <~ y]] @ n [[x <~ y]]
  end
where "m [[ x <~ y ]]" := (rename m x y).

(* Safety condition for renaming *)
Inductive safe : term -> id -> id -> Prop :=
  safe_Var   : forall x y z (NEQ : x <> z),
    safe (Var x) y z

| safe_App   : forall m n x y (SAFEM : safe m x y) (SAFEN : safe n x y),
    safe (m @ n) x y

| safe_Lam_1 : forall m z y (NFV : ~ fv y m), safe (\ z --> m) z y
| safe_Lam_2 : forall m x y z (NEQY : y <> z) (NEQX : x <> z)
                      (SAFEM : safe m x y),
    safe (\ z --> m) x y

| safe_Lam_3 : forall m x z (NEQX : x <> z) (NFV : ~ fv x m),
    safe (\ z --> m) x z.

(* Some lemmas about safety and renaming *)
Lemma safe_nfv m x y (SAFEM : safe m x y) : ~ fv y m.
Proof. admit. Admitted.

Lemma safe_fv_neq m x y z (SAFEM : safe m x y) (FV : fv z m) : y <> z.
Proof. admit. Admitted.

Lemma rename_not_fv m x z (NEQ : x <> z) : ~ fv x (m [[x <~ z]]).
Proof. admit. Admitted.

Lemma safe_reverse m x y (SAFEM : safe m x y) :
  safe (m [[x <~ y]]) y x.
Proof. admit. Admitted.

#[local]
Hint Resolve safe_reverse : ll.

Lemma rename_eq_eq m x : m [[ x <~ x]] = m.
Proof. admit. Admitted.
  
Lemma rename_not_free_is_id m x y (FH : ~ fv x m) : m [[ x <~ y ]] = m.
Proof. admit. Admitted.

Lemma rename_reverse m x y (SH : safe m x y) : (m [[x <~ y]]) [[y <~ x]] = m.
Proof. admit. Admitted.

Lemma rename_preserves m x z y (FH : fv x m) (NEH : z <> x) : fv x (m [[ z <~ y ]]).
Proof. admit. Admitted.

Lemma rename_free_reverse x y z m (HXZ: x <> z) (HYZ: x <> y) (HFV: fv x (m [[ z <~ y]])) : fv x m.
Proof. admit. Admitted.

Lemma rename_if_free m x y z (HFV : fv x (m [[ y <~ z ]])) (HXZ : x <> z) : y <> x.
Proof. admit. Admitted.

#[local]
Hint Resolve rename_reverse : ll.

(* Contexts *)
Inductive Context : Set :=
  CHole : Context
| CAbs  : id -> Context -> Context
| CAppL : Context -> term -> Context
| CAppR : term -> Context -> Context.

(* Substitution in a context *)
Fixpoint term_in_context (C : Context) (t : term) : term :=
  match C with
  | CHole     => t
  | CAbs x c  => Abs x (term_in_context c t)
  | CAppL c p => App (term_in_context c t) p
  | CAppR p c => App p (term_in_context c t)
  end.

(* Some lemmas about contexts *)
Lemma fv_in_term_in_context
      (C : Context) (m : term) (x : id) :
      fv x (term_in_context C m) -> fv x (term_in_context C (\ x --> v x)) \/ fv x m.
Proof. admit. Admitted.

Lemma fv_in_context
      (C : Context) (m : term) (x : id) :
      fv x (term_in_context C (\ x --> v x)) -> fv x (term_in_context C m).
Proof. admit. Admitted.

Lemma fv_in_another_term_in_context
      (C : Context) (m n : term) (x : id) (FVM : fv x m) (FVC : fv x (term_in_context C m)) :
      fv x n -> fv x (term_in_context C n).
Proof. admit. Admitted.

Lemma empty_context m n (H : term_in_context CHole m = n) : m = n.
Proof. admit. Admitted.

Lemma term_in_context_is_var m x C (H : term_in_context C m = v x) : C = CHole.
Proof. admit. Admitted.

(* Alpha conversion *)
Reserved Notation "m <~~> n" (at level 38, no associativity).

(* Alpha equivalence *)
Inductive alpha_equivalent : term -> term -> Prop :=
| ae_Refl    : forall m, m <~~> m
| ae_Rename  : forall m x y, safe m x y -> (\ x --> m) <~~> (\ y --> m [[ x <~ y ]])
| ae_Subterm : forall C a b, a <~~> b -> term_in_context C a <~~> term_in_context C b 
| ae_Trans   : forall m n p, m <~~> n -> n <~~> p -> m <~~> p
where "m <~~> n" := (alpha_equivalent m n).

#[local]
Hint Constructors alpha_equivalent : ll.

Lemma alpha_equivalent_symm (m n : term) (HA : m <~~> n) : n <~~> m.
Proof. Admitted.

End Lambda.
