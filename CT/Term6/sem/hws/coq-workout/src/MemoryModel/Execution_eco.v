Require Import Classical Peano_dec.
From hahn Require Import Hahn.
Require Import AuxRel.

Require Import Events.
Require Import Execution.

Set Implicit Arguments.

Section ECO.
Variable G : execution.

Notation "'E'" := (acts_set G).
Notation "'sb'" := (sb G).
Notation "'rf'" := (rf G).
Notation "'co'" := (co G).
Notation "'rmw'" := (rmw G).

Notation "'fr'" := (fr G).
Notation "'coe'" := (coe G).
Notation "'coi'" := (coi G).
Notation "'rfi'" := (rfi G).
Notation "'rfe'" := (rfe G).
Notation "'fre'" := (fre G).
Notation "'fri'" := (fri G).

Notation "'lab'" := (lab G).
Notation "'loc'" := (loc lab).
Notation "'val'" := (val lab).
Notation "'mod'" := (mod lab).
Notation "'same_loc'" := (same_loc lab).

Notation "'R'" := (fun a => is_true (is_r lab a)).
Notation "'W'" := (fun a => is_true (is_w lab a)).
Notation "'F'" := (fun a => is_true (is_f lab a)).
Notation "'RW'" := (R ∪₁ W).
Notation "'FR'" := (F ∪₁ R).
Notation "'FW'" := (F ∪₁ W).

Notation "'Pln'" := (is_only_pln lab).
Notation "'Rlx'" := (is_rlx lab).
Notation "'Rel'" := (is_rel lab).
Notation "'Acq'" := (is_acq lab).
Notation "'Acqrel'" := (is_acqrel lab).
Notation "'Sc'" := (is_sc lab).

Implicit Type WF : Wf G.
Implicit Type COMP : complete G.
Implicit Type ATOM : rmw_atomicity G.

(******************************************************************************)
(** ** extended coherence order  *)
(******************************************************************************)

Definition eco := (rf ∪ co ∪ fr)⁺.

(******************************************************************************)
(** ** Basic Properties  *)
(******************************************************************************)

Lemma co_in_eco: co ⊆ eco.
Proof. Admitted.

Lemma rf_in_eco: rf ⊆ eco.
Proof. Admitted.

Lemma fr_in_eco: fr ⊆ eco.
Proof. Admitted.

Lemma loceq_eco WF : funeq loc eco.
Proof. Admitted.

Lemma wf_ecoE WF : eco ≡ ⦗E⦘ ⨾ eco ⨾ ⦗E⦘.
Proof. Admitted.

Lemma wf_ecoD WF : eco ≡ ⦗RW⦘ ⨾ eco ⨾ ⦗RW⦘.
Proof. Admitted.

Lemma eco_trans WF: transitive eco.
Proof. Admitted.

Lemma eco_alt WF: eco ≡ (fun _ _ => False).
Proof. Admitted.

Lemma eco_irr WF: irreflexive eco.
Proof. Admitted.

End ECO.