Require Import Arith Arith.EqNat.
Require Import Lia.

Definition id := nat.

Lemma lt_eq_lt_id_dec (id1 id2 : id) :
  {id1 < id2} + {id1 = id2} + {id2 < id1}.
Proof. admit. Admitted.

Lemma gt_eq_gt_id_dec (id1 id2 : id):
  {id1 > id2} + {id1 = id2} + {id2 > id1}.
Proof. admit. Admitted.

Lemma le_gt_id_dec (id1 id2 : id): {id1 <= id2} + {id1 > id2}.
Proof. admit. Admitted.

Lemma id_eq_dec (id1 id2 : id): {id1 = id2} + {id1 <> id2}.
Proof. admit. Admitted.

Lemma eq_id {T} x (p q:T):
  (if id_eq_dec x x then p else q) = p.
Proof. admit. Admitted.

Lemma neq_id {T} x y (p q:T) (NEQ: x <> y):
  (if id_eq_dec x y then p else q) = q.
Proof. admit. Admitted.

Lemma lt_gt_id_false (id1 id2 : id)
      (GT : id1 > id2) (GT': id2 > id1):
  False.
Proof. admit. Admitted.

Lemma le_gt_id_false (id1 id2 : id)
      (LE : id2 <= id1) (GT : id2 > id1) :
  False.
Proof. admit. Admitted.

Lemma le_lt_eq_id_dec (id1 id2 : id) (LE : id1 <= id2):
  {id1 = id2} + {id2 > id1}.
Proof. admit. Admitted.

Lemma neq_lt_gt_id_dec (id1 id2 : id) (NEQ : id1 <> id2):
    {id1 > id2} + {id2 > id1}.
Proof. admit. Admitted.
    
Lemma eq_gt_id_false (id1 id2 : id)
      (EQ : id1 = id2) (GT : id1 > id2) :
  False.
Proof. admit. Admitted.

Lemma ne_symm (id1 id2 : id) (NEQ : id1 <> id2) : id2 <> id1.
Proof. admit. Admitted.
