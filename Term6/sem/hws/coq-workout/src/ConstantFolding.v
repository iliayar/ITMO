Require Import BinInt ZArith_dec Zorder.
Require Export Id.
Require Export State.
Require Export Expr.

From hahn Require Import HahnBase.

Definition eval_op (op : bop) (z1 z2 : Z) : option Z :=
  match op with
  | Add => Some (z1 + z2)%Z
  | Sub => Some (z1 - z2)%Z
  | Mul => Some (z1 * z2)%Z
  | Div =>
    match z2 with
    | 0%Z => None
    | _   => Some (Z.div z1 z2)
    end
  | Mod =>
    match z2 with
    | 0%Z => None
    | _   => Some (Z.modulo z1 z2)
    end
  | Le =>
    match Ztrichotomy_inf z1 z2 with
    | inleft  _ => Some 1%Z
    | _ => Some 0%Z
    end
  | Lt =>
    match Ztrichotomy_inf z1 z2 with
    | inleft (left _) => Some 1%Z
    | _ => Some 0%Z
    end
  | Ge =>
    match Ztrichotomy_inf z1 z2 with
    | inleft (right _)
    | inright _ => Some 1%Z
    | _ => Some 0%Z
    end
  | Gt =>
    match Ztrichotomy_inf z1 z2 with
    | inright _ => Some 1%Z
    | _ => Some 0%Z
    end
  | Eq =>
    match Ztrichotomy_inf z1 z2 with
    | inleft (right _) => Some 1%Z
    | _ => Some 0%Z
    end
  | Ne =>
    match Ztrichotomy_inf z1 z2 with
    | inleft (right _) => Some 0%Z
    | _ => Some 1%Z
    end
  | And =>
    match z1, z2 with
    | 1%Z, 1%Z => Some 1%Z
    | 0%Z, 0%Z 
    | 0%Z, 1%Z
    | 1%Z, 0%Z => Some 0%Z
    | _, _ => None
    end
  | Or =>
    match z1, z2 with
    | 0%Z, 0%Z => Some 0%Z
    | 0%Z, 1%Z
    | 1%Z, 0%Z
    | 1%Z, 1%Z => Some 1%Z
    | _, _ => None
    end
  end.

Fixpoint cfold (e : expr) : expr :=
  match e with
  | Bop op e1 e2 =>
    let (c1, c2) := (cfold e1, cfold e2) in
    match c1, c2 with
    | Nat z1, Nat z2 =>
      match eval_op op z1 z2 with
      | Some v1 => Nat v1
      | _       => Bop op c1 c2
      end
    | _, _ => Bop op c1 c2
    end
  | _ => e
  end.

Lemma cfold_correct (e : expr) : cfold e ~e~ e.
Proof. admit. Admitted.
