Require Import List.
Import ListNotations.
Require Import Lia.

Require Import BinInt ZArith_dec Zorder ZArith.
Require Export Id State Expr Stmt.

From hahn Require Import HahnBase.

Module Euclid.
  Definition m := 0.
  Definition n := 1.
  Definition M := Var m.
  Definition N := Var n.

  Definition body :=
          COND (M [<] N)
          THEN n ::= (N [-] M)
          ELSE m ::= (M [-] N)
          END.

  Definition euclid :=
    WHILE (M [/=] N) DO
          body
    END.
  
  Lemma euclid_terminates st mz nz
        (VARM : st / m => (Z.of_nat mz))
        (VARN : st / n => (Z.of_nat nz))
        (M1   : mz >= 1)
        (N1   : nz >= 1) :
    exists st', (st, [], []) == euclid ==> (st', [], []).
  Proof. Admitted.
End Euclid.

