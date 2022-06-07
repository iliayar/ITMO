Require Import List.
Import ListNotations.
Require Import Lia.

From hahn Require Import HahnBase.

Require Import BinInt ZArith_dec Zorder ZArith.
Require Export Id.
Require Export State.
Require Export Expr Stmt.

Definition assertion := state Z -> Prop.

Definition get_state (c : conf) : state Z :=
  match c with
  | (st, _, _) => st
  end.

Definition hoare_triple
           (P : assertion) (s : stmt) (Q : assertion) : Prop :=
  forall c c' (EXEC : c == s ==> c') (PP : P (get_state c)),
    Q (get_state c').

Notation "{{ P }} c {{ Q }}" :=
  (hoare_triple P c Q) (at level 90, c at next level).

Definition assn_sub x e P : assertion :=
  fun (st : state Z) =>
  exists v,
    << SVAL : [| e |] st => v >> /\
    << PP : P (st [ x <- v ]) >>.

Notation "P 'h[' x '<-' e ']'" := (assn_sub x e P)
  (at level 10, x at next level).

Lemma hoare_skip Q :
  {{ Q }} SKIP {{ Q }}.
Proof.
  unfold hoare_triple; intros.
  inv EXEC.
Qed.

Lemma hoare_assign Q x e:
  {{ Q h[x <- e] }} x ::= e {{ Q }}.
Proof.
  unfold hoare_triple; unfold assn_sub; unfold get_state. intros.
  inv EXEC.
  inv PP. inv H.
  eapply eval_deterministic in VAL; eauto.
  subst; eauto.
Qed.

Definition assn_sub_example_P x st : Prop :=
  exists v,
    << XVAL : st / x => v >> /\
    << XLT  : Z.lt v (Z.of_nat 5) >>.

Example assn_sub_example x :
  {{ (assn_sub_example_P x) h[x <- (Var x) [+] (Nat 1)]}}
  x ::= ((Var x) [+] (Nat 1))
  {{ assn_sub_example_P x }}.
Proof.
  eapply hoare_assign.
Qed.

Lemma hoare_consequence_pre (P P' Q : assertion) s
      (HC : {{P'}} s {{Q}})
      (CONS : forall st (PP : P st), P' st) :
  {{P}} s {{Q}}.
Proof.
  unfold hoare_triple in *; intros.
  eapply HC in CONS; eauto.
Qed.

Lemma hoare_consequence_post (P Q Q' : assertion) s
      (HC : {{P}} s {{Q'}}) (CONS : forall st (QQ : Q' st), Q st) :
  {{P}} s {{Q}}.
Proof.
  unfold hoare_triple in *; intros.
  eapply CONS in HC; eauto.
Qed.

Lemma hoare_consequence (P P' Q Q' : assertion) s
      (HC : {{P'}} s {{Q'}})
      (PCONS : forall st (PP : P  st), P' st)
      (QCONS : forall st (QQ : Q' st), Q  st) :
  {{P}} s {{Q}}.
Proof.
  eapply hoare_consequence_pre; eauto.
  eapply hoare_consequence_post; eauto.
Qed.

Lemma hoare_seq (P Q R : assertion) s s'
      (PQ : {{P}} s  {{Q}})
      (QR : {{Q}} s' {{R}}) :
  {{P}} s;;s' {{R}}.
Proof.
  unfold hoare_triple; intros.
  inv EXEC; eauto.
Qed.

Lemma hoare_if (P Q : assertion) e s s'
      (TH : {{fun st => P st /\ [| e |] st => 1 }} s  {{Q}})
      (EL : {{fun st => P st /\ [| e |] st => 0 }} s' {{Q}}) :
  {{P}} COND e THEN s ELSE s' END {{Q}}.
Proof.
  unfold hoare_triple; intros.
  inv EXEC; eauto.
Qed.

Lemma hoare_while (P : assertion) e s
      (TH : {{fun st => P st /\ [| e |] st => 1 }} s {{P}}) :
  {{P}} WHILE e DO s END {{fun st => P st /\ [| e |] st => 0 }}.
Proof.
  unfold hoare_triple; intros.
  remember (WHILE e DO s END) as W.
  einduction EXEC; try inv HeqW.
  ins. eapply IHb2; eauto.
Qed.

    (**)
(* Coq is inconsistent with this axiom :) *)
Axiom state_extensionality :
  forall st st'
         (EXT : forall x, equivalent_states st st' x),
    st = st'.

Lemma state_shadow_eq (s : state Z) x a b v  : s [x <- a] [x <- v] = s [x <- b] [x <- v].
Proof.
  eapply state_extensionality; intros.
  econstructor; intros;
    eapply update_shadow;
    apply update_shadow in H;
    eauto.
Qed.

Lemma hoare_assign_fwd x m e P :
  {{ fun st =>
       << PST   : P st >> /\
       << XVAL : st / x => m >> }}
    x ::= e
  {{ fun st =>
       exists v,
         << PST'  : P h[x <- (Nat m)] st >> /\
         << EVAL : [| e |] (st [x <- m]) => v  >> /\
         << VST  : st / x => v >> }}.
Proof.
  red. ins. desf.
  inv EXEC. ins.
  exists z. splits.
  3: { econstructor. }
  2: { generalize dependent z.
       induction e; ins.
       { inv VAL. econstructor. }
       { inv VAL.
         destruct (id_eq_dec i0 x) as [ | NEQ ]; subst.
         { econstructor.
           assert (z = m); subst.
           { eapply state_deterministic; eauto. }
           econstructor. }
         econstructor.
         repeat (apply update_neq; auto). }

       inv VAL; econstructor;
         try (erewrite state_shadow_eq);
         try (eapply IHe1; eauto; econstructor; eauto);
         try (eapply IHe2; eauto; econstructor; eauto);
         eauto. }
  red. exists m.
  splits.
  { econstructor. }
  enough (((s) [x <- z]) [x <- m] = s) as AA.
  { rewrite AA; auto. }
  apply state_extensionality.
  ins. red. ins.
  etransitivity.
  { apply update_shadow. }
  destruct (id_eq_dec x0 x) as [ | NEQ ]; subst.
  { split; intros HH.
    { inv HH. }
    assert (z0 = m); subst.
    { eapply state_deterministic; eauto. }
    constructor. }
  split; intros HH.
  { inv HH. }
  constructor; auto.
Qed.

Opaque hoare_triple.

Module MultEx.
  Definition m := 0.
  Definition n := 1.
  Definition p := 2.
  Definition c := 3.
  Definition M := Var m.
  Definition N := Var n.
  Definition P := Var p.
  Definition C := Var c.

  Definition body :=
    (p ::= (P [+] M)) ;;
    (c ::= (C [+] (Nat 1))).

  Definition loop :=
    WHILE (C [<] N) DO
          body
    END.
  
  Lemma multSpec mv nv :
    {{ fun st =>
         << PINIT : st / p => 0%Z >> /\
         << CINIT : st / c => 0%Z >> /\
         << MINIT : st / m => mv >> /\
         << NINIT : st / n => nv >> /\
         << NPOS  : (nv >= 0)%Z >>
    }} loop {{
       fun st' =>
         << PVAL : st' / p => (mv * nv)%Z >>
    }}.
  Proof.
    Ltac exploit_st_det :=
      match goal with
      | S1 : (?st) / ?n => (?v1), S2 : (?st) / ?x => ?v2 |- _ =>
          assert (v1 = v2) as -> by (eapply state_deterministic; eauto)
      end.
    Ltac econs_unfold_solve := (repeat econstructor; eauto); unfold c, n, m, p; lia.

    unfold loop.
    eapply hoare_consequence.
    { unfold body.
      apply hoare_while with (
          P := fun st => exists cv,
                   st / c => cv /\
                   st / p => (cv * mv)%Z /\
                   (cv <= nv)%Z /\
                   st / n => nv /\
                   st / m => mv
        ).

      eapply hoare_seq.
      2: { apply hoare_assign. }

      eapply hoare_consequence.
      { eapply hoare_assign. }
      { ins. desc.
        Unshelve.
        2: exact (fun st => exists cv,
                   st / p => (cv * mv + mv)%Z /\
                   st / c => cv /\
                   st / n => nv /\
                   st / m => mv /\
                   (cv < nv)%Z
                                 ).
        red. exists (cv * mv + mv)%Z. splits.
        { econs_unfold_solve. }
        eexists.
        splits; try econs_unfold_solve.
        inv PP0. inv VALA. inv VALB.
        repeat exploit_st_det. lia. }
      ins. desc. red.
      exists (cv + 1)%Z. splits.
      { econs_unfold_solve. }
      eexists. splits; try econs_unfold_solve.
      { econstructor.
        { econs_unfold_solve. }
        replace ((cv + 1) * mv)%Z with (cv * mv + mv)%Z by lia. auto. } }
    { ins. desc.
      exists 0%Z. splits; auto. lia. }
    ins. desc. red.
    assert (cv = nv) as ->.
    2: { replace ((mv * nv)%Z) with ((nv * mv)%Z) by lia. auto. }
    inv QQ0. inv VALA. inv VALB.
    repeat exploit_st_det. lia.
  Qed. 

End MultEx.

Module FactorialEx.
  Definition x := 0.
  Definition y := 1.
  Definition X := Var x.
  Definition Y := Var y.

  Definition body :=
    (y ::= (X [*] Y)) ;;
    (x ::= (X [-] (Nat 1))).

  Definition loop :=
    WHILE (X [>] (Nat 0)) DO
          body
    END.

  Lemma factorialSpec n :
    {{ fun st =>
         << YINIT : st / y => (Z.of_nat 1) >> /\
         << XINIT : st / x => (Z.of_nat n) >>
    }} loop {{
       fun st' =>
         << YVAL : st' / y => (Z.of_nat (fact n)) >>
    }}.
  Proof.
    Ltac exploit_st_det :=
      match goal with
      | S1 : (?st) / ?n => (?v1), S2 : (?st) / ?x => ?v2 |- _ =>
          assert (v1 = v2) as -> by (eapply state_deterministic; eauto)
      end.
    Ltac econs_unfold_solve := (repeat econstructor; eauto); unfold x, y; lia.

    unfold loop.
    eapply hoare_consequence.
    { unfold body.
      apply hoare_while with (P := fun st => exists cx cy,
                                       st / y => (Z.of_nat cy) /\
                                       st / x => (Z.of_nat cx)  /\
                                       fact (n) = cy * fact (cx)
                             ).
      eapply hoare_seq.
      2: { apply hoare_assign. }

      eapply hoare_consequence.
      { eapply hoare_assign. }
      { ins. desc.
        Unshelve.
        2: { exact (fun st => exists cx cy,
                        st / y => (Z.of_nat cy) /\
                        st / x => (Z.of_nat cx) /\
                        cx >= 1 /\
                        fact (n) = cy * fact (cx - 1)
                   ). }
        red. exists (Z.mul (Z.of_nat cx) (Z.of_nat cy)).
        splits.
        { econs_unfold_solve. }
        exists cx, (cx * cy).
        splits; try econs_unfold_solve.
        { rewrite Nat2Z.inj_mul. econs_unfold_solve. }

        { inv PP0. inv VALA. inv VALB.
          exploit_st_det. lia. }

        { replace (cx * cy * fact (cx - 1)) with (cy * (fact (cx - 1) * cx)).
          2: { lia. }
          replace (fact (cx - 1) * cx) with (fact (cx)).
          { auto. }
          remember (cx - 1) as A.
          replace cx with (S A).
          { unfold fact. fold fact. lia. }
          inv PP0. inv VALA. inv VALB.
          exploit_st_det. lia. } }
      ins. desc. red.
      exists ((Z.of_nat cx) - 1)%Z. splits.
      { econs_unfold_solve. }
      exists (cx - 1), cy. splits; try econs_unfold_solve.
      { rewrite Nat2Z.inj_sub.
        { econs_unfold_solve. }
        lia. } }

    { ins. desc. exists n, 1.
      splits; eauto. lia. }
    ins. desc. red.
    inv QQ0. inv VALB. inv VALA.
    exploit_st_det.
    assert (cx = 0).
    { lia. }
    subst.
    unfold fact in QQ2. fold fact in QQ2.
    rewrite QQ2. replace (cy * 1) with cy; eauto.
    lia.
  Qed. 

End FactorialEx.

Module FastPowEx.
  Definition x := 0.
  Definition y := 1.
  Definition z := 2.
  Definition X := Var x.
  Definition Y := Var y.
  Definition Z := Var z.

  Definition body :=
    WHILE ((Y [%] (Nat 2)) [==] (Nat 0)) DO
          (x ::= (X [*] X)) ;;
          (y ::= (Y [/] (Nat 2)))
    END ;;
    (z ::= (Z [*] X)) ;;
    (y ::= (Y [-] (Nat 1))).

  Definition loop :=
    WHILE (Y [/=] (Nat 0)) DO
          body
    END.
  
  Lemma powerSpec m n :
    {{ fun st =>
         << XINIT : st / x => m >> /\
         << YINIT : st / y => n >> /\
         << ZINIT : st / z => 1%Z >>
    }} loop {{
       fun st' =>
         << ZVAL : st' / z => (m^n)%Z >>
    }}.
  Proof.
    Ltac exploit_st_det :=
      match goal with
      | S1 : (?st) / ?n => (?v1), S2 : (?st) / ?x => ?v2 |- _ =>
          assert (v1 = v2) as -> by (eapply state_deterministic; eauto)
      end.
    Ltac econs_unfold_solve := (repeat econstructor; eauto); unfold x, y, z; lia.

    unfold loop.
    eapply hoare_consequence.
    { unfold body.
      eapply hoare_while with (P := fun st => exists cm cn ck,
                                    st / z => ck%Z /\
                                    st / y => cn%Z /\
                                    st / x => cm%Z /\
                                    (m^n)%Z = (cm^cn * ck)%Z
                              ).
      eapply hoare_seq.
      { eapply hoare_consequence.
        { eapply hoare_while with (P := fun st => exists cm cn ck,
                                    st / z => ck%Z /\
                                    st / y => cn%Z /\
                                    st / x => cm%Z /\
                                    (m ^ n)%Z = (cm ^ (cn - 1) * (ck * (cm)))%Z
                              ).
          eapply hoare_seq.
          2: { eapply hoare_assign. }
          eapply hoare_consequence.
          { eapply hoare_assign. }

          { ins. desc.
            Unshelve.
            3: { exact (fun st => exists cm cn ck,
                            st / z => ck%Z /\
                            st / y => cn%Z /\
                            st / x => cm%Z /\
                            (m ^ n)%Z = (cm ^ ((Z.div cn 2) - 1) * (ck * (cm)))%Z
                       ). }
            2: { exact (fun st => exists cm cn ck,
                            st / z => ck%Z /\
                            st / y => cn%Z /\
                            st / x => cm%Z /\
                            (m ^ n)%Z = (cm ^ (cn - 1) * (ck * (cm)))%Z
                       ). }
            red. exists (cm * cm)%Z.
            splits; try econs_unfold_solve.
            exists (cm * cm)%Z, cn, ck.
            splits; try econs_unfold_solve.
            rewrite PP3.
            assert (cn <> 1)%Z.
            { inv PP0. inv VALA. inv VALB.
              inv VALA0. inv VALB0.
              exploit_st_det.
              inv OP.
              destruct (Z.eq_dec za0 1).
              { subst. inv H0. }
              auto. }
            destruct (Z.eq_dec cm 0).
            { subst. lia. }
            destruct (Z.eq_dec ck 0).
            { subst. lia. }
            destruct (Z_lt_ge_dec cn 0).
            { replace (cm ^ (cn - 1))%Z with (0)%Z.
              2: { symmetry. eapply Z.pow_neg_r. lia. }
              replace ((cm * cm) ^ ((Z.div cn 2) - 1))%Z with (0)%Z.
              2: { symmetry. eapply Z.pow_neg_r.
                   assert (Z.div cn 2 < 1)%Z.
                   2: { lia. }
                   remember (Z.div cn 2) as TMP.
                   replace cn with (2 * TMP)%Z in *.
                   { lia. }
                   { subst. inv PP0. inv VALA. inv VALB.
                     inv VALA0. inv VALB0.
                     eapply Z_div_exact_2 in OP; try lia.
                     exploit_st_det. auto. } }
              lia. }
            destruct (Z.eq_dec cn 0).
            { subst. simpl. auto. }
            assert (cn > 0)%Z.
            { lia. }
            assert (cn > 1)%Z.
            { lia. }
            assert (cn >= 2)%Z.
            { lia. }
            replace ((cm * cm) ^ ((Z.div cn 2) - 1))%Z with ((cm ^ 2) ^ ((Z.div cn 2) - 1))%Z.
            2: { rewrite Z.pow_2_r. lia. }
            replace ((cm ^ 2) ^ ((Z.div cn 2) - 1))%Z with (cm ^ (2 * ((Z.div cn 2) - 1)))%Z.
            2: { eapply Z.pow_mul_r; try lia.
                 inv PP0. inv VALA. inv VALB.
                 inv VALA0. inv VALB0. exploit_st_det.
                 enough ((Z.div za0 2)%Z >= 1%Z)%Z.
                 { lia. }
                 { remember (Z.div za0 2)%Z as TMP.
                   replace (za0) with (2 * TMP)%Z in *.
                   { lia. }
                   subst. symmetry.
                   eapply Z_div_exact_2; try lia.
                   auto. } }
            replace (2 * ((Z.div cn 2) - 1))%Z with (cn - 2)%Z.
            2: { replace (2 * ((Z.div cn 2) - 1))%Z with (2 * (Z.div cn 2) - 2)%Z.
                 2: { lia. }
                 replace (2 * (Z.div cn 2))%Z with cn.
                 2: { inv PP0. inv VALA. inv VALB.
                      inv OP. inv VALA0. inv VALB0.
                      exploit_st_det.
                      eapply Z_div_exact_2; try lia. }
                 lia. }
            replace (cm ^ (cn - 2) * (ck * (cm * cm)))%Z with ((cm ^ (cn - 2) * cm) * (ck * cm))%Z.
            2: { lia. }
            eapply Z.mul_cancel_r.
            { lia. }
            replace (cn - 1)%Z with ((cn - 2) + 1)%Z.
            2: { lia. }
            replace (cm ^ (cn - 2) * cm)%Z with (cm ^ (cn - 2) * cm ^ 1)%Z.
            2: { lia. }
            eapply Z.pow_add_r; try lia. }
          ins. desc. red.
          exists (Z.div cn 2).
          splits; try econs_unfold_solve.
          { econstructor.
            { econstructor. auto. }
            { econstructor. }
            { replace (Z.zero) with 0%Z; eauto.
              lia. } } }
        { ins. desc.
          exists cm, cn, ck. split; eauto.
          splits; try econs_unfold_solve.
          rewrite PP3.
          destruct (Z.eq_dec ck 0).
          { subst. lia. }
          replace (cm ^ (cn - 1) * (ck * cm))%Z with ((cm * cm ^ (cn - 1)) * ck)%Z.
          2: { lia. }
          eapply Z.mul_cancel_r with (p := ck).
          { lia. }
          replace (cm * cm ^ (cn - 1))%Z with (cm ^ Z.succ (cn - 1))%Z.
          { replace (Z.succ (cn - 1)) with (cn); auto.
            lia. }
          destruct (Z_ge_lt_dec (cn - 1) 0).
          { erewrite Z.pow_succ_r; auto. lia. }
          replace (cm ^ (cn - 1))%Z with 0%Z.
          2: { symmetry. eapply Z.pow_neg_r. lia. }
          replace (cm ^ Z.succ (cn - 1))%Z with 0%Z.
          { lia. }
          symmetry. eapply Z.pow_neg_r.
          inv PP0. inv VALA. inv VALB.
          exploit_st_det.
          destruct (Z.eq_dec za 0).
          {  contradiction. }
          lia. }
        ins. desc. exists cm, cn, ck.
        splits; try econs_unfold_solve. }

      eapply hoare_seq.
      2: { eapply hoare_assign. }

      eapply hoare_consequence.
      { eapply hoare_assign. }
      { ins. desc.
        Unshelve.
        2: { exact (fun st => exists cm cn ck,
                        st / z => ck%Z /\
                        st / y => cn%Z /\
                        st / x => cm%Z /\
                        (m^n)%Z = (cm^(cn - 1) * ck)%Z
                   ). }
        red. exists (ck * cm)%Z.
        splits; try econs_unfold_solve. }
      ins. desc. red.
      exists (cn - 1)%Z.
      splits; try econs_unfold_solve. }

    { ins. desc.
      exists m, n, 1%Z.
      splits; try econs_unfold_solve. }

    ins. desc. red.
    inv QQ0. inv VALB. inv VALA.
    exploit_st_det. rewrite QQ3.
    replace ((cm ^ za * ck)%Z) with (ck).
    { auto. }
    rewrite OP. lia.
  Qed. 
          
    
End FastPowEx.
  
