(* This file contains definitions that will be moved to CompCertO later *)

Require Import Relations RelationClasses Relators.
Require Import List Maps.
Require Import Coqlib.
Require Import CallconvAlgebra_.
Require Import LanguageInterface_ Events Globalenvs Smallstep_ CategoricalComp FlatComp.
Require Import Memory Values.
Require Import Linking.

Global Instance fsim_transitive {li1 li2: language_interface}:
  Transitive (forward_simulation (@cc_id li1) (@cc_id li2)).
Proof.
  intros L1 L2 L3 HL1 HL2.
  eapply open_fsim_ccref. apply cc_compose_id_left.
  unfold flip. apply cc_compose_id_left.
  eapply compose_forward_simulations; eauto.
Qed.


Section HCOMP_FSIM.

  Context {li1 li2} (cc: callconv li1 li2)
          (L1a L1b: Smallstep_.semantics li1 li1)
          (L2a L2b: Smallstep_.semantics li2 li2).
  Hypothesis (HL1: forward_simulation cc cc L1a L2a)
             (HL2: forward_simulation cc cc L1b L2b).
  Let L1 := fun b => match b with | true => L1a | false => L1b end.
  Let L2 := fun b => match b with | true => L2a | false => L2b end.

  Variable (sk: AST.program unit unit).
  Hypothesis (Hsk1: linkorder (skel L1a) sk)
             (Hsk2: linkorder (skel L1b) sk).

  Lemma horizontal_compose_simulation':
    forward_simulation cc cc (SmallstepLinking_.semantics L1 sk)
                       (SmallstepLinking_.semantics L2 sk).
  Proof.
    destruct HL1 as [Ha]. destruct HL2 as [Hb].
    assert (HL: forall i, fsim_components cc cc (L1 i) (L2 i)) by (intros [|]; auto).
    constructor.
    eapply Forward_simulation with
        (SmallstepLinking_.order cc L1 L2 HL)
        (SmallstepLinking_.match_states cc L1 L2 HL).
    - reflexivity.
    - intros i. cbn. destruct Ha, Hb.
      rewrite fsim_footprint, fsim_footprint0. reflexivity.
    - intros se1 se2 w qset Hse Hse1.
      eapply SmallstepLinking_.semantics_simulation; eauto.
      intros [|]; cbn; eapply Genv.valid_for_linkorder; eauto.
    - clear - HL. intros [i x].
      induction (fsim_order_wf (HL i) x) as [x Hx IHx].
      constructor. intros z Hxz. inv Hxz; SmallstepLinking_.subst_dep. eauto.
  Qed.
End HCOMP_FSIM.

Section COMP_FSIM.

  Context {liA1 liA2 liB1 liB2 liC1 liC2}
          {cc1: callconv liA1 liA2}
          {cc2: callconv liB1 liB2}
          {cc3: callconv liC1 liC2}
          (L1a: Smallstep_.semantics liB1 liC1)
          (L2a: Smallstep_.semantics liB2 liC2)
          (L1b: Smallstep_.semantics liA1 liB1)
          (L2b: Smallstep_.semantics liA2 liB2).
  Hypothesis (HL1: forward_simulation cc2 cc3 L1a L2a)
             (HL2: forward_simulation cc1 cc2 L1b L2b).

  Variable (sk: AST.program unit unit).
  Hypothesis (Hsk1: linkorder (skel L1a) sk)
             (Hsk2: linkorder (skel L1b) sk).

  Lemma categorical_compose_simulation':
    forward_simulation cc1 cc3 (comp_semantics' L1a L1b sk)
                       (comp_semantics' L2a L2b sk).
  Proof.
    destruct HL1 as [Ha]. destruct HL2 as [Hb].
    constructor.
    eapply Forward_simulation
      with (CategoricalComp.order cc1 cc2 cc3 L1a L1b L2a L2b Ha Hb)
           (CategoricalComp.match_states cc1 cc2 cc3 L1a L1b L2a L2b Ha Hb).
    - cbn. destruct Ha, Hb. congruence.
    - cbn. intros i. destruct Ha, Hb.
      rewrite fsim_footprint, fsim_footprint0. reflexivity.
    - intros se1 se2 w qset Hse Hse1.
      eapply CategoricalComp.semantics_simulation; eauto.
      eapply Genv.valid_for_linkorder. apply Hsk1. auto.
      eapply Genv.valid_for_linkorder. apply Hsk2. auto.
    - clear - Ha Hb. intros [|].
      + induction (fsim_order_wf Ha f). constructor.
        intros. inv H1. apply H0. auto.
      + induction (fsim_order_wf Hb f0). constructor.
        intros. inv H1. apply H0. auto.
  Qed.

End COMP_FSIM.

Require Import SmallstepLinking_.

Section HCOMP_ASSOC.

  Context {li} (L1 L2 L3: Smallstep_.semantics li li).
  Variable (sk: AST.program unit unit).
  Let L12 := fun b => match b with | true => L1 | false => L2 end.
  Let L := fun b => match b with
                 | true => SmallstepLinking_.semantics L12 sk
                 | false => L3
                 end.
  Let L23 := fun b => match b with | true => L2 | false => L3 end.
  Let L' := fun b => match b with
                  | true => L1
                  | false => SmallstepLinking_.semantics L23 sk
                  end.

  Variant frame3: Type :=
  | fm1: state L1 -> frame3
  | fm2: state L2 -> frame3
  | fm3: state L3 -> frame3.

  Inductive flatten1: list (frame L) -> list frame3 -> Prop :=
  | flatten1_nil_nil: flatten1 nil nil
  | flatten1_fm1' s k2 k:
      flatten1 k2 k ->
      flatten1 (st L true (st L12 true s :: nil) :: k2) (fm1 s :: k)
  | flatten1_fm1 s k1 k2 k:
      k1 <> nil -> flatten1 (st L true k1 :: k2) k ->
      flatten1 (st L true (st L12 true s :: k1) :: k2) (fm1 s :: k)
  | flatten1_fm2' s k2 k:
      flatten1 k2 k ->
      flatten1 (st L true (st L12 false s :: nil) :: k2) (fm2 s :: k)
  | flatten1_fm2 s k1 k2 k:
      k1 <> nil -> flatten1 (st L true k1 :: k2) k ->
      flatten1 (st L true (st L12 false s :: k1) :: k2) (fm2 s :: k)
  | flatten1_fm3 s k1 k:
      flatten1 k1 k ->
      flatten1 (st L false s :: k1) (fm3 s :: k).

  Inductive flatten2: list (frame L') -> list frame3 -> Prop :=
  | flatten2_nil_nil: flatten2 nil nil
  | flatten2_fm1 s k1 k:
      flatten2 k1 k ->
      flatten2 (st L' true s :: k1) (fm1 s :: k)
  | flatten2_fm2' s k2 k:
      flatten2 k2 k ->
      flatten2 (st L' false (st L23 true s :: nil) :: k2) (fm2 s :: k)
  | flatten2_fm2 s k1 k2 k:
      k1 <> nil -> flatten2 (st L' false k1 :: k2) k ->
      flatten2 (st L' false (st L23 true s :: k1) :: k2) (fm2 s :: k)
  | flatten2_fm3' s k2 k:
      flatten2 k2 k ->
      flatten2 (st L' false (st L23 false s :: nil) :: k2) (fm3 s :: k)
  | flatten2_fm3 s k1 k2 k:
      k1 <> nil -> flatten2 (st L' false k1 :: k2) k ->
      flatten2 (st L' false (st L23 false s :: k1) :: k2) (fm3 s :: k).

  Hint Constructors flatten1 flatten2.

  Definition state_match (s1: list (frame L)) (s2: list (frame L')): Prop :=
    exists fm, flatten1 s1 fm /\ flatten2 s2 fm.

  Lemma horizontal_compose_associativity:
    SmallstepLinking_.semantics L sk ≤ SmallstepLinking_.semantics L' sk.
  Proof.
    constructor. econstructor. reflexivity.
    intros. apply or_assoc.
    intros se ? [ ] qset [ ] Hse.
    instantiate (1 := fun _ _ _ => _). cbn beta.
    apply forward_simulation_step
      with (match_states := state_match); cbn.
    - intros q ? s1 <- H. inv H. destruct i.
      (* initial state of L12 *)
      + cbn in *. inv H1. destruct i.
        (* initial state of L1 *)
        * cbn in *. eexists; split.
          apply initial_state_intro with (i := true).
          firstorder. eauto.
          eexists. split; eauto.
        (* initial state of L2 *)
        * cbn in *. eexists; split.
          apply initial_state_intro with (i := false).
          cbn. firstorder.
          apply initial_state_intro with (i := true).
          firstorder. eauto.
          eexists. split; eauto.
      (* initial state of L3 *)
      + cbn in *. eexists; split.
        apply initial_state_intro with (i := false).
        cbn. firstorder.
        apply initial_state_intro with (i := false).
        firstorder. eauto.
        eexists. split; eauto.
    - intros s1 s2 r Hs H. exists r; split; auto.
      inv H. destruct i.
      (* final state of L12 *)
      + cbn in *. inv H0. destruct i.
        (* final state of L1 *)
        * cbn in *. destruct Hs as [fs [Hs1 Hs2]].
          admit.
        (* final state of L2 *)
        * admit.
      (* final state of L3 *)
      + cbn in *. destruct Hs as [fs [Hs1 Hs2]].
        inv Hs1. subst_dep.
        inv H3. inv Hs2. inv H2.
        repeat constructor; auto.
        inv H4.
    - admit.
    - intros s1 t s1' Hstep s2 Hs.
      inv Hstep.
      (* internal step *)
      + destruct i.
        (* internal step of L12 *)
        * inv H.
          (* internal step of L1 or L2 *)
          {
            destruct i.
            (* internal step of L1 *)
            - destruct Hs as [fm [Hs1 Hs2]].
              inv Hs1.
              inv Hs.
              admit.
            (* internal step of L2 *)
            - admit.
          }
          (* cross component call between L1 and L2 *)
          -- admit.
          (* return *)
          -- admit.
        (* internal step of L3 *)
        * admit.
      (* cross component call between L12 and L3 *)
      + destruct i.
        (* call from L12 *)
        * cbn in *. inv H. destruct i.
          (* call from L1 *)
          -- admit.
          (* call from L2 *)
          -- admit.
        (* call from L3 *)
        * admit.
      (* return *)
      + admit.

  Admitted.

End HCOMP_ASSOC.
