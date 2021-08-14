Require Import Relations RelationClasses Relators.
Require Import List.
Require Import Coqlib.
Require Import CallconvAlgebra_.
Require Import LanguageInterface_ Events Globalenvs.
Require Import CategoricalComp.
Require Import SmallstepLinking_.
Require Import Smallstep_.
Require Import Linking.
Require Import CompCertO.

(* Definitions *)
Section Lifting.
  (* Lifting a language interface with abstract data of type K *)
  Variable K: Type.
  Definition lifted_li li: language_interface :=
    {|
    query := query li * K;
    reply := reply li * K;
    entry '(q, _) := entry q
    |}.

  (* Lifting an LTS with abstract data of type K. The lifted LTS simply
     passes the abstract state through without modifying it *)
  Context {liA liB state} (L: lts liA liB state).
  Let stateX := (state * K)%type.
  Let liBX := lifted_li liB.
  Let liAX := lifted_li liA.

  Program Definition lifted_lts: lts liAX liBX stateX :=
    {|
      genvtype := genvtype L;
      step p ge '(s, a) t '(s', a') := (step L p ge s t s' /\ a = a')%type;
      initial_state := (initial_state L) * eq;
      at_external := fun s (q: query liAX) => ((at_external L) * eq) s q;
      after_external s := (after_external L (fst s)) * eq;
      final_state := (final_state L) * eq;
      globalenv := globalenv L
    |}%rel.
  Next Obligation.
    destruct s, s'. split.
    eapply steps_monotone; now eauto.
    easy.
  Qed.

End Lifting.

Definition lifted_semantics {liA liB} (K: Type) (L: semantics liA liB) :=
  {|
    skel := skel L;
    activate se := lifted_lts K (L se);
    footprint := footprint L;
  |}.

(* Notations *)
Delimit Scope li_scope with li.
Bind Scope li_scope with language_interface.
(* Delimit Scope lts_scope with lts. *)
(* Bind Scope lts_scope with lts. *)

(* Note since we are overloading the @ operator, the right associativity and
   precedence level will be inherited *)
Notation "li @ K" := (lifted_li K li): li_scope.
(* Notation "L @ K" := (lifted_lts K L): lts_scope. *)

Delimit Scope lts_scope with lts.
Bind Scope lts_scope with semantics.
Notation "L @ K" := (lifted_semantics K L): lts_scope.

Notation " 'layer' K " := (Smallstep_.semantics li_null (li_c @ K)) (at level 1).

(* Properties *)

Section CAT_COMP_LIFT.
  Variable K: Type.
  Context {liA liB liC} (L1: semantics liB liC) (L2: semantics liA liB).
  Variable (sk: AST.program unit unit).

  Local Inductive state_match: (comp_state L1 L2 * K) -> comp_state (L1 @ K) (L2 @ K) -> Prop :=
  | state_match1 s1 k:
      state_match (st1 _ _ s1, k) (st1 (L1@K) (L2@K) (s1, k))
  | state_match2 s1 s2 k k':
      state_match (st2 _ _ s1 s2, k) (st2 (L1@K) (L2@K) (s1, k') (s2, k)).

  Lemma lift_categorical_comp1:
    (comp_semantics' L1 L2 sk) @ K ≤ comp_semantics' (L1 @ K) (L2 @ K) sk.
  Proof.
    constructor. econstructor. reflexivity. intros i. reflexivity.
    intros se _ [ ] ? [ ] Hse. instantiate (1 := fun _ _ _ => _). cbn beta.
    eapply forward_simulation_step with (match_states := state_match).
    - intros q _ s1 [ ] Hq. destruct s1 as [s1 ks].
      inv Hq. inv H. destruct q as [q k]. cbn in *. subst.
      eexists _. split; repeat constructor; auto.
    - intros [s1 k] s2 [r kr] Hs Hr.
      inv Hr. inv H. cbn in *. subst. inv Hs.
      eexists. split; eauto. constructor. constructor; cbn; auto.
    - intros [s1 k] s2 [q1 kq] Hs Hq.
      eexists tt, _. repeat apply conj; try constructor.
      inv Hq. inv H. cbn in *. subst. inv Hs. constructor; auto.
      constructor; auto.
      intros [r1 kr1] [r2 kr2] [s1' k1'] [ ] Hr. inv Hr. inv H.
      inv Hq. inv H. cbn in *. subst. inv Hs. inv H8.
      eexists; split; repeat econstructor; eauto.
    - intros [s1 k1] t [s1' k1'] Hstep s2 Hs.
      inv Hstep. inv H; inv Hs.
      + eexists. split. apply step1.
        instantiate (1 := (_, _)). econstructor; eauto.
        constructor.
      + eexists. split. apply step2.
        instantiate (1 := (_, _)). econstructor; eauto.
        constructor.
      + eexists. split. eapply CategoricalComp.step_push.
        instantiate (1 := (_, _)). constructor; cbn; eauto.
        instantiate (1 := (_, _)). econstructor; cbn; eauto.
        auto. auto. constructor.
      + eexists. split. eapply  CategoricalComp.step_pop.
        instantiate (1 := (_, _)). econstructor; cbn; eauto.
        instantiate (1 := (_, _)). econstructor; cbn; eauto.
        constructor.
    - apply well_founded_ltof.
  Qed.

  Lemma lift_categorical_comp2:
    comp_semantics' (L1 @ K) (L2 @ K) sk ≤ (comp_semantics' L1 L2 sk) @ K.
  Proof.
    constructor. econstructor. reflexivity. intros i. reflexivity.
    intros se _ [ ] ? [ ] Hse. instantiate (1 := fun _ _ _ => _). cbn beta.
    eapply forward_simulation_step
      with (match_states := fun s1 s2 => state_match s2 s1).
    - intros [q1 kq] _ s [ ] H. inv H. inv H0.
      destruct s0. cbn in *. subst.
      eexists (_, _). split; repeat (cbn; econstructor); auto.
    - intros s1 [s2 ks] [r kr] Hs H. inv H. inv H0.
      destruct s. cbn in *. subst. inv Hs.
      eexists (_, _). split; repeat (cbn; econstructor); auto.
    - intros s1 [s2 ks] [q kq] Hs H. inv H. inv H2.
      cbn in *. subst. inv Hs. cbn in *.
      eexists _, (_, _).
      repeat apply conj; repeat constructor; eauto.
      intros [r1 kr1] [r2 kr2] s1' <- Hr. inv Hr. inv H6.
      destruct s2'. cbn in *. subst.
      eexists; split; repeat (cbn; econstructor); eauto.
      cbn. constructor; auto.
    - intros s1 t s1' Hstep [s2 ks] Hs.
      inv Hstep; inv Hs.
      + destruct s1'0. inv H.
        eexists (_, _); split; constructor; auto.
        apply step1. auto.
      + destruct s2'. inv H.
        eexists (_, _); split; constructor; auto.
        apply step2. auto.
      + destruct q, s3. inv H. inv H0. cbn in *. subst.
        eexists (_, _); split; constructor; auto.
        eapply CategoricalComp.step_push; eauto.
      + destruct r, s1'0. inv H. inv H0. cbn in *. subst.
        eexists (_, _); split; constructor; auto.
        eapply CategoricalComp.step_pop; eauto.
    - apply well_founded_ltof.
      Unshelve. exact tt.
  Qed.

  Lemma lift_categorical_comp:
    (comp_semantics' L1 L2 sk) @ K ≡ comp_semantics' (L1 @ K) (L2 @ K) sk.
  Proof.
    split; [ exact lift_categorical_comp1 | exact lift_categorical_comp2 ].
  Qed.

End CAT_COMP_LIFT.

Section HCOMP_LIFT.

  Variable K: Type.
  Context {I li} (L: I -> Smallstep_.semantics li li).
  Variable (sk: AST.program unit unit).
  Let LK := fun i => (L i)@K.

  Inductive state_match_hcomp: (list (frame L) * K) -> list (frame LK) -> Prop :=
  | state_match_hcomp_nil k: state_match_hcomp (nil, k) nil
  | state_match_hcomp_cons i s k k' cont kcont:
      state_match_hcomp (cont, k') kcont ->
      state_match_hcomp (st L i s :: cont, k) (st LK i (s, k) :: kcont).

  Lemma lift_horizontal_comp1:
    (SmallstepLinking_.semantics' L sk)@K ≤ SmallstepLinking_.semantics' LK sk.
  Proof.
    constructor. econstructor. reflexivity.
    intros i. reflexivity.
    intros se _ [ ] ? [ ] Hse. instantiate (1 := fun _ _ _ => _). cbn beta.
    eapply forward_simulation_step with (match_states := state_match_hcomp).
    - intros [q kq] ? [s ks] [ ] H. inv H. cbn in *. subst.
      inv H0. eexists. split.
      + constructor. instantiate (1 := i).
        unfold LK. apply H.
        instantiate (1 := (_, _)). constructor; cbn; eauto.
      + repeat econstructor.
    - intros [s1 ks1] s2 [r kr] Hs H. inv H. cbn in *; subst.
      inv H0. inv Hs. subst_dep. inv H5.
      eexists (_, _). split; eauto.
      constructor. constructor; cbn; auto.
    - intros [s1 ks1] s2 [q kq] Hs H. inv H. cbn in *; subst.
      inv H0. inv Hs. subst_dep.
      eexists tt, (_, _). repeat apply conj; eauto.
      + repeat (constructor; auto).
      + intros [r1 kr1] [r2 kr2] [s' ks'] Hr Hx. inv Hr.
        inv Hx. cbn in *; subst. inv H0. subst_dep.
        eexists; split. constructor.
        instantiate (1 := (_, _)). constructor; cbn; eauto.
        econstructor. eauto.
    - intros [s1 ks1] t [s1' k1] Hstep s2 Hs. inv Hstep. inv H.
      + inv Hs. subst_dep. eexists; split.
        * constructor. instantiate (1 := (_, _)).
          constructor; eauto.
        * econstructor. eauto.
      + inv Hs. subst_dep. eexists; split.
        * eapply step_push with (q0 := (_, _)) (j0 := j) (s'0 := (_, _));
            [ constructor | | constructor]; cbn; eauto.
        * repeat econstructor. eauto.
      + inv Hs. subst_dep. inv H6. subst_dep. eexists; split.
        * eapply step_pop with (r0 := (_, _)) (s'0 := (_, _));
            constructor; cbn; eauto.
        * econstructor. eauto.
    - apply well_founded_ltof.
      Unshelve. exact ks.
  Qed.

  Lemma lift_horizontal_comp2:
    SmallstepLinking_.semantics' LK sk ≤ (SmallstepLinking_.semantics' L sk)@K.
  Proof.
    constructor. econstructor. reflexivity.
    intros i. reflexivity.
    intros se _ [ ] ? [ ] Hse. instantiate (1 := fun _ _ _ => _). cbn beta.
    eapply forward_simulation_step
      with (match_states := fun s1 s2 => state_match_hcomp s2 s1).
    - intros [q1 kq1] [q2 kq2] s1 [ ] H. inv H. inv H1.
      destruct s. cbn in *; subst.
      eexists (_, _). repeat apply conj; cbn; eauto.
      constructor; eauto. apply H0. econstructor. constructor.
    - intros s1 [s ks] [r kr] Hs H. inv H. inv H0.
      inv Hs. destruct s0. cbn in *; subst_dep. inv H5. inv H2.
      eexists (_, _). split; eauto.
      constructor; eauto. cbn. constructor. eauto.
    - intros s1 [s ks] [q kq] Hs H. inv H. inv H0.
      inv Hs. destruct s0. cbn in *. subst_dep. inv H6.
      eexists tt, (_, _). repeat apply conj; cbn; eauto.
      + constructor; eauto.
      + intros [r1 kr1] [r2 kr2] s' Hr Hx. inv Hr. inv Hx.
        destruct s'0, s2. subst_dep. inv H4. inv H7.
        cbn in *; subst.
        eexists (_, _). repeat apply conj; cbn; eauto.
        constructor. eauto.
        econstructor. eauto.
    - intros s1 t s1' Hstep [s ks] Hs. inv Hstep.
      + inv Hs. destruct s0, s'. inv H. subst_dep. inv H4.
        eexists. split.
        instantiate (1 := (_, _)). constructor; eauto.
        apply step_internal. eauto.
        econstructor. eauto.
      + inv Hs. destruct s0, q, s'. inv H. inv H1.
        cbn in *. subst_dep. inv H6.
        eexists (_, _); repeat apply conj; eauto.
        eapply step_push; eauto. apply H0.
        econstructor. econstructor. eauto.
      + inv Hs. destruct sk0, s0, r, s'. inv H. inv H0.
        cbn in *. subst_dep. inv H5. inv H2. subst_dep.
        eexists (_, _). repeat apply conj; eauto.
        eapply step_pop; eauto.
        econstructor. eauto.
    - apply well_founded_ltof.
      Unshelve. exact k.
  Qed.

  Lemma lift_horizontal_comp:
    (SmallstepLinking_.semantics' L sk)@K ≡ SmallstepLinking_.semantics' LK sk.
  Proof.
    split; [ exact lift_horizontal_comp1 | exact lift_horizontal_comp2 ].
  Qed.

End HCOMP_LIFT.

Lemma lifting_step_star {liA liB K} (L: Smallstep_.semantics liA liB) se qset s1 t s2 k:
  Star (L se) qset s1 t s2 ->
  Star(lifted_lts K (L se)) qset (s1, k) t (s2, k).
Proof.
  induction 1; [eapply star_refl | eapply star_step]; eauto.
  constructor; auto.
Qed.

Lemma lifting_step_plus {liA liB K} (L: Smallstep_.semantics liA liB) se qset s1 t s2 k:
  Plus (L se) qset s1 t s2 ->
  Plus (lifted_lts K (L se)) qset (s1, k) t (s2, k).
Proof.
  destruct 1; econstructor; eauto using lifting_step_star.
  split; eauto.
Qed.

Lemma lifting_simulation {K li1 li2} {L1 L2: Smallstep_.semantics li1 li2}:
  L1 ≤ L2 -> L1 @ K ≤ L2 @ K.
Proof.
  intros [H]. constructor.
  eapply Forward_simulation with
      (fsim_order H)
      (fun se1 se2 w i '(s1, k1) '(s2, k2) =>
         fsim_match_states H se1 se2 w i s1 s2 /\ k1 = k2).
  - apply (fsim_skel H).
  - intros i. apply (fsim_footprint H).
  - destruct H as [? ? ? ? ? Hf ?]. cbn. clear -Hf.
    intros se1 se2 [ ] qset Hse Hse'.
    specialize (Hf se1 se2 tt qset Hse Hse'). subst.
    econstructor.
    + intros [q kq] ? [s1 ks] [ ] Hi. inv Hi. cbn in *; subst.
      exploit (fsim_match_initial_states Hf); eauto. econstructor.
      intros (? & ? & ? & ?). eexists _, (_, _).
      repeat apply conj; cbn; eauto.
    + intros i [s1 ks1] [s2 ks2] [r kr] [Hs Hk] Hi.
      inv Hi. cbn in *; subst.
      exploit (fsim_match_final_states Hf); eauto.
      intros (? & ? & ?). inv H1.
      eexists (_, _). repeat apply conj; cbn; eauto.
    + intros i [s1 ks1] [s2 ks2] [q1 kq1] [Hs Hk] Hi.
      inv Hi. cbn in *; subst.
      exploit (fsim_match_external Hf); eauto.
      intros (? & ? & ? & Hq & ? & Hx). inv Hq.
      eexists tt, (_, _). repeat apply conj; cbn; eauto.
      intros [r kr] [? ?] [s1' Hs1'] <- Ha. inv Ha.
      cbn in *; subst. exploit Hx; eauto.
      intros (? & ? & ? & ?). eexists _, (_, _).
      repeat apply conj; cbn; eauto.
    + intros [s1 ks1] t [s1' ks1'] Hstep i [s2 ks2] [Hs Hk].
      inv Hstep. exploit (fsim_simulation Hf); eauto.
      intros (? & ? & Hx & ?). destruct Hx.
      * eexists _, (_, _); repeat apply conj; eauto.
        left. apply lifting_step_plus; auto.
      * eexists _, (_, _); repeat apply conj; eauto.
        right. destruct H1. split; eauto using lifting_step_star.
  - apply fsim_order_wf.
Qed.

Definition skel_extend {liA liB} (L: Smallstep_.semantics liA liB) sk :=
  {|
  activate se := L se;
  skel := sk;
  footprint := footprint L;
  |}.

(* Lifting a code skeleton *)
Section SKEL.
  Context {liA1 liB1 liA2 liB2}
          {cc1: callconv liA1 liA2}
          {cc2: callconv liB1 liB2}
          {L1: Smallstep_.semantics liA1 liB1}
          {L2: Smallstep_.semantics liA2 liB2}
          (HL: forward_simulation cc1 cc2 L1 L2).
  Variable (sk: AST.program unit unit).
  Hypothesis Hsk: linkorder (skel L1) sk.

  Lemma skel_extend_fsim:
    forward_simulation cc1 cc2 (skel_extend L1 sk) (skel_extend L2 sk).
  Proof.
    unfold skel_extend. destruct HL.
    constructor. econstructor. reflexivity.
    - intros; cbn. eapply fsim_footprint. apply X.
    - intros. exploit (fsim_lts X); eauto. cbn in *.
      eapply Genv.valid_for_linkorder; eauto.
    - apply (fsim_order_wf X).
  Qed.
End SKEL.

Section SKEL_EXT_LIFT.
  Context {K1 K2: Type}
          {liA1 liB1 liA2 liB2: language_interface}
          {cc1: callconv (liA1@K1) (liA2@K2)}
          {cc2: callconv (liB1@K1) (liB2@K2)}
          (L1: Smallstep_.semantics liA1 liB1)
          (L2: Smallstep_.semantics liA2 liB2).
  Hypothesis HL: forward_simulation cc1 cc2 (L1@K1) (L2@K2).
  Variable (sk: AST.program unit unit).
  Hypothesis Hsk: linkorder (skel L1) sk.
  Lemma lift_skel_extend:
    forward_simulation cc1 cc2 (skel_extend L1 sk @ K1)
                       (skel_extend L2 sk @ K2).
  Proof.
    destruct HL as [H]. constructor. econstructor.
    - reflexivity.
    - apply (fsim_footprint H).
    - intros. apply (fsim_lts H); auto.
      eapply Genv.valid_for_linkorder; eauto.
    - apply (fsim_order_wf H).
  Qed.
End SKEL_EXT_LIFT.
