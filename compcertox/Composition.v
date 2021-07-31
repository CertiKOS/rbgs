Require Import Relations RelationClasses Relators.
Require Import List Maps.
Require Import Coqlib.
Require Import CallconvAlgebra_.
Require Import LanguageInterface_ Events Globalenvs Smallstep_ CategoricalComp FlatComp.
Require Import Memory Values.
Require Import Clight_ Linking.
Require Import AbstractStateRel Lifting.

Set Implicit Arguments.
Set Asymmetric Patterns.

Inductive rel_adt: Type -> Type -> Type :=
| empty_rel K: rel_adt K K
| singleton_rel {K1 K2} : krel K1 K2 -> rel_adt K1 K2
| vcomp_rel {K1 K2 K3} : rel_adt K1 K2 -> rel_adt K2 K3 -> rel_adt K1 K3.

(* Why asymmetric patterns flag doesn't work? *)
Fixpoint absrel_to_cc {K1 K2} (rel: rel_adt K1 K2):
  callconv (li_c @ K1) (li_c @ K2) :=
  match rel with
  | empty_rel _ => cc_id
  | singleton_rel _ _ r => kcc_c r
  | vcomp_rel _ _ _ r1 r2 => (absrel_to_cc r1) @ (absrel_to_cc r2)
  end.

Delimit Scope krel_scope with krel.
Bind Scope krel_scope with rel_adt.

Notation "[ R ]" := (singleton_rel R) (at level 30): krel_scope.
Notation "R1 ∘ R2" := (vcomp_rel R1 R2): krel_scope.

Coercion absrel_to_cc : rel_adt >-> callconv.

(* A module is a list of compilation units. Specifically, they are Clight
   programs at this time. Note that in the layer library the modules are
   organized as mapping from identifiers to vars or functions. A module like
   that is transformed into a Clight program by [make_program] because separate
   compilation is not supported. However, here a module is nothing but a list of
   programs and the semantics is given by the horizontal composition of the
   Clight programs *)
Notation cmodule := (list Clight_.program).

Fixpoint semantics (cmod: cmodule) sk: semantics li_c li_c :=
  match cmod with
  | nil => id_semantics sk
  | (p :: ps) =>
    let L b := match b with
               | true  => Clight_.semantics1 p
               | false => semantics ps sk
               end
    in SmallstepLinking_.semantics L sk
  end.

Notation cmod_combine := app.
Notation " M ++ N " := (cmod_combine M N).

Definition layer_comp {K} (M: cmodule) (L: layer K) sk :=
  comp_semantics' (semantics M sk @ K) L sk.

Definition ksim {K1 K2: Type} (L1: layer K1) (L2: layer K2)
           (M: cmodule) (R: rel_adt K1 K2) :=
  forward_simulation 1 R L1 (layer_comp M L2 (skel L1)).

Section LIST_IND.
  Variable A: Type.
  Variable P: list A -> Prop.
  Variable P1: forall x, P (x :: nil).
  Variable Pcons: forall x xs, P xs -> P (x :: xs).

  Theorem list_ind1: forall xs, (List.length xs >= 1)%nat -> P xs.
  Proof.
    set (Q := fun l => (Datatypes.length l >= 1)%nat -> P l).
    apply (@list_ind A Q).
    - unfold Q. inversion 1.
    - subst Q. cbn. intros.
      destruct l.
      + apply P1.
      + apply Pcons. apply H. cbn. firstorder.
  Qed.
End LIST_IND.

Instance fsim_transitive {li1 li2: language_interface}:
  Transitive (forward_simulation (@cc_id li1) (@cc_id li2)).
Proof.
  intros L1 L2 L3 HL1 HL2.
  eapply open_fsim_ccref. apply cc_compose_id_left.
  unfold flip. apply cc_compose_id_left.
  eapply compose_forward_simulations; eauto.
Qed.

Definition skel_extend {liA liB} (L: Smallstep_.semantics liA liB) sk :=
  {|
    activate se := L se;
    skel := sk;
    footprint := footprint L;
  |}.

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

Section HCOMP_INIT_STATE.
  Context {li} (L1 L2: Smallstep_.semantics li li).
  Let L := fun i => match i with | true => L1 | false => L2 end.
  Hypothesis H: forall i q s se, Smallstep_.initial_state (L i se) q s ->
                            valid_query (L i) se q.

  Lemma initial_state_valid_comp sk:
    forall q s se,
      Smallstep_.initial_state (SmallstepLinking_.semantics L sk se) q s ->
      valid_query (SmallstepLinking_.semantics L sk) se q.
  Proof.
    intros q s se Hx. inv Hx. destruct i.
    - exploit H; eauto. firstorder.
    - exploit H; eauto. firstorder.
  Qed.
End HCOMP_INIT_STATE.

Lemma cmodule_initial_state_valid sk M:
  (List.length M >= 1)%nat ->
  forall se s q, Smallstep_.initial_state (semantics M sk se) q s ->
            valid_query (semantics M sk) se q.
Proof.
  set (P := fun M => forall se s q, Smallstep_.initial_state (semantics M sk se) q s -> valid_query (semantics M sk) se q).
  apply (@list_ind1 _ P); subst P; cbn beta.
  - intros. inv H. destruct H0 as (? & ? & ? & ?). destruct i.
    + unfold valid_query. split; auto.
      eexists; split; eauto. now left.
    + inv H0.
  - intros p ps IH se s q H.
    cbn. eapply initial_state_valid_comp.
    * intros. destruct i.
      eapply initial_state_valid; eauto.
      eapply IH; eauto.
    * apply H.
Qed.

(* TODO: move this to lifting.v *)
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

Lemma singleton_app {A} x (xs: list A):
  app (x :: nil) xs = x :: xs.
Proof. firstorder. Qed.

(* M has to be non-empty is due to the fact that we can't prove id ∘ L ≡ L *)
Lemma cmodule_simulation {M N : cmodule} {sk1 sk2 sk: AST.program unit unit}:
  (List.length N >= 1)%nat -> (List.length M >= 1)%nat ->
  comp_semantics' (semantics M sk1) (semantics N sk2) sk ≤ semantics (M ++ N) sk.
Proof.
  intros HN.
  set (P := fun l => comp_semantics' (semantics l sk1) (semantics N sk2) sk ≤ semantics (l ++ N) sk).
  apply (@list_ind1 _ P); subst P; cbn beta.
  - intros p. etransitivity.
    apply categorical_compose_approximation.
    {
      intros [|] se q s H.
      - eapply cmodule_initial_state_valid; eauto.
      - eapply cmodule_initial_state_valid; eauto.
    }
    rewrite singleton_app. cbn.
    apply horizontal_compose_simulation'.
    +

Admitted.

(* A special case of categorical_compose_simulation *)
Lemma categorical_compose_simulation'
      {liA1 liA2 liB1 liB2 liC1 liC2}
      (cc1: callconv liA1 liA2) (cc2: callconv liB1 liB2) (cc3: callconv liC1 liC2)
      L1a L1b L1 L2a L2b L2 sk:
  forward_simulation cc2 cc3 L1a L2a ->
  forward_simulation cc1 cc2 L1b L2b ->
  comp_semantics' L1a L1b sk = L1 ->
  comp_semantics' L2a L2b sk = L2 ->
  forward_simulation cc1 cc3 L1 L2.
Proof.
Admitted.

Lemma clight_krel {K1 K2} (R: rel_adt K1 K2) p:
  forward_simulation R R (Clight_.semantics1 p @ K1) (Clight_.semantics1 p @ K2).
Proof.
  induction R; simpl.
  - apply lifting_simulation.
    apply identity_forward_simulation.
  - apply clight_sim.
  - eapply compose_forward_simulations; eauto.
Qed.

Lemma cmodule_krel {K1 K2} (R: rel_adt K1 K2) M sk:
  forward_simulation R R (semantics M sk @ K1) (semantics M sk @ K2).
Proof.
Admitted.


Section VCOMP.

  Context {K1 K2 K3 L1 L2 L3} {M N: cmodule}
          {R: rel_adt K1 K2} {S: rel_adt K2 K3}
          (HL1: ksim L1 L2 M R) (HL2: ksim L2 L3 N S).

  Theorem layer_vcomp: ksim L1 L3 (M ++ N) (R ∘ S).
  Proof.
    unfold ksim in *.
    pose proof (cmodule_krel S M (skel L1)) as Hsim1.
    exploit @categorical_compose_simulation'.
    exact Hsim1. exact HL2. reflexivity. reflexivity.
    instantiate (1 := (skel L1)).
    intros Hsim2.

    eapply open_fsim_ccref. apply cc_compose_id_left.
    unfold flip. reflexivity.
    cbn. eapply compose_forward_simulations.
    apply HL1. unfold layer_comp.

    eapply open_fsim_ccref. apply cc_compose_id_left.
    unfold flip. apply cc_compose_id_right.
    eapply compose_forward_simulations. apply Hsim2.

    eapply open_fsim_ccref. apply cc_compose_id_left.
    unfold flip. apply cc_compose_id_left.
    eapply compose_forward_simulations.
    unfold layer_comp. apply assoc1.

    eapply categorical_compose_simulation';
      [ | apply identity_forward_simulation
        | reflexivity
        | reflexivity
      ].

    eapply open_fsim_ccref. apply cc_compose_id_left.
    unfold flip. apply cc_compose_id_left.
    eapply compose_forward_simulations.
    apply lift_categorical_comp2.
    apply lifting_simulation.
    apply cmodule_simulation.
  Qed.

End VCOMP.

Section HCOMP.

  Context {K1 K2 L1 L2 L3} {M N: cmodule} {R: rel_adt K1 K2}
          (HL1: ksim L1 L3 M R) (HL2: ksim L2 L3 N R).

  Theorem layer_hcomp L:
    L1 ⊎ L2 = Some L -> ksim L L3 (M ⊕ N) R.
  Admitted.

  (* Naming convention:
     xxx is the composition definition or lemma with linked skeleton
     xxx' is the same with a provided code skeleton *)
  Theorem layer_hcomp' sk:
    ksim (flat_comp_semantics' L1 L2 sk) L3 (M ⊕ N) R.
  Admitted.

End HCOMP.
