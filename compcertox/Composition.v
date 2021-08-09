Require Import Relations RelationClasses Relators.
Require Import List Maps.
Require Import Coqlib.
Require Import CallconvAlgebra_.
Require Import LanguageInterface_ Events Globalenvs Smallstep_ CategoricalComp FlatComp.
Require Import Memory Values.
Require Import Clight_ Linking.
Require Import AbstractStateRel Lifting CModule CompCertO.

Definition layer_comp {K} (M: cmodule) (L: layer K) sk :=
  comp_semantics' (semantics M sk @ K) L sk.

Definition ksim {K1 K2: Type} (L1: layer K1) (L2: layer K2)
           (M: cmodule) (R: rel_adt K1 K2) :=
  linkorder (skel L2) (skel L1) /\
  skel_module_compatible (skel L1) M /\
  forward_simulation 1 R L1 (layer_comp M L2 (skel L1)).

Lemma compatible_app sk M N:
  skel_module_compatible sk M ->
  skel_module_compatible sk N ->
  skel_module_compatible sk (M ++ N).
Proof.
  unfold skel_module_compatible.
  rewrite !Forall_forall.
  intros Hm Hn p Hp. apply in_app_or in Hp.
  destruct Hp; [ apply Hm | apply Hn ]; auto.
Qed.

Lemma compatible_trans sk1 sk2 N:
  linkorder sk1 sk2 ->
  skel_module_compatible sk1 N ->
  skel_module_compatible sk2 N.
Proof.
  unfold skel_module_compatible.
  rewrite !Forall_forall.
  intros; eapply linkorder_trans; eauto.
Qed.

Section SKEL_EXT.
  Context {liA liB liC}
          (L1: Smallstep_.semantics liB liC)
          (L2: Smallstep_.semantics liA liB).
  Lemma skel_extend_compose sk sk':
    skel_extend (comp_semantics' L1 L2 sk) sk' ≤ comp_semantics' L1 L2 sk'.
  Proof.
    constructor. eapply Forward_simulation with _ (fun _ _ _ => _); auto.
    - intros. reflexivity.
    - intros se ? [ ] qset [ ] Hse.
      eapply forward_simulation_plus with (match_states := eq);
        cbn; intros; subst; eauto 10 using plus_one.
      exists tt, q1. intuition (subst; eauto).
  - apply well_founded_ltof.
  Qed.

  Lemma skel_extend_component sk sk':
    comp_semantics' (skel_extend L1 sk) L2 sk' ≤ comp_semantics' L1 L2 sk'.
  Proof.
  Admitted.

End SKEL_EXT.

Section VCOMP.

  Context {K1 K2 K3 L1 L2 L3} {M N: cmodule}
          {R: rel_adt K1 K2} {S: rel_adt K2 K3}
          (HL1: ksim L1 L2 M R) (HL2: ksim L2 L3 N S).
  Hypothesis HM: (List.length M >= 1)%nat.
  Hypothesis HN: (List.length N >= 1)%nat.

  Theorem layer_vcomp: ksim L1 L3 (M ++ N) (R ∘ S).
  Proof.
    unfold ksim in *.
    destruct HL1 as [Hsk1 [Hmod1 H1]].
    destruct HL2 as [Hsk2 [Hmod2 H2]].
    split. eapply linkorder_trans; eauto.
    split. apply compatible_app; eauto.
    eapply compatible_trans; eauto.

    assert (HX1: forward_simulation 1 R L1
                 (layer_comp M (skel_extend L2 (skel L1)) (skel L1))).
    { admit. }
    assert (HX2: forward_simulation 1 S (skel_extend L2 (skel L1))
                 (layer_comp N L3 (skel L1))).
    {
      eapply skel_extend_fsim in H2; eauto.
      eapply open_fsim_ccref. apply cc_compose_id_left.
      unfold flip. apply cc_compose_id_right.
      eapply compose_forward_simulations. apply H2.
      unfold layer_comp. etransitivity.
      apply skel_extend_compose.

      admit.
    }
    edestruct (cmodule_krel S M (skel L1) HM). auto.
    exploit @categorical_compose_simulation'.
    constructor. exact X. apply HX2.

    instantiate (1 := (skel L1)). admit.
    cbn. apply linkorder_refl. intros Hsim2.

    eapply open_fsim_ccref. apply cc_compose_id_left.
    unfold flip. reflexivity.
    cbn. eapply compose_forward_simulations.
    apply HX1. unfold layer_comp.

    eapply open_fsim_ccref. apply cc_compose_id_left.
    unfold flip. apply cc_compose_id_right.
    eapply compose_forward_simulations. apply Hsim2.

    eapply open_fsim_ccref. apply cc_compose_id_left.
    unfold flip. apply cc_compose_id_left.
    eapply compose_forward_simulations.
    unfold layer_comp. apply assoc1.

    eapply categorical_compose_simulation';
      [ | apply identity_forward_simulation
        | apply linkorder_refl
        | eapply linkorder_trans; eauto
      ].

    eapply open_fsim_ccref. apply cc_compose_id_left.
    unfold flip. apply cc_compose_id_left.
    eapply compose_forward_simulations.
    apply lift_categorical_comp2.
    apply lifting_simulation.
    apply cmodule_simulation; eauto.
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
