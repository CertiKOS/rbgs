Require Import Relations RelationClasses Relators.
Require Import List Maps.
Require Import Coqlib.
Require Import CallconvAlgebra_.
Require Import LanguageInterface_ Events Globalenvs Smallstep_ CategoricalComp FlatComp.
Require Import Memory Values.
Require Import Clight_ Linking.
Require Import AbstractStateRel Lifting CModule.

Definition layer_comp {K} (M: cmodule) (L: layer K) sk :=
  comp_semantics' (semantics M sk @ K) L sk.

Definition ksim {K1 K2: Type} (L1: layer K1) (L2: layer K2)
           (M: cmodule) (R: rel_adt K1 K2) :=
  linkorder (skel L2) (skel L1) /\
  skel_module_compatible M (skel L1) /\
  forward_simulation 1 R L1 (layer_comp M L2 (skel L1)).

Lemma compatible_app sk M N:
  skel_module_compatible M sk ->
  skel_module_compatible N sk ->
  skel_module_compatible (M ++ N) sk.
Proof.
  unfold skel_module_compatible.
  rewrite !Forall_forall.
  intros Hm Hn p Hp. apply in_app_or in Hp.
  destruct Hp; [ apply Hm | apply Hn ]; auto.
Qed.

Lemma compatible_trans sk1 sk2 N:
  linkorder sk1 sk2 ->
  skel_module_compatible N sk1 ->
  skel_module_compatible N sk2.
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
    - intros se ? [ ] [ ] Hse.
      eapply forward_simulation_plus with (match_states := eq);
        cbn; intros; subst; eauto 10 using plus_one.
      exists tt, q1. intuition (subst; eauto).
  - apply well_founded_ltof.
  Qed.
End SKEL_EXT.

Section VCOMP.

  Context {K1 K2 K3 L1 L2 L3} {M N: cmodule}
          {R: rel_adt K1 K2} {S: rel_adt K2 K3}
          (HL1: ksim L1 L2 M R) (HL2: ksim L2 L3 N S).
  (* FIXME: the linkable hypothesis should be simplified *)
  Context `{!CategoricalLinkable (semantics M (skel L1)) (semantics N (skel L1))}.

  Theorem layer_vcomp: ksim L1 L3 (M ++ N) (R ∘ S).
  Proof.
    unfold ksim in *.
    destruct HL1 as [Hsk1 [Hmod1 H1]]. clear HL1.
    destruct HL2 as [Hsk2 [Hmod2 H2]]. clear HL2.
    split. eapply linkorder_trans; eauto.
    split. apply compatible_app; eauto.
    eapply compatible_trans; eauto.

    edestruct (cmodule_krel S M (skel L1)). auto.
    exploit @categorical_compose_simulation'.
    constructor. exact X. apply H2.
    instantiate (1 := (skel L1)). apply linkorder_refl. auto.
    clear X. intros X.

    eapply open_fsim_ccref. apply cc_compose_id_left.
    unfold flip. reflexivity.
    cbn. eapply compose_forward_simulations.
    apply H1. unfold layer_comp.

    eapply open_fsim_ccref. apply cc_compose_id_left.
    unfold flip. apply cc_compose_id_right.
    eapply compose_forward_simulations. apply X. clear X.

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
    apply cmodule_app_simulation'; eauto.
  Qed.

End VCOMP.

Section HCOMP.

  Generalizable All Variables.
  Context `{R: rel_adt K1 K2}
          {M N: cmodule} `(HL1: ksim L1 L3 M R) `(HL2: ksim L2 L3 N R).
  Variable (sk: AST.program unit unit).
  Hypothesis (Hk1: linkorder (skel L1) sk)
             (Hk2: linkorder (skel L2) sk).
  (* Theorem layer_hcomp L: *)
  (*   L1 ⊎ L2 = Some L -> ksim L L3 (M ⊕ N) R. *)
  (* Admitted. *)

  (* Naming convention: *)
  (*      xxx is the composition definition or lemma with linked skeleton *)
  (*      xxx' is the same with a provided code skeleton *)
  Theorem layer_hcomp':
    ksim (flat_comp_semantics' L1 L2 sk) L3 (M ++ N) R.
  Proof.
    unfold ksim in *.
    destruct HL1 as [Hsk1 [Hmod1 H1]]. clear HL1.
    destruct HL2 as [Hsk2 [Hmod2 H2]]. clear HL2.
    split. eapply linkorder_trans; eauto.
    split. apply compatible_app; (eapply compatible_trans; [ | eauto]); eauto.



  Admitted.

End HCOMP.
