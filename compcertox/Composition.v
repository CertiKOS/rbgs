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
  forward_simulation 1 R L1 (layer_comp M L2 (skel L1)).

Section VCOMP.

  Context {K1 K2 K3 L1 L2 L3} {M N: cmodule}
          {R: rel_adt K1 K2} {S: rel_adt K2 K3}
          (HL1: ksim L1 L2 M R) (HL2: ksim L2 L3 N S).
  Hypothesis HM: (List.length M >= 1)%nat.
  Hypothesis HN: (List.length N >= 1)%nat.

  Theorem layer_vcomp: ksim L1 L3 (M ++ N) (R ∘ S).
  Proof.
    unfold ksim in *.
    pose proof (cmodule_krel S M (skel L1) HM) as Hsim1.
    exploit @categorical_compose_simulation'.
    exact Hsim1. exact HL2.


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
