(* This file contains definitions that will be moved to CompCertO later *)

Require Import Relations RelationClasses Relators.
Require Import List Maps.
Require Import Coqlib.
Require Import CallconvAlgebra_.
Require Import LanguageInterface_ Events Globalenvs Smallstep_ CategoricalComp FlatComp.
Require Import Memory Values.
Require Import Linking.

(* TODO: move this to compcert *)
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

Section HCOMP_ASSOC.

  Context {li} (L1 L2 L3: Smallstep_.semantics li li).
  Variable (sk: AST.program unit unit).
  Let L := fun b => match b with
                 | true => SmallstepLinking_.semantics
                            (fun b => match b with | true => L1 | false => L2 end) sk
                 | false => L3
                 end.
  Let L' := fun b => match b with
                  | true => L1
                  | false => SmallstepLinking_.semantics
                              (fun b => match b with | true => L2 | false => L3 end) sk
                  end.

  Lemma horizontal_compose_associativity:
    SmallstepLinking_.semantics L sk ≤ SmallstepLinking_.semantics L' sk.
  Proof.
  Admitted.

End HCOMP_ASSOC.
