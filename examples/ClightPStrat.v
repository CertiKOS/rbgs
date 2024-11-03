(* Require Import Classical. *)
(* Require Import Program.Equality. *)
(* Require Import LogicalRelations. *)
Require Import Poset.
(* Require Import Lattice. *)
(* Require Import Downset. *)
(* Require Import IntStrat. *)
(* Require Import Classical_Prop. *)
(* Require Import Coqlib. *)

Require Import FunctionalExtensionality.
Require Import IntStrat.
Require Import CompCertStrat.
Require Import PEnv ClightP ClightPComp.
Require Import BQUtil.

Require LanguageInterface.
Import -(notations) LanguageInterface.

Section LIFT_CONVERT.

  Context {li: language_interface} {S: Type}.

  Program Definition liftr_emor : emor (Lifting.lifted_li S li) (li @ S) :=
    fun q =>
      match q with
      | ((se, q)%embed, s) =>
          econs (se, Datatypes.pair q s)%embed (fun '(r, s) => (r, s))
      end.

  Lemma liftr_lift:
    ecomp lift_emor liftr_emor = eid.
  Proof.
    apply functional_extensionality_dep. intros [se [q s]].
    unfold eid, ecomp. cbn. f_equal.
    apply functional_extensionality. intros [r s']. reflexivity.
  Qed.

  Lemma liftr_emor_property:
    rsq vid lift_emor liftr_emor (id (Lifting.lifted_li S li)).
  Proof.
    rewrite <- (compose_id_l liftr_emor).
    rewrite <- liftr_lift.
    rewrite emor_strat_ecomp.
    eapply rsq_comp.
    - apply emor_strat_intro.
    - apply rsq_id_conv. reflexivity.
  Qed.

End LIFT_CONVERT.

(** Embed ClightP semantics into strategies *)
Section CLIGHTP.

  Definition pin vars ce : li_c <=> li_c := de (p0 vars) ;; lift_emor ;; pin ce.
  Definition pout : li_c <=> li_c := pout.

  Context (p: ClightP.program).
  Let ce := p.(ClightP.prog_comp_env).

  Definition clightp_strat : li_c ->> li_c @ penv :=
    liftr_emor ⊙ lts_strat (ClightP.clightp2 p).

  Lemma clightp_rsq:
    rsq vid lift_emor clightp_strat (lts_strat (ClightP.clightp2 p)).
  Proof.
    unfold clightp_strat.
    rewrite <- compose_id_l.
    eapply rsq_comp.
    - apply liftr_emor_property.
    - eapply rsq_id_conv. reflexivity.
  Qed.

  Definition eclightp_strat : li_c ->> li_c :=
    encap (p0 (vars_of_program p)) (id (li_c @ penv)) ⊙ clightp_strat.

  Context (tp: Clight.program) (Hp: ClightP.transl_program p = Errors.OK tp).

  Lemma eclightp_correct:
    rsq pout (pin (vars_of_program p) (ClightP.prog_comp_env p))
      eclightp_strat (lts_strat (Clight.semantics2 tp)).
  Proof.
    apply transl_program_correct in Hp.
    apply fsim_rsq in Hp. 2: apply Determ.clight_determinate.
    unfold pin, eclightp_strat.
    rewrite <- compose_id_l.
    eapply rsq_comp.
    - eapply rsq_vcomp.
      3: apply deencap_rsq.
      1-2: typeclasses eauto.
      apply rsq_id_strat. reflexivity.
    - rewrite vcomp_vid_l.
      erewrite <- (vcomp_vid_l pout).
      eapply rsq_vcomp.
      4: apply Hp.
      apply lts_strat_determ. apply Determ.clightp_determinate.
      apply lts_strat_determ. apply Determ.clight_determinate.
      apply clightp_rsq.
  Qed.

End CLIGHTP.

Section POUT_POUT.

  Lemma pout_pout : pout ;; pout [= pout.
  Admitted.

End POUT_POUT.

Section PIN_PIN.

  Import Ctypes AST Maps.

  Context (vars1 vars2: list (ident * PEnv.val))
    (Hvs: PEnv.vars_disjoint vars1 vars2).
  Let vars := (vars1 ++ vars2)%list.
  Context (ce ce1 ce2: composite_env).
  Context (Hce1: forall id co, ce1 ! id = Some co -> ce ! id = Some co).
  Context (Hce2: forall id co, ce2 ! id = Some co -> ce ! id = Some co).
  Context (Hvs1: vars_type_ok ce1 vars1).
  Context (Hvs2: vars_type_ok ce2 vars2).

  Lemma pin_pin : pin vars ce [= pin vars1 ce1 ;; pin vars2 ce2.
  Admitted.

End PIN_PIN.

Section CLIGHTP_OUT.

  Context (p: ClightP.program).

  Lemma eclightp_out:
    rsq pout pout (eclightp_strat p) (eclightp_strat p).
  Admitted.

End CLIGHTP_OUT.

Section CLIGHT_IN.

  Import AST Ctypes.

  Context (p: Clight.program) (vars: list (ident * val)) (ce: composite_env).

  Lemma clight_in:
    rsq (pin vars ce) (pin vars ce)
      (lts_strat (Clight.semantics2 p))
      (lts_strat (Clight.semantics2 p)).
  Admitted.

End CLIGHT_IN.

Section COMP.

  Context p1 p2 tp1 tp2
    (HT1: transl_program p1 = Errors.OK tp1)
    (HT2: transl_program p2 = Errors.OK tp2)
    (Hvs: PEnv.vars_disjoint (vars_of_program p1) (vars_of_program p2)).
  Context p (Hp: Linking.link p1 p2 = Some p).

  Let vars1 := vars_of_program p1.
  Let vars2 := vars_of_program p2.
  Let sk := ClightP.clightp_erase_program p.
  Let vars := (vars1 ++ vars2)%list.
  Let ce1 := ClightP.prog_comp_env p1.
  Let ce2 := ClightP.prog_comp_env p2.
  Let ce := ClightP.prog_comp_env p.

  Import List Maps Coqlib.

  Lemma Hce1: forall id co, ce1 ! id = Some co -> ce ! id = Some co.
  Proof.
    apply Linking.link_linkorder in Hp as [Hp1 Hp2].
    destruct Hp1 as (A & B & C). apply B.
  Qed.
  Lemma Hce2: forall id co, ce2 ! id = Some co -> ce ! id = Some co.
  Proof.
    apply Linking.link_linkorder in Hp as [Hp1 Hp2].
    destruct Hp2 as (A & B & C). apply B.
  Qed.
  Lemma Hvs1: vars_type_ok ce1 vars1.
  Proof.
    generalize (ClightP.prog_priv_ok p1).
    intros H i x Hi.
    unfold vars_of_program, init_of_pvars in Hi.
    apply in_map_iff in Hi as ((i' & x') & Hi' & Hx'). inv Hi'.
    specialize (H _ _ Hx'). apply H.
  Qed.
  Lemma Hvs2: vars_type_ok ce2 vars2.
  Proof.
    generalize (ClightP.prog_priv_ok p2).
    intros H i x Hi.
    unfold vars_of_program, init_of_pvars in Hi.
    apply in_map_iff in Hi as ((i' & x') & Hi' & Hx'). inv Hi'.
    specialize (H _ _ Hx'). apply H.
  Qed.

  Lemma clightp_comp:
    rsq pout (pin vars ce)
      (eclightp_strat p1 ⊙ eclightp_strat p2)
      (lts_strat (Clight.semantics2 tp1) ⊙ lts_strat (Clight.semantics2 tp2)).
  Proof.
    rewrite <- pout_pout. unfold vars.
    erewrite (pin_pin vars1 vars2 Hvs ce ce1 ce2); eauto using Hce1, Hce2, Hvs1, Hvs2.
    eapply rsq_comp with (S := pout ;; pin vars2 ce2).
    - eapply rsq_vcomp. 1-2: admit.
      apply eclightp_correct; eauto.
      apply clight_in.
    - eapply rsq_vcomp. 1-2: admit.
      apply eclightp_out.
      apply eclightp_correct; eauto.
  Admitted.

End COMP.
