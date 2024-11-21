Require Import Classical.
Require Import Program.Equality.
Require Import Poset.
Require Import Downset.

Require Import FunctionalExtensionality.
Require Import IntStrat CompCertStrat Frame.
Require Import PEnv ClightP.
Require Import BQUtil.
Require LanguageInterface.
Import -(notations) LanguageInterface.
Require Import Coqlib Memory.

(** * §6.5 Embed ClightP semantics into strategies *)

(** The semantics of ClightP in defined using CompCertO's transition system, and
    the definitions and correctness proofs can be found in ClightP.v. Here we
    embed the ClightP semantics into the strategy model. The embedding is also
    used in the bounded queue example. *)

Section CLIGHTP.

  Definition pin vars ce : li_c <=> li_c := de (p0 vars) ;; lift_emor ;; pin ce.
  Definition vars_of_program (p: ClightP.program) :=
    init_of_pvars p.(ClightP.prog_private).

  Context (p: ClightP.program).
  Let ce := p.(ClightP.prog_comp_env).

  Definition clightp_strat_sk sk: li_c ->> li_c @ penv :=
    liftr_emor ⊙ lts_strat_sk sk (ClightP.clightp2 p).

  (** The ClightP semantics in the strategy model
        ClightP(M): C@mem ↠ C@mem@penv *)
  Definition clightp_strat : li_c ->> li_c @ penv :=
    clightp_strat_sk (ClightP.clightp_erase_program p).

  Lemma clightp_sk_rsq sk:
    rsq vid lift_emor (clightp_strat_sk sk) (lts_strat_sk sk (ClightP.clightp2 p)).
  Proof.
    unfold clightp_strat.
    rewrite <- compose_id_l.
    eapply rsq_comp.
    - apply rsq_lift_emor_1.
    - eapply rsq_id_conv. reflexivity.
  Qed.

  Lemma clightp_rsq:
    rsq vid lift_emor clightp_strat (lts_strat (ClightP.clightp2 p)).
  Proof. apply clightp_sk_rsq. Qed.

  (** The ClightP semantics with state encapsulation
        ClightP⟨M⟩: C@mem ↠ C@mem *)
  Definition eclightp_strat : li_c ->> li_c :=
    encap (p0 (vars_of_program p)) (id (li_c @ penv)) ⊙ clightp_strat.

  Context (tp: Clight.program) (Hp: ClightP.transl_program p = Errors.OK tp).

  (** The correctness property of compiling ClightP programs into Clight
      programs. *)
  Lemma clightp_correct_sk sk:
    Linking.linkorder (ClightP.clightp_erase_program p) sk ->
    rsq pout (lift_emor ;; ClightP.pin (ClightP.prog_comp_env p))
      (clightp_strat_sk sk) (lts_strat_sk sk (Clight.semantics2 tp)).
  Proof.
    intros Hlink. cbn in Hlink.
    apply transl_program_correct in Hp.
    eapply fsim_rsq_sk with (sk := sk) in Hp; eauto.
    2: apply Determ.clight_determinate.
    erewrite <- (vcomp_vid_l pout).
    eapply rsq_vcomp.
    4: apply Hp.
    apply lts_strat_determ. apply Determ.clightp_determinate.
    apply lts_strat_determ. apply Determ.clight_determinate.
    apply clightp_sk_rsq.
  Qed.

  Lemma clightp_correct:
    rsq pout (lift_emor ;; ClightP.pin (ClightP.prog_comp_env p))
      clightp_strat (lts_strat (Clight.semantics2 tp)).
  Proof.
    unfold lts_strat.
    exploit clightp_skel_correct; eauto.
    intros Hskel. cbn. rewrite <- Hskel.
    apply clightp_correct_sk.
    apply Linking.linkorder_refl.
  Qed.

  (** The correctness property with state encapsulation *)
  Lemma eclightp_correct:
    rsq pout (pin (vars_of_program p) (ClightP.prog_comp_env p))
      eclightp_strat (lts_strat (Clight.semantics2 tp)).
  Proof.
    unfold pin, eclightp_strat.
    rewrite <- compose_id_l.
    eapply rsq_comp.
    - eapply rsq_vcomp.
      3: apply deencap_rsq.
      1-2: typeclasses eauto.
      apply rsq_id_strat. reflexivity.
    - rewrite vcomp_vid_l.
      apply clightp_correct.
  Qed.

End CLIGHTP.

