Require Import Classical.
Require Import Program.Equality.
(* Require Import LogicalRelations. *)
Require Import Poset.
(* Require Import Lattice. *)
Require Import Downset.
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

(* rsq rb_cc (lift_emor ;; rb_cc ;; liftr_emor) liftr_emor liftr_emor *)

End LIFT_CONVERT.

Require Import Coqlib Memory.

(* Ltac emor_change := *)
(*   match goal with *)
(*   | [ |- emor_rc_has ?f (rcp_allow ?m1 ?m2) ] => *)
(*       replace m1 with (operator (f m2)) by reflexivity *)
(*   | [ |- emor_rc_has ?f (rcp_forbid ?m1 ?m2 _ _) ] => *)
(*       replace m1 with (operator (f m2)) by reflexivity *)
(*   end. *)

(* Section POUT. *)

(*   (** C@mem⊛⟨mem]^* *) *)
(*   Definition pout : li_c <=> li_c := trur ;; li_c @ lcp ldrop ;; join_conv. *)
(*   Lemma pout_ref : cc_conv ClightP.pout [= pout. *)
(*   Proof. *)
(*     rewrite cc_conv_expand. *)
(*     intros p [w Hp]. destruct w as [w|]. *)
(*     2: { inv Hp. } *)
(*     cbn in w. revert w Hp. induction p; intros w Hp. *)
(*     - cbn in *. dependent destruction Hp. *)
(*       cbn in *. subst. *)
(*       eexists ((_, _)%embed, tt). split. *)
(*       { emor_change. constructor. } *)
(*       eexists ((_, _)%embed, _). split. *)
(*       { split; eauto. emor_change. constructor. } *)
(*       eexists (_, Datatypes.pair _ _)%embed. split. *)
(*       { emor_change. constructor. } *)
(*       econstructor. reflexivity. inv HM. constructor. eauto. *)
(*     - cbn in *. dependent destruction Hp. *)
(*       cbn in *. subst. inv HM. *)
(*       eexists ((_, _)%embed, tt). split. *)
(*       { emor_change. constructor. } *)
(*       split. *)
(*       { eexists ((_, _)%embed, _). split. *)
(*         { split; eauto. emor_change. constructor. } *)
(*         eexists (_, Datatypes.pair _ _)%embed. split. *)
(*         { emor_change. constructor. } *)
(*         econstructor. reflexivity. constructor. eauto. } *)
(*       intros [n []]. *)
(*       destruct (classic (n1 = n)). *)
(*       2: { left. emor_change. constructor. cbn. congruence. } *)
(*       subst. right. eexists ((_, _)%embed, _). *)
(*       split. *)
(*       { split; eauto. emor_change. constructor. } *)
(*       split. *)
(*       { eexists (_, Datatypes.pair _ _)%embed. split. *)
(*         { emor_change. constructor. } *)
(*         econstructor. reflexivity. constructor. eauto. } *)
(*       intros [nr mr]. *)
(*       destruct (classic (w = mr /\ n = nr)) as [[<- <-]|]. *)
(*       2: { admit. } *)
(*       right. *)
(*       eexists (_, Datatypes.pair _ _)%embed. split. *)
(*       { emor_change. constructor. } *)
(*       split. *)
(*       { econstructor. reflexivity. constructor. eauto. } *)
(*       intros [nr mr]. *)
(*       destruct (classic (w = mr /\ n = nr)) as [[<- <-]|]. *)
(*       2: { admit. } *)
(*       right. econstructor. reflexivity. *)
(*       constructor. eauto. intros Hn. apply HN. *)
(*       inv Hn. constructor. eauto. *)
(*     - cbn in *. dependent destruction Hp. *)
(*       cbn in *. subst. inv HM. *)
(*       eexists ((_, _)%embed, tt). split. *)
(*       { emor_change. constructor. } *)
(*       split. *)
(*       { eexists ((_, _)%embed, _). split. *)
(*         { split; eauto. emor_change. constructor. } *)
(*         eexists (_, Datatypes.pair _ _)%embed. split. *)
(*         { emor_change. constructor. } *)
(*         econstructor. reflexivity. constructor. eauto. } *)
(*       intros [n []]. *)
(*       destruct (classic (n1 = n)). *)
(*       2: { left. emor_change. constructor. cbn. congruence. } *)
(*       subst. right. *)
(*   Admitted. *)

(*   Lemma pout_pout : pout ;; pout [= pout. *)
(*   Proof. *)
(*     unfold pout. *)
(*   Admitted. *)

(* End POUT. *)

(** Embed ClightP semantics into strategies *)
Section CLIGHTP.

  Definition pin vars ce : li_c <=> li_c := de (p0 vars) ;; lift_emor ;; pin ce.

  Context (p: ClightP.program).
  Let ce := p.(ClightP.prog_comp_env).

  Definition clightp_strat : li_c ->> li_c @ penv :=
    liftr_emor ⊙ lts_strat (ClightP.clightp2 p).
  Definition clightp_strat_sk sk: li_c ->> li_c @ penv :=
    liftr_emor ⊙ lts_strat_sk sk (ClightP.clightp2 p).

  Lemma clightp_sk_rsq sk:
    rsq vid lift_emor (clightp_strat_sk sk) (lts_strat_sk sk (ClightP.clightp2 p)).
  Proof.
    unfold clightp_strat.
    rewrite <- compose_id_l.
    eapply rsq_comp.
    - apply liftr_emor_property.
    - eapply rsq_id_conv. reflexivity.
  Qed.

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
    apply transl_program_correct in Hp.
    apply fsim_rsq in Hp. 2: apply Determ.clight_determinate.
    erewrite <- (vcomp_vid_l pout).
    eapply rsq_vcomp.
    4: apply Hp.
    apply lts_strat_determ. apply Determ.clightp_determinate.
    apply lts_strat_determ. apply Determ.clight_determinate.
    apply clightp_rsq.
  Qed.

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

Section POUT_POUT.

  Lemma pout_pout : pout ;; pout [= cc_conv pout.
  Proof.
    (* intros p. induction p. *)
    (* - rename m2 into m3. *)
    (*   intros (m2 & Hm1 & Hm2). cbn in *. *)
    (*   dependent destruction Hm1. *)
    (*   dependent destruction Hm2. cbn in *. subst. *)
    (*   inv HM. inv HM0. *)
    (*   apply join_commutative in MJOIN. *)
    (*   apply join_commutative in MJOIN0. *)
    (*   edestruct join_associative_exist as (mx & X & Y). *)
    (*   apply MJOIN. apply MJOIN0. *)
    (*   econstructor. reflexivity. *)
    (*   econstructor. apply join_commutative. eauto. *)
    (* - rename m2 into m3, n2 into n3. *)
    (*   intros (m2 & Hm1 & Hm2 & Hn). cbn in *. *)
    (*   dependent destruction Hm1. *)
    (*   dependent destruction Hm2. cbn in *. subst. *)
    (*   inv HM. inv HM0. *)
    (*   apply join_commutative in MJOIN. *)
    (*   apply join_commutative in MJOIN0. *)
    (*   edestruct join_associative_exist as (mx & X & Y). *)
    (*   apply MJOIN. apply MJOIN0. *)
    (*   econstructor. instantiate (1:=mx). reflexivity. *)
    (*   + constructor. apply join_commutative. eauto. *)
    (*   + intros Hx. inv Hx. *)
    (*     specialize (Hn (cr rv mx)) as [Hn|Hn]. *)
    (*     * inv Hn. inv HM. apply HN. constructor. *)
    (*       dependent destruction *)
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
