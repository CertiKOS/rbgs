Require Import Classical.
Require Import Program.Equality.
Require Import LogicalRelations.
Require Import Poset.
Require Import Lattice.
Require Import Downset.
Require Import IntStrat.
Require Import Classical_Prop.
Require Import Coqlib.
Require Import IntStrat CompCertStrat.
From compcert Require Import Smallstep Globalenvs.
Require LanguageInterface.
Import -(notations) LanguageInterface.
Require Clight Join Memory Lifting.

(** * § 6.2 Memory Separation *)

(** ** Theorem 6.2 (The frame property for Clight)  *)

Global Instance emor_rc_regular {E F} (f: emor E F):
  RegularConv f.
Proof.
  split. intros * Hm Hn. apply antisymmetry.
  - intros x Hx. cbn in *.
    dependent destruction Hx.
    apply H.
    destruct (classic (operand (f m2) n1 = n2)); eauto.
    exfalso. apply Hn. constructor; eauto.
  - intros x Hx. cbn in *.
    dependent destruction Hm.
    econstructor; eauto.
Qed.

Lemma emor_rc_allow_intro {E1 E2} (f: emor E1 E2) m1 m2:
  m1 = operator (f m2) ->
  emor_rc_has f (rcp_allow m1 m2).
Proof. intros. subst. eapply emor_rc_allow. Qed.

(** An auxiliary structure that converts between CompCertO's spatial composition
    and strategy's spatial composition. This is useful for us to reuse some
    properties provided by CompCertO *)

Section LIFT_CONVERT.

  Import FunctionalExtensionality.

  Context {li: language_interface} {S: Type}.

  Program Definition lift_emor : emor (li @ S) (Lifting.lifted_li S li) :=
    fun q =>
      match q with
      | (se, Datatypes.pair q s)%embed =>
          econs ((se, q)%embed, s) (fun '(r, s) => (r, s))
      end.
  Program Definition liftr_emor : emor (Lifting.lifted_li S li) (li @ S) :=
    fun q =>
      match q with
      | ((se, q)%embed, s) =>
          econs (se, Datatypes.pair q s)%embed (fun '(r, s) => (r, s))
      end.

  Lemma liftr_lift: ecomp lift_emor liftr_emor = eid.
  Proof.
    apply functional_extensionality_dep. intros [se [q s]].
    unfold eid, ecomp. cbn. f_equal.
    apply functional_extensionality. intros [r s']. reflexivity.
  Qed.
  Lemma lift_liftr: ecomp liftr_emor lift_emor = eid.
  Proof.
    apply functional_extensionality_dep. intros [[se q] s].
    unfold eid, ecomp. cbn. f_equal.
    apply functional_extensionality. intros [r s']. reflexivity.
  Qed.

  Lemma rsq_lift_emor_1: rsq vid lift_emor liftr_emor (id _).
  Proof.
    rewrite <- (compose_id_l liftr_emor).
    rewrite <- liftr_lift.
    rewrite emor_strat_ecomp.
    eapply rsq_comp.
    - apply emor_strat_intro.
    - apply rsq_id_conv. reflexivity.
  Qed.

  Lemma rsq_lift_emor_2:  rsq lift_emor vid (id _) liftr_emor.
  Proof.
    rewrite <- (compose_id_r liftr_emor).
    rewrite <- lift_liftr at 1.
    rewrite emor_strat_ecomp.
    eapply rsq_comp.
    - apply rsq_id_conv. reflexivity.
    - apply emor_strat_elim.
  Qed.

  Lemma lift_emor_operator se q s:
    ((se, q)%embed, s) = operator (lift_emor (se, Datatypes.pair q s))%embed.
  Proof. intros. reflexivity. Qed.

  Lemma rsq_lift_emor sk L:
    rsq lift_emor lift_emor
      ((lts_strat_sk sk L) @ S)
      (lts_strat_sk sk (Lifting.lifted_semantics S L)).
  Proof.
    Ltac split_evar := instantiate (1 := (_, _)).
    setoid_rewrite <- closure_lift.
    apply rsq_closure; eauto with typeclass_instances.
    intros p (s & t & Hs & Ht & Hst). cbn in *.
    dependent destruction Ht. { xinv Hs. apply rsp_ready. constructor. }
    dependent destruction Hs. apply rsp_oq. { constructor. }
    intros qx Hq. xinv Hq. destruct qx as (se1 & q1 & s1).
    cbn in H0. inv H0. rename q2 into d1.
    simple inversion Hst; try congruence. xsubst; congruence.
    clear Hst. xsubst. inv H2. inv H3. xsubst. intros Hst Hu.
    eapply rsp_ref. 1-3: reflexivity.
    { instantiate (1 := state_strat _ _ _ _ _).
      cbn. intros. econstructor; eauto.
      split. split_evar.
      instantiate (1 := u).
      all: cbn; eauto. } clear Hu.
    (* assert ((IntStrat.get slens_id (d1, tt)) = d1). reflexivity. *)
    (* setoid_rewrite H in Hst. clear H. *)
    clear HVF INIT. revert d1 u s2 s Hs Hst.
    dependent induction HS; intros.
    - dependent destruction Hs. eapply rsp_pq.
      { instantiate (1 := (_, _)%embed). split_evar.
        rewrite lift_emor_operator. constructor. }
      dependent destruction Hs. apply rsp_suspended.
      econstructor. split; cbn; eauto.
      xinv Hst. easy.
    - dependent destruction Hs. eapply rsp_pq.
      { instantiate (1 := (_, _)%embed). split_evar.
        rewrite lift_emor_operator. constructor. }
      dependent destruction Hs. apply rsp_oa.
      { econstructor. split; cbn; eauto. xinv Hst. easy. }
      cbn. intros [r xs] Hr.
      destruct (classic ((n, n2) = (r, xs))).
      2: { exfalso. apply Hr.
           rewrite lift_emor_operator. constructor. eauto. }
      inv H.
      rewrite regular_conv; eauto.
      2: { rewrite lift_emor_operator. constructor. }
      xinv Hst. dependent destruction H1.
      eapply rsp_ref. 1-3: reflexivity.
      2: { eapply IHHS; eauto. }
      intros p Hp. cbn. econstructor 2.
      { split; eauto. }
      { split. split_evar. all: cbn; eauto. }
      apply Hp.
    - dependent destruction Hs. dependent destruction Hs.
      dependent destruction Hst.
      eapply rsp_pa.
      { intros Hr. xinv Hr. apply H0. constructor. }
      apply rsp_ready. cbn.
      econstructor 3. split; eauto.
    - eapply rsp_ref. 1-3: reflexivity.
      2: { eapply IHHS; eauto. }
      intros p Hp. econstructor 4. split_evar. 2: apply Hp.
      apply Lifting.lifting_step_star; eauto.
  Qed.

End LIFT_CONVERT.

(** ** The frame property *)

Section CLIGHT.

  Import AST Values Join.
  Context (p: Clight.program) (vars: list (ident * val)).

  Lemma clight_expr_lvalue_join mx ge:
    forall e le m1 m2,
      join mx m1 m2 ->
      (forall expr v,
          Clight.eval_expr ge e le m1 expr v ->
          Clight.eval_expr ge e le m2 expr v)
      /\
      (forall expr b ofs bf,
         Clight.eval_lvalue ge e le m1 expr b ofs bf ->
         Clight.eval_lvalue ge e le m2 expr b ofs bf).
  Proof.
    intros * HM.
    apply Clight.eval_expr_lvalue_ind;
      try solve [ intros; econstructor; eauto ].
    - intros. econstructor. eauto.
      exploit sem_unary_operation_join; eauto.
      rewrite H1. intros X. inv X. reflexivity.
    - intros. econstructor; eauto.
      exploit sem_binary_operation_join; eauto.
      rewrite H3. intros X. inv X. reflexivity.
    - intros. econstructor; eauto.
      exploit sem_cast_join; eauto.
      rewrite H1. intros X. inv X. reflexivity.
    - intros. econstructor; eauto.
      exploit deref_loc_join; eauto.
  Qed.

  Lemma clight_expr_join mx ge:
    forall e le m1 m2 expr v,
      join mx m1 m2 ->
      Clight.eval_expr ge e le m1 expr v ->
      Clight.eval_expr ge e le m2 expr v.
  Proof.
    intros. eapply clight_expr_lvalue_join in H.
    destruct H. apply H; eauto.
  Qed.

  Lemma clight_lvalue_join mx ge:
    forall e le m1 m2 expr b ofs bf,
      join mx m1 m2 ->
      Clight.eval_lvalue ge e le m1 expr b ofs bf ->
      Clight.eval_lvalue ge e le m2 expr b ofs bf.
  Proof.
    intros. eapply clight_expr_lvalue_join in H.
    destruct H. apply H1; eauto.
  Qed.

  Lemma clight_exprlist_join mx ge:
    forall e le m1 m2 al tyargs vargs,
      join mx m1 m2 ->
      Clight.eval_exprlist ge e le m1 al tyargs vargs ->
      Clight.eval_exprlist ge e le m2 al tyargs vargs.
  Proof.
    intros * HM HX. induction HX; cbn.
    - constructor.
    - exploit clight_expr_join; eauto. intros A.
      exploit sem_cast_join; eauto. rewrite H0.
      intros B. inv B.
      econstructor; eauto.
  Qed.

  Lemma clight_function_entry_join mx ge:
    forall f vargs m1 m2 m1' e le,
      join mx m1 m2 ->
      Clight.function_entry2 ge f vargs m1 e le m1' ->
      exists m2', Clight.function_entry2 ge f vargs m2 e le m2' /\ join mx m1' m2'.
  Proof.
    intros * HM HX. inv HX.
    exploit alloc_variables_join; eauto. intros (? & A & B).
    eexists. split; eauto. econstructor; eauto.
    destruct HM. inv mjoin_alloc_flag; congruence.
  Qed.

End CLIGHT.

Section FRAME.
  Import Clight Join Memory.Mem.
  Import -(notations) Lifting.

  Inductive join_query : query (lifted_li mem li_c) -> query li_c -> Prop :=
  | join_query_intro vf sg vargs m msrc mtgt
      (MJOIN: Join.join m msrc mtgt):
    join_query (cq vf sg vargs msrc, m) (cq vf sg vargs mtgt).

  Inductive join_reply: reply (lifted_li mem li_c) -> reply li_c -> Prop :=
  | join_reply_intro rv m msrc mtgt
      (MJOIN: Join.join m msrc mtgt):
    join_reply (cr rv msrc, m) (cr rv mtgt).

  Program Definition join_cc : callconv (lifted_li mem li_c) li_c :=
    {|
      ccworld := unit;
      match_senv _ se1 se2 := se1 = se2;
      LanguageInterface.match_query _ := join_query;
      LanguageInterface.match_reply _ := join_reply;
    |}.
  Next Obligation. reflexivity. Qed.
  Next Obligation. inv H0. reflexivity. Qed.
  Next Obligation. inv H. reflexivity. Qed.

  Context (p: program).
  Inductive join_ms : state * mem -> state -> Prop :=
  | clightp_ms_State:
    forall f s k e le mx m1 m2 (HJ: join mx m1 m2),
      join_ms (State f s k e le m1, mx) (State f s k e le m2)
  | join_ms_Callstate:
    forall vf args k mx m1 m2 (HJ: join mx m1 m2),
      join_ms (Callstate vf args k m1, mx) (Callstate vf args k m2)
  | join_ms_Returnstate:
    forall rv k mx m1 m2 (HJ: join mx m1 m2),
      join_ms (Returnstate rv k m1, mx) (Returnstate rv k m2).

  Lemma join_step ge mx:
    forall s1 t s1',
    Clight.step2 ge s1 t s1' ->
    forall s2, join_ms (s1, mx) s2 ->
    exists s2', Clight.step2 ge s2 t s2' /\
    join_ms (s1', mx) s2'.
  Proof with (eexists _; split; econstructor; eauto).
    induction 1; intros S1 HS; inv HS;
      try solve [ eexists _; split; econstructor; eauto ].
    - exploit clight_lvalue_join; eauto. intros A.
      exploit clight_expr_join; eauto. intros B.
      exploit sem_cast_join; eauto.
      rewrite H1. intros C. inv C.
      exploit assign_loc_join; eauto. intros (? & D & E)...
    - exploit clight_expr_join; eauto. intros A...
    - exploit clight_expr_join; eauto. intros A.
      exploit clight_exprlist_join; eauto; intros B...
    - exploit clight_exprlist_join; eauto. intros A.
      exploit ClightP.external_call_join; eauto. intros (? & B & C)...
    - exploit clight_expr_join; eauto. intros A.
      exploit bool_val_join; eauto.
      rewrite H0. intros B. inv B...
    - exploit free_list_join; eauto.
      rewrite H. intros A. inv A...
    - exploit clight_expr_join; eauto. intros A.
      exploit sem_cast_join; eauto.
      rewrite H0. intros B. inv B.
      exploit free_list_join; eauto.
      rewrite H1. intros C. inv C...
    - exploit free_list_join; eauto.
      rewrite H0. intros A. inv A...
    - exploit clight_expr_join; eauto. intros A...
    - exploit clight_function_entry_join; eauto. intros (? & A & B)...
    - exploit ClightP.external_call_join; eauto. intros (? & A & B)...
  Qed.

  (** The frame property in term of the CompCertO's simulation *)
  Lemma frame_property :
    forward_simulation join_cc join_cc (lifted_semantics mem (semantics2 p)) (semantics2 p).
  Proof.
    constructor. econstructor. reflexivity. firstorder.
    instantiate (1 := fun _ _ _ => _). cbn beta.
    intros se1 se2 w Hse Hse1. cbn -[semantics2] in *. subst se2.
    rename w into mx.
    eapply forward_simulation_step with (match_states := join_ms).
    - intros [q1 mq] q2 [s1 ms] Hq Hi. cbn in *. eprod_crush.
      inv Hq. inv H.
      eexists. split; econstructor; eauto.
      apply mjoin_nextblock in MJOIN.
      rewrite MJOIN. unfold Ple in *.
      etransitivity; eauto.
      apply Pos.le_max_r.
    - intros [s1 ms1] s2 [r1 mr1] Hjoin Hf.
      inv Hf. cbn in *. subst. inv H. inv Hjoin.
      eexists. split; constructor; eauto.
    - intros [s1 ms1] s2 [q1 mq1] Hjoin He.
      inv He. cbn in *. subst. inv H. inv Hjoin.
      eexists tt, _. repeat apply conj; eauto.
      + econstructor; eauto.
      + constructor; eauto.
      + intros [r1 mr1] r2 [s1' ms1'] Hjoin Hr.
        eprod_crush. inv H. inv Hjoin.
        eexists. split; constructor; eauto.
    - intros [s1 ms1] t [s1' ms1'] [HS <-] s2 Hjoin.
      eapply join_step; eauto.
    - apply well_founded_ltof.
  Qed.

  Definition join_conv : conv (li_c @ mem) li_c := lift_emor ;; join_cc.

  Import Determ.

  Lemma frame_property_ref_sk sk:
    Linking.linkorder (skel (semantics2 p)) sk ->
    rsq join_conv join_conv (lts_strat_sk sk (semantics2 p) @ mem) (lts_strat_sk sk (semantics2 p)).
  Proof.
    intros Hlink. unfold join_conv. eapply rsq_vcomp.
    3: apply rsq_lift_emor.
    apply lts_strat_determ. apply lifting_determinate. apply clight_determinate.
    apply lts_strat_determ. apply clight_determinate.
    apply fsim_rsq_sk. apply clight_determinate.
    apply frame_property. apply Hlink.
  Qed.

  (* The frame property using refinement. *)
  Lemma frame_property_ref:
    rsq join_conv join_conv (lts_strat (semantics2 p) @ mem) (lts_strat (semantics2 p)).
  Proof.
    apply frame_property_ref_sk.
    apply Linking.linkorder_refl.
  Qed.

End FRAME.

