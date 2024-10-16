From compcert Require Import
     AST Coqlib Maps Values Integers Errors Events
     LanguageInterface Smallstep Globalenvs Memory Floats.
From compcert Require Import
     CategoricalComp.
From compcert.clightp Require Import
     TensorComp Lifting
     PEnv ClightP Encapsulation.
From compcert Require Import Join Ctypes.
Require Import Lia.
Require Import LogicalRelations.

Generalizable All Variables.

(** ------------------------------------------------------------------------- *)
(** patch to the identity semantics *)
Section LEFT_UNIT.
  Context {liA liB} (L: semantics liA liB).
  Definition left_comp_id' :=
    comp_semantics' (id_semantics (skel L)) L (skel L).

  Inductive lc_ms: state left_comp_id' -> state (∘ L) -> Prop :=
  | lc_ms_q q:
    lc_ms (st1 (id_semantics (skel L)) _ (st_q q)) (st1 1%lts _ (st_q q))
  | lc_ms_s q s:
    lc_ms (st2 (id_semantics (skel L)) _ (st_q q) s) (st2 1%lts _ (st_q q) s)
  | lc_ms_r r:
    lc_ms (st1 (id_semantics (skel L)) _ (st_r r)) (st1 1%lts _ (st_r r)).
  Hint Constructors lc_ms.

  Lemma left_unit_sk_irrelevent_1:
    forward_simulation 1 1 left_comp_id' (∘ L).
  Proof.
    constructor. econstructor. reflexivity. firstorder.
    intros. inv H.
    apply forward_simulation_step with (match_states := lc_ms).
    - intros * Hq Hs. inv Hq. inv Hs. inv H.
      eexists. split. repeat constructor. eauto.
    - intros * Hs Hf. inv Hf. inv H. inv Hs.
      eexists. split. repeat constructor. constructor.
    - intros * Hs Hq. inv Hq. inv Hs.
      eexists tt, _. repeat split; eauto.
      intros * Hr Hs. inv Hr. inv Hs.
      eexists. split. repeat constructor; eauto. eauto.
    - intros * HS * Hs. inv HS; inv Hs; try inv H.
      + eexists. split. 2: econstructor. apply step2. eauto.
      + eexists. split. 2: econstructor.
        eapply step_push; eauto. constructor.
      + inv H1. eexists. split. 2: econstructor.
        eapply step_pop; eauto. constructor.
    - apply well_founded_ltof.
  Qed.

  Lemma left_unit_sk_irrelevent_2:
    forward_simulation 1 1 (∘ L) left_comp_id'.
  Proof.
    constructor. econstructor. reflexivity. firstorder.
    intros. inv H.
    apply forward_simulation_step with (match_states := flip lc_ms);
      unfold flip.
    - intros * Hq Hs. inv Hq. inv Hs. inv H.
      eexists. split. repeat constructor. eauto.
    - intros * Hs Hf. inv Hf. inv H. inv Hs.
      eexists. split. repeat constructor. constructor.
    - intros * Hs Hq. inv Hq. inv Hs.
      eexists tt, _. repeat split; eauto.
      intros * Hr Hs. inv Hr. inv Hs.
      eexists. split. repeat constructor; eauto. eauto.
    - intros * HS * Hs. inv HS; inv Hs; try inv H.
      + eexists. split. 2: econstructor. apply step2. eauto.
      + eexists. split. 2: econstructor.
        eapply step_push; eauto. constructor.
      + inv H1. eexists. split. 2: econstructor.
        eapply step_pop; eauto. constructor.
    - apply well_founded_ltof.
  Qed.

  Lemma left_unit_1':
    CAT.forward_simulation 1 1 L left_comp_id'.
  Proof.
    unfold CAT.forward_simulation, normalize_sem.
    etransitivity. instantiate (1 := ∘ left_comp_id L ∘).
    apply CAT.left_unit_1.
    eapply categorical_compose_simulation'.
    - reflexivity.
    - eapply categorical_compose_simulation'.
      + apply left_unit_sk_irrelevent_2.
      + reflexivity.
      + apply Linking.linkorder_refl.
      + apply CategoricalComp.id_skel_order.
    - apply CategoricalComp.id_skel_order.
    - apply Linking.linkorder_refl.
  Qed.

  Lemma left_unit_2':
    CAT.forward_simulation 1 1 left_comp_id' L.
  Proof.
    unfold CAT.forward_simulation, normalize_sem.
    etransitivity. instantiate (1 := ∘ left_comp_id L ∘).
    2: { apply CAT.left_unit_2. }
    eapply categorical_compose_simulation'.
    - reflexivity.
    - eapply categorical_compose_simulation'.
      + apply left_unit_sk_irrelevent_1.
      + reflexivity.
      + apply Linking.linkorder_refl.
      + apply CategoricalComp.id_skel_order.
    - apply CategoricalComp.id_skel_order.
    - apply Linking.linkorder_refl.
  Qed.
End LEFT_UNIT.

(** ------------------------------------------------------------------------- *)
(** simulation conventions *)

Instance mem_pset ce (vars: list (ident * val)) : PSet mem :=
  { pset_init se := m0 ce vars se }.
Instance penv_pset (vars: list (ident * val)) : PSet penv :=
  { pset_init _ := p0 vars }.
Instance symtbl_pset : PSet Genv.symtbl :=
  { pset_init se := se }.

Instance mem_world ce (vars: list (ident * val)): World mem :=
  {|
    w_state := mem;
    w_pset := mem_pset ce vars;
    (* maybe we need unchanged_on *)
    w_int_step := {| Encapsulation.rel := fun m1 m2 => True |};
    w_ext_step := {| Encapsulation.rel := eq |};
  |}.

Instance se_world : World Genv.symtbl :=
  {|
    w_state := Genv.symtbl;
    w_pset := symtbl_pset;
    w_int_step := {| Encapsulation.rel := eq |};
    w_ext_step := {| Encapsulation.rel := eq |};
  |}.

Definition unp_out: ST.callconv li_c li_c := &pout.

(* TODO: define [join_query] and [join_reply] *)
Inductive unp_penv_query: Memory.mem -> query (li_c@penv) -> query (li_c@penv) -> Prop :=
| unp_penv_query_intro vf sg vargs m msrc mtgt pe
    (MJOIN: join m msrc mtgt):
  unp_penv_query m (cq vf sg vargs msrc, pe) (cq vf sg vargs mtgt, pe).

Inductive unp_penv_reply: Memory.mem -> reply (li_c@penv) -> reply (li_c@penv) -> Prop :=
| unp_penv_reply_intro rv m msrc mtgt pe
    (MJOIN: join m msrc mtgt):
  unp_penv_reply m (cr rv msrc, pe) (cr rv mtgt, pe).

Program Definition unp_penv' : callconv (li_c@penv) (li_c@penv) :=
  {|
    ccworld := Memory.mem;
    match_senv _ se1 se2 := se1 = se2;
    match_query := unp_penv_query;
    match_reply := unp_penv_reply;
  |}.
Next Obligation. reflexivity. Qed.
Next Obligation. inv H0. reflexivity. Qed.
Next Obligation. inv H. reflexivity. Qed.

Definition unp_penv: ST.callconv (li_c@penv) (li_c@penv) := &unp_penv'.

Inductive unp_in_query: Memory.mem -> query li_c -> query li_c -> Prop :=
| unp_in_query_intro vf sg vargs m msrc mtgt
    (MJOIN: join m msrc mtgt):
  unp_in_query m (cq vf sg vargs msrc) (cq vf sg vargs mtgt).

Inductive unp_in_reply: Memory.mem -> reply li_c -> reply li_c -> Prop :=
| unp_in_reply_intro rv m msrc mtgt
    (MJOIN: join m msrc mtgt):
  unp_in_reply m (cr rv msrc) (cr rv mtgt).

Program Definition unp_in ce vars : ST.callconv li_c li_c :=
  {|
    ST.ccworld := Genv.symtbl * mem;
    ST.ccworld_world := world_prod se_world (mem_world ce vars);
    ST.match_senv '(se, _) se1 se2 := se = se1 /\ se = se2;
    ST.match_query '(_, m) := unp_in_query m;
    ST.match_reply '(_, m) := unp_in_reply m;
  |}.
Next Obligation. reflexivity. Qed.
Next Obligation. inv H0. reflexivity. Qed.
Next Obligation. inv H. reflexivity. Qed.

Definition vars_of_program (p: ClightP.program) :=
  init_of_pvars p.(ClightP.prog_private).

Definition eclightp (p: ClightP.program) :=
  comp_esem'
    (@encap_prim _ penv (penv_pset (vars_of_program p))
       (ClightP.clightp_erase_program p))
    (semantics_embed (ClightP.clightp2 p))
    (ClightP.clightp_erase_program p).

(** ------------------------------------------------------------------------- *)
(** promote the result from [ClightP.v] to encapsulation version *)

Lemma valid_for_pvars (p: ClightP.program) se:
  Genv.valid_for (ClightP.clightp_erase_program p) se ->
  valid_pvars (ClightP.prog_private p) se.
Proof.
  intros H id pv HV.
  assert (exists g, (prog_defmap (ClightP.clightp_erase_program p)) ! id = Some g)
    as (g & Hg).
  {
    apply prog_defmap_dom. cbn -[PTree_Properties.of_list].
    apply in_map_iff. eexists (id, _). split; eauto.
    apply PTree_Properties.in_of_list.
    rewrite PTree_Properties.of_list_elements.
    rewrite PTree.gcombine by reflexivity.
    pose proof (ClightP.prog_norepet p) as HP.
    apply list_norepet_app in HP as (HP1 & HP2 & HP).
    erewrite PTree_Properties.of_list_norepet; eauto.
    destruct ((prog_defmap (ClightP.program_of_program p)) ! id)
      eqn: Hd.
    - exfalso. eapply HP; eauto.
      + apply in_map_iff. eexists (id, _). split; eauto.
      + apply in_map_iff. eexists (id, _). split; eauto.
        apply PTree_Properties.in_of_list.
        apply Hd.
    - reflexivity.
  }
  specialize (H _ _ Hg).
  destruct H as (? & ? & ?). eexists. apply H.
Qed.

Open Scope nat_scope.
Section ESIM.

  Context prog tprog (HT: transl_program prog = OK tprog).
  Let S := eclightp prog.
  Let T := semantics_embed (Clight.semantics2 tprog).
  Let vars := vars_of_program prog.
  Let ce := prog.(ClightP.prog_comp_env).
  Let sk := ClightP.clightp_erase_program prog.

  Inductive encap_ms se : mem -> penv -> @state (li_c@penv) (li_c@penv) 1 -> @state li_c li_c 1 -> Prop :=
  | encap_ms_q m pe vf sg vargs msrc mtgt
      (MJOIN: join m msrc mtgt)
      (HPE: penv_mem_match ce se pe m):
    encap_ms se m pe (@st_q (li_c@penv) ((cq vf sg vargs msrc), pe)) (st_q (cq vf sg vargs mtgt))
  | encap_ms_r m pe rv msrc mtgt
      (MJOIN: join m msrc mtgt)
      (HPE: penv_mem_match ce se pe m):
    encap_ms se m pe (@st_r (li_c@penv) ((cr rv msrc), pe)) (st_r (cr rv mtgt)).

  Lemma penv_encap:
    E.forward_simulation
     (& (pin ce)) (unp_in ce vars)
     (@encap_prim _ penv (penv_pset vars) sk)
     (semantics_embed (id_semantics sk)).
  Proof.
    apply st_normalize_fsim. constructor.
    eapply ST.Forward_simulation with
      (ltof _ (fun (_: unit) => 0))
      (fun se0 _ _ _ '((se, m), (pe, _)) _ s1 s2 =>
         encap_ms se m pe s1 s2 /\ se0 = se)
      (fun _ '((se, m), (pe, _)) => penv_mem_match ce se pe m);
      try easy.
    - intros. cbn in *. eprod_crush. eauto.
    - intros. cbn in *. apply vars_init.
      + eapply build_composite_env_consistent.
        subst ce. eapply ClightP.prog_comp_env_eq.
      + apply valid_for_pvars. apply H.
      + apply prog.
    - intros. cbn in *. constructor; cbn.
      + intros. eprod_crush. subst. inv H3. inv H4.
        eexists tt, _. split. constructor.
        eexists tt, (_, _, (_, tt)). repeat split; eauto.
        econstructor; eauto.
      + intros. eprod_crush. inv H2. inv H3. inv H3.
        eexists (_, tt). split; eauto.
        eexists. repeat split.
        eexists (_, _, (_, tt)). split.
        repeat split; eauto. split; eauto.
        split; eauto. constructor; eauto.
      + intros. eprod_crush. inv H3. inv H2.
        eexists. split. constructor.
        eexists _, (_, _). split; eauto. split; eauto. split.
        constructor; eauto. split; eauto.
        intros. eprod_crush. inv H3. inv H2.
        eexists tt, _. split.
        eexists _. split. reflexivity. constructor.
        eexists tt, (_, _, (_, tt)). split; eauto.
        split. 2: split; constructor; eauto.
        repeat split.
      + easy.
  Qed.

  Lemma promote_clightp:
    E.forward_simulation unp_out (unp_in ce vars) S T.
  Proof.
    rewrite <- (ccref_right_unit2 unp_out).
    rewrite (ccref_right_unit1 (unp_in ce vars)).
    eapply encap_fsim_vcomp.
    instantiate (1 := (comp_esem' (semantics_embed (id_semantics sk)) T sk)).
    - eapply encap_fsim_lcomp_sk.
      instantiate (1 := &(pin ce)).
      + apply penv_encap.
      + apply encap_fsim_embed.
        apply transl_program_correct. eauto.
      + apply Linking.linkorder_refl.
      + apply Linking.linkorder_refl.
    - rewrite ccref_left_unit1 at 2.
      rewrite <- ccref_left_unit2 at 1.
      eapply encap_fsim_vcomp; eauto.
      instantiate (1 := semantics_embed _).
      2: { apply encap_fsim_embed_cat. apply left_unit_2'. }
      assert (skel (Clight.semantics2 tprog) = sk).
      { apply transl_program_correct in HT as [X].
        symmetry. apply X. }
      unfold left_comp_id'. rewrite H.
      apply encap_comp_embed1.
  Qed.

End ESIM.

(** ------------------------------------------------------------------------- *)
(** Properties *)

Section UNP_IN.

  Context (vars1 vars2: list (ident * val)) (Hvs: PEnv.vars_disjoint vars1 vars2).
  Let vars := vars1 ++ vars2.
  Context (ce ce1 ce2: composite_env).
  Context (Hce1: forall id co, ce1 ! id = Some co -> ce ! id = Some co).
  Context (Hce2: forall id co, ce2 ! id = Some co -> ce ! id = Some co).
  Context (Hvs1: vars_type_ok ce1 vars1).
  Context (Hvs2: vars_type_ok ce2 vars2).

  Inductive unp_in_inv:
    ST.ccstate (ST.cc_compose (unp_in ce1 vars1) (unp_in ce2 vars2)) ->
    ST.ccstate (unp_in ce vars) -> Prop :=
  | unp_in_inv_intro:
    forall m m1 m2 se, join m1 m2 m -> unp_in_inv ((se, m1), (se, m2)) (se, m).
  Inductive unp_in_ms se:
    ST.ccstate (ST.cc_compose (unp_in ce1 vars1) (unp_in ce2 vars2)) ->
    ST.ccstate (unp_in ce vars) -> @state li_c li_c 1 -> @state li_c li_c 1 -> Prop :=
  | unp_in_ms_query:
    forall q1 q2 m1 m2 m
      (MQ: ST.match_query (unp_in ce vars) (se, m) q1 q2)
      (MJ: join m1 m2 m),
      unp_in_ms se ((se, m1), (se, m2)) (se, m) (st_q q1) (st_q q2)
  | unp_in_ms_reply:
    forall r1 r2 m1 m2 m
      (MR: ST.match_reply (unp_in ce vars) (se, m) r1 r2)
      (MJ: join m1 m2 m),
      unp_in_ms se ((se, m1), (se, m2)) (se, m) (st_r r1) (st_r r2).

  Lemma unp_in_idemp:
    st_ccref (unp_in ce vars) (ST.cc_compose (unp_in ce1 vars1) (unp_in ce2 vars2)).
  Proof.
    apply st_normalize_fsim. constructor.
    eapply ST.Forward_simulation with
      (ltof _ (fun (_: unit) => 0)) (fun se _ _ wa wb _ => unp_in_ms se wa wb)
      (fun wa wb => unp_in_inv wa wb); try easy.
    - intros. cbn in *. eprod_crush. inv H. constructor; eauto.
    - cbn. intros se Hse. constructor.
      apply disjoint_init_mem; eauto.
    - intros sa wb se1 se2 Hse0 Hsk I. inv I.
      cbn in *. eprod_crush. subst. constructor.
      + intros q1 q2 s1 sb1 Hb Hq Hx Hse.
        cbn in *. eprod_crush.
        exists tt, (st_q q2). inv Hx. inv Hq.
        split. constructor.
        eexists (_, _), _. repeat split; eauto.
        constructor; eauto.
        constructor; eauto.
      + intros sa1 sb1 [] s1 s2 r1 HS HF.
        cbn in *. eprod_crush. inv HF. inv HS.
        eexists. split. econstructor.
        eexists (_, _). split. reflexivity.
        split. 2: constructor; eauto.
        inv MR. constructor; eauto.
      + intros sa sb1 [ ] s1 s2 q1 HS HE.
        cbn in *. eprod_crush.
        inv HE. inv HS. inv MQ.
        eexists. split. constructor.
        eexists (_, _, (_, _)), (_, (_, _, (_, _))).
        split. reflexivity.
        split. reflexivity.
        split. 2: split.
        * apply join_commutative in MJ.
          edestruct join_associative_exist as (mx & A & B).
          apply MJ. apply MJOIN.
          eexists. split; constructor; eauto.
        * split; easy.
        * intros r1 r2 s1' sa1 HA HR HE.
          cbn in *. eprod_crush. inv HE. inv H. inv H3.
          eexists tt, _. split. constructor.
          apply join_commutative in MJOIN0.
          apply join_commutative in MJOIN1.
          edestruct join_associative_exist as (mx & A & B).
          apply MJOIN0. apply MJOIN1.
          eexists (_, _, (_, _)), (_, mx).
          repeat split. constructor; eauto.
          constructor; eauto. apply join_commutative. eauto.
      + easy.
  Qed.

End UNP_IN.

Section UNP_OUT.

  Inductive unp_out_ms: ST.ccworld (ST.cc_compose unp_out unp_out) -> @state li_c li_c 1 -> @state li_c li_c 1 -> Prop :=
  | unp_out_query:
    forall q1 q2 m1 m2 m se,
      ST.match_query unp_out m q1 q2 ->
      join m1 m2 m ->
      unp_out_ms (se, (m1, m2))  (st_q q1) (st_q q2)
  | unp_out_reply:
    forall r1 r2 m1 m2 m se,
      ST.match_reply unp_out m r1 r2 ->
      join m1 m2 m ->
      unp_out_ms (se, (m1, m2)) (st_r r1) (st_r r2).

  Lemma unp_out_idemp:
    st_ccref (ST.cc_compose unp_out unp_out) unp_out.
  Proof.
    apply st_normalize_fsim. constructor.
    eapply ST.Forward_simulation with
      (ltof _ (fun (_: unit) => 0)) (fun _ _ w _ _ _ => unp_out_ms w)
      (fun sa sb => True); try easy.
    - intros sa sb se1 se2 Hse0 Hsk I. inv I. constructor.
      + intros q1 q2 s1 sb1 Hb Hq Hx Hse. exists tt, (st_q q2).
        cbn in *. eprod_crush. subst.
        inv Hx. inv H5. inv H6.
        split. constructor.
        exists tt, (tt, tt). repeat split; eauto.
        apply join_commutative in MJOIN.
        apply join_commutative in MJOIN0.
        edestruct join_associative_exist as (mx & X & Y).
        apply MJOIN. apply MJOIN0.
        econstructor; eauto. econstructor. apply join_commutative; eauto.
      + intros [] [] [] s1 s2 r1 HS HF. inv HF. inv HS.
        eexists. split. econstructor.
        eexists (tt, tt). split; eauto. split; constructor.
        split; eauto. cbn. inv H0.
        apply join_commutative in H2.
        edestruct join_associative_exist as (mx & A & B).
        apply H2. apply MJOIN.
        eexists. split; econstructor; eauto.
      + intros [] [] [] s1 s2 q1 HS HE.
        inv HE. inv HS. inv H0.
        eexists. split. constructor.
        exists tt, m. split. reflexivity. split. reflexivity.
        split. constructor. apply MJOIN.
        split. inv Hse0. inv H. inv H0. constructor.
        intros r1 r2 s1' [] [] HR HE. inv HE. inv HR. cbn in *.
        eexists tt, _. split. constructor.
        eexists tt, (tt, tt).
        repeat split. econstructor; eauto.
        constructor; eauto.
      + easy.
  Qed.

End UNP_OUT.

Section CLIGHT_IN.

  Context (p: Clight.program) (vars: list (ident * val)) (ce: composite_env).

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

  Inductive clight_ms se:
    ST.ccstate (unp_in ce vars) ->
    ST.ccstate (ST.callconv_lift (unp_in ce vars) unit unit) ->
    state (Clight.semantics2 p) -> state (Clight.semantics2 p) -> Prop :=
  | clight_ms_State:
    forall f s k e le m1 m2 mx
      (MJ: join mx m1 m2),
      clight_ms se (se, mx) ((se, mx), (tt, tt))
        (Clight.State f s k e le m1) (Clight.State f s k e le m2)
  | clight_ms_Callstate:
    forall vf args k m1 m2 mx
      (MJ: join mx m1 m2),
      clight_ms se (se, mx) ((se, mx), (tt, tt))
        (Clight.Callstate vf args k m1) (Clight.Callstate vf args k m2)
  | clight_ms_Returnstate:
    forall rv k m1 m2 mx
      (MJ: join mx m1 m2),
      clight_ms se (se, mx) ((se, mx), (tt, tt))
        (Clight.Returnstate rv k m1) (Clight.Returnstate rv k m2).

  Inductive clight_inv : ST.ccstate (unp_in ce vars) -> ST.ccstate (ST.callconv_lift (unp_in ce vars) unit unit) -> Prop :=
  | clight_inv_intro m se:
    clight_inv (se, m) ((se, m), (tt, tt)).

  Lemma clight_in_step se wa wb ge:
    forall s1 t s1',
    Clight.step2 ge s1 t s1' ->
    forall s2, clight_ms se wa wb s1 s2 ->
    exists s2', Clight.step2 ge s2 t s2' /\
    clight_ms se wa wb s1' s2'.
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

  Lemma clight_in: E.forward_simulation (unp_in ce vars) (unp_in ce vars)
                     (semantics_embed (Clight.semantics2 p))
                     (semantics_embed (Clight.semantics2 p)).
  Proof.
    apply st_normalize_fsim. cbn. constructor.
    eapply ST.Forward_simulation with
      (ltof _ (fun (_: unit) => 0)) (fun se _ _ sa sb _ => clight_ms se sa sb)
      (fun sa sb => clight_inv sa sb); try easy.
    intros. inv H. cbn in *. eprod_crush. constructor.
    intros sa wb se1 se2 Hse0 Hsk INV. cbn in *. eprod_crush.
    inv INV. constructor; cbn.
    - intros [q1 []] [q2 []] s1 [m1 [[] []]] HW HQ HX Hse.
      eprod_crush. inv HX. inv H3.
      eexists tt, _. split.
      econstructor; eauto.
      apply mjoin_nextblock in MJOIN.
      rewrite MJOIN. unfold Ple in *.
      etransitivity; eauto.
      apply Pos.le_max_r.
      eexists (_, m0), ((_, m0), (tt, tt)). split. reflexivity.
      split. reflexivity.
      constructor; eauto.
    - intros sa [sb [[] []]] [] s1 s2 [r1 []] HS HX.
      destruct HX as (rx & HX & HY). inv HX. inv HY. inv HS.
      eexists (_, tt). split. eexists. split; constructor.
      eexists (_, _, (tt, tt)). split. reflexivity.
      split. constructor; constructor; eauto.
      constructor.
    - intros sa [sb [[] []]] [] s1 s2 q1 HS HX.
      inv HX. unfold id in H1. subst. inv HS.
      eexists. split. econstructor. eauto.
      eexists (_, _), (_, _).
      split. reflexivity. split. reflexivity.
      split. constructor; eauto. split; eauto.
      intros r1 r2 s1' sa1 [] HR HX.
      eprod_crush. unfold id in *. inv HR. inv H2.
      eexists tt, _. split. eexists. split; constructor.
      eexists (_, _), (_, m1, (tt, tt)). split. reflexivity.
      split. repeat split; eauto.
      econstructor; eauto.
    - intros s1 t s1' HX wa [wb [[] []]] [] s2 HS.
      exploit clight_in_step; eauto.
      intros (s2' & HY & HZ).
      eexists tt, s2'. split.
      left. apply plus_one. apply HY.
      eexists _, (_, (tt, tt)). repeat constructor; eauto.
  Qed.

End CLIGHT_IN.

Section CLICHTP_OUT.

  Context (p: ClightP.program).
  Let ce := ClightP.prog_comp_env p.

  Inductive clightp_ms mx : state (ClightP.clightp1 p) -> state (ClightP.clightp1 p) -> Prop :=
  | clightp_ms_State:
    forall f s k e le m1 m2 pe,
      join mx m1 m2 ->
      clightp_ms mx (ClightP.State f s k e le m1, pe) (ClightP.State f s k e le m2, pe)
  | clightp_ms_Callstate:
    forall vf args k m1 m2 pe,
      join mx m1 m2 ->
      clightp_ms mx (ClightP.Callstate vf args k m1, pe) (ClightP.Callstate vf args k m2, pe)
  | clightp_ms_Returnstate:
    forall rv k m1 m2 pe,
      join mx m1 m2 ->
      clightp_ms mx (ClightP.Returnstate rv k m1, pe) (ClightP.Returnstate rv k m2, pe).

  Lemma clightp_expr_lvalue_loc_join mx ge:
    forall e le m1 m2 pe,
      join mx m1 m2 ->
      (forall expr v,
          ClightP.eval_expr ce ge e le pe m1 expr v ->
          ClightP.eval_expr ce ge e le pe m2 expr v)
      /\
      (forall expr b ofs bf,
         ClightP.eval_lvalue ce ge e le pe m1 expr b ofs bf ->
         ClightP.eval_lvalue ce ge e le pe m2 expr b ofs bf)
      /\
      (forall expr id l,
        ClightP.eval_loc ce ge e le pe m1 expr id l ->
        ClightP.eval_loc ce ge e le pe m2 expr id l ).
  Proof.
    intros e le m1 m2 pe HM.
    apply ClightP.eval_expr_lvalue_loc_ind;
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

  Lemma clightp_expr_join mx ge:
    forall e le m1 m2 pe expr v,
      join mx m1 m2 ->
      ClightP.eval_expr ce ge e le pe m1 expr v ->
      ClightP.eval_expr ce ge e le pe m2 expr v.
  Proof.
    intros. eapply clightp_expr_lvalue_loc_join in H.
    destruct H. apply H; eauto.
  Qed.

  Lemma clightp_lvalue_join mx ge:
    forall e le m1 m2 pe expr b ofs bf,
      join mx m1 m2 ->
      ClightP.eval_lvalue ce ge e le pe m1 expr b ofs bf ->
      ClightP.eval_lvalue ce ge e le pe m2 expr b ofs bf.
  Proof.
    intros. eapply clightp_expr_lvalue_loc_join in H.
    destruct H as (A & B & C). apply B; eauto.
  Qed.

  Lemma clightp_loc_join mx ge:
    forall e le m1 m2 pe expr id l,
      join mx m1 m2 ->
      ClightP.eval_loc ce ge e le pe m1 expr id l ->
      ClightP.eval_loc ce ge e le pe m2 expr id l.
  Proof.
    intros. eapply clightp_expr_lvalue_loc_join in H.
    destruct H as (A & B & C). apply C; eauto.
  Qed.

  Lemma clightp_exprlist_join mx ge:
    forall e le m1 m2 pe al tyargs vargs,
      join mx m1 m2 ->
      ClightP.eval_exprlist ce ge e le pe m1 al tyargs vargs ->
      ClightP.eval_exprlist ce ge e le pe m2 al tyargs vargs.
  Proof.
    intros * HM HX. induction HX; cbn.
    - constructor.
    - exploit clightp_expr_join; eauto. intros A.
      exploit sem_cast_join; eauto. rewrite H0.
      intros B. inv B.
      econstructor; eauto.
  Qed.

  Lemma clightp_alloc_variables_join m:
    Monotonic
      (@ClightP.alloc_variables)
      (- ==> - ==> join m ++> - ==> - ==> set_le (join m)).
  Proof.
    repeat rstep. intros ? ?. revert y H.
    induction H0.
    - intros. eexists. split. econstructor. eauto.
    - intros.
      Existing Instance alloc_join. transport H.
      eprod_crush.
      exploit IHalloc_variables. eauto.
      intros (? & ? & ?).
      eexists. split; eauto. econstructor; eauto.
  Qed.

  Lemma clightp_function_entry_join mx ge:
    forall f vargs m1 m2 m1' e le,
      join mx m1 m2 ->
      ClightP.function_entry2 ge f vargs m1 e le m1' ->
      exists m2', ClightP.function_entry2 ge f vargs m2 e le m2'
             /\ join mx m1' m2'.
  Proof.
    intros * HM HX. inv HX.
    exploit clightp_alloc_variables_join; eauto. intros (? & A & B).
    eexists. split; eauto. econstructor; eauto.
    destruct HM. inv mjoin_alloc_flag; congruence.
  Qed.

  Lemma clightp_out_step mx ge:
    forall s1 t s1',
      ClightP.step2 ce ge s1 t s1' ->
      forall s2, clightp_ms mx s1 s2 ->
      exists s2', ClightP.step2 ce ge s2 t s2' /\
      clightp_ms mx s1' s2'.
  Proof with (eexists (_, _); split; econstructor; eauto).
    induction 1; intros S2 MS; inv MS;
      try solve [ eexists (_, _); split; econstructor; eauto ].
    - exploit clightp_lvalue_join; eauto. intros A.
      exploit clightp_expr_join; eauto. intros B.
      exploit sem_cast_join; eauto.
      rewrite H1. intros C. inv C.
      exploit assign_loc_join; eauto. intros (? & D & E)...
    - exploit clightp_expr_join; eauto. intros A...
    - exploit clightp_loc_join; eauto. intros A.
      exploit clightp_expr_join; eauto. intros B...
    - exploit clightp_expr_join; eauto. intros A.
      exploit clightp_exprlist_join; eauto; intros B...
    - exploit clightp_exprlist_join; eauto. intros A.
      exploit ClightP.external_call_join; eauto. intros (? & B & C)...
    - exploit clightp_expr_join; eauto. intros A.
      exploit bool_val_join; eauto.
      rewrite H0. intros B. inv B...
    - exploit free_list_join; eauto.
      rewrite H. intros A. inv A...
    - exploit clightp_expr_join; eauto. intros A.
      exploit sem_cast_join; eauto.
      rewrite H0. intros B. inv B.
      exploit free_list_join; eauto.
      rewrite H1. intros C. inv C...
    - exploit free_list_join; eauto.
      rewrite H0. intros A. inv A...
    - exploit clightp_expr_join; eauto. intros A...
    - exploit clightp_function_entry_join; eauto. intros (? & A & B)...
    - exploit ClightP.external_call_join; eauto. intros (? & A & B)...
  Qed.

  Lemma clightp_out: forward_simulation pout unp_penv'
                       (ClightP.clightp2 p) (ClightP.clightp2 p).
  Proof.
    constructor. econstructor; eauto.
    { intros i. reflexivity. }
    instantiate (1 := fun _ _ _ => _). cbn beta.
    intros se1 se2 w Hse Hse1. cbn -[ClightP.clightp1] in *. subst se2.
    rename w into mx.
    apply forward_simulation_step with (match_states := clightp_ms mx); cbn.
    - intros [q1 pe1] [q2 pe2] [s1 pe1'] HQ HX.
      inv HQ. inv HX. eexists (_, _). split.
      + econstructor; eauto.
        apply mjoin_nextblock in MJOIN.
        rewrite MJOIN.
        unfold Ple in *.
        etransitivity; eauto.
        apply Pos.le_max_r.
      + constructor. eauto.
    - intros [s1 pe1] [s2 pe2] [r1 pe1'] HS HX.
      inv HX. inv HS. eexists (_, _). split.
      + econstructor.
      + constructor. eauto.
    - intros [s1 pe1] [s2 pe2] q1 HS HX.
      inv HX. inv HS.
      eexists mx, _.
      split. econstructor; eauto.
      split. constructor. eauto.
      split. eauto.
      intros r1 r2 [s1' pe1'] HR HX.
      inv HX. inv HR.
      eexists (_, _).
      split. constructor.
      constructor. eauto.
    - intros. eapply clightp_out_step; eauto.
    - apply well_founded_ltof.
  Qed.

  Let sk := ClightP.clightp_erase_program p.

  Inductive penv_ms (vars: list (ident * val)):
    ST.ccworld (@ST.callconv_lift _ _ unp_out penv (penv_pset vars) penv (penv_pset vars)) ->
    @state (li_c@penv) (li_c@penv) (id_semantics sk) ->
    @state (li_c@penv) (li_c@penv) (id_semantics sk) -> Prop :=
  | penv_ms_query:
    forall q1 q2 m pe0 pe,
      ST.match_query unp_out m q1 q2 ->
      penv_ms vars (m, (pe0, pe0))
        (@st_q (li_c@penv) (q1, pe))
        (@st_q (li_c@penv) (q2, pe))
  | penv_ms_reply:
    forall r1 r2 m pe0 pe,
      ST.match_reply unp_out m r1 r2 ->
      penv_ms vars (m, (pe0, pe0))
        (@st_r (li_c@penv) (r1, pe))
        (@st_r (li_c@penv) (r2, pe)).

  Lemma encap_prim_out vars:
    E.forward_simulation unp_penv unp_out
      (@encap_prim _ penv (penv_pset vars) sk)
      (@encap_prim _ penv (penv_pset vars) sk).
  Proof.
    apply st_normalize_fsim. cbn. constructor.
    eapply ST.Forward_simulation with
      (ltof _ (fun (_: unit) => 0)) (fun _ _ w _ _ _ => penv_ms vars w)
      (fun _ '(_, (pe1, pe2)) => pe1 = pe2); try easy.
    intros. cbn in *. eprod_crush. easy.
    intros. cbn in *. eprod_crush. constructor; cbn.
    - intros. eprod_crush. subst. inv H2. inv H1.
      eexists tt, _. split. constructor.
      eexists tt, (tt, (_, _)). split; eauto.
      split. repeat constructor.
      econstructor. econstructor; eauto.
    - intros. eprod_crush. inv H. inv H1. inv H1. inv H7.
      eexists (_, _). split. constructor.
      eexists (tt, (_, _)). split. repeat constructor.
      split. split. constructor. eauto.
      split; eauto. constructor.
    - intros. eprod_crush. inv H1. inv H. inv H7.
      eexists (_, _). split. constructor.
      eexists tt, _. split; eauto. split; eauto.
      split. econstructor; eauto. split; eauto.
      intros. eprod_crush. inv H1. inv H2.
      eexists tt, _. split. constructor.
      eexists tt, (tt, (_, _)). split; eauto.
      split. repeat constructor.
      econstructor. constructor. eauto.
    - easy.
      Unshelve. all: eauto.
  Qed.

  Lemma eclightp_out: E.forward_simulation unp_out unp_out
                        (eclightp p) (eclightp p).
  Proof.
    unfold eclightp.
    eapply encap_fsim_lcomp_sk; eauto.
    instantiate (1 := unp_penv).
    - apply encap_prim_out.
    - apply encap_fsim_embed.
      apply clightp_out.
    - apply Linking.linkorder_refl.
    - apply Linking.linkorder_refl.
  Qed.

End CLICHTP_OUT.

Section COMP.

  Context (S1: li_c +-> li_c) (S2: li_c +-> li_c)
    (T1: li_c +-> li_c) (T2: li_c +-> li_c)
    (vars1 vars2: list (ident * val))
    (Hvs: PEnv.vars_disjoint vars1 vars2)
    (ce1 ce2 ce: composite_env)
    (Hvs1: vars_type_ok ce1 vars1)
    (Hvs2: vars_type_ok ce2 vars2)
    (Hce1: forall id co, ce1 ! id = Some co -> ce ! id = Some co)
    (Hce2: forall id co, ce2 ! id = Some co -> ce ! id = Some co)
    (H1: E.forward_simulation unp_out (unp_in ce1 vars1) S1 T1)
    (H2: E.forward_simulation unp_out (unp_in ce2 vars2) S2 T2).
  Context (sk: AST.program unit unit)
    (Hsk1: Linking.linkorder (skel S1) sk)
    (Hsk2: Linking.linkorder (skel S2) sk).

  Hypothesis P1: E.forward_simulation (unp_in ce2 vars2) (unp_in ce2 vars2) T1 T1.
  Hypothesis P2: E.forward_simulation unp_out unp_out S2 S2.

  Let vars := vars1 ++ vars2.

  Theorem clightp_comp':
    E.forward_simulation unp_out (unp_in ce vars)
      (comp_esem' S1 S2 sk) (comp_esem' T1 T2 sk).
  Proof.
    rewrite <- unp_out_idemp. unfold vars.
    rewrite unp_in_idemp. 5-6: eauto. 2-4: eauto.
    eapply encap_fsim_lcomp_sk; eauto.
    instantiate (1 := (ST.cc_compose unp_out (unp_in ce2 vars2))).
    - eapply encap_fsim_vcomp; eauto.
    - eapply encap_fsim_vcomp; eauto.
  Qed.

End COMP.

Require Import ClightPLink.

Section COMP.

  Context p1 p2 tp1 tp2 (HT1: transl_program p1 = OK tp1)
    (HT2: transl_program p2 = OK tp2)
    (Hvs: PEnv.vars_disjoint (vars_of_program p1) (vars_of_program p2)).
  Let S1 := eclightp p1.
  Let S2 := eclightp p2.
  Let T1 := semantics_embed (Clight.semantics2 tp1).
  Let T2 := semantics_embed (Clight.semantics2 tp2).
  Let sk1 := ClightP.clightp_erase_program p1.
  Let sk2 := ClightP.clightp_erase_program p2.
  Let vars := vars_of_program p1 ++ vars_of_program p2.
  Context p (Hp: Linking.link p1 p2 = Some p).
  Let sk := ClightP.clightp_erase_program p.
  Let ce := ClightP.prog_comp_env p.

  Theorem clightp_comp:
    E.forward_simulation unp_out (unp_in ce vars)
      (comp_esem' S1 S2 sk) (comp_esem' T1 T2 sk).
  Proof.
    eapply clightp_comp' with
      (ce1:=(ClightP.prog_comp_env p1))
      (ce2:=(ClightP.prog_comp_env p2)).
    - eauto.
    - generalize (ClightP.prog_priv_ok p1).
      intros H i x Hi.
      unfold vars_of_program, init_of_pvars in Hi.
      apply in_map_iff in Hi as ((i' & x') & Hi' & Hx'). inv Hi'.
      specialize (H _ _ Hx'). apply H.
    - generalize (ClightP.prog_priv_ok p2).
      intros H i x Hi.
      unfold vars_of_program, init_of_pvars in Hi.
      apply in_map_iff in Hi as ((i' & x') & Hi' & Hx'). inv Hi'.
      specialize (H _ _ Hx'). apply H.
    - apply Linking.link_linkorder in Hp as [Hp1 Hp2].
      destruct Hp1 as (A & B & C). apply B.
    - apply Linking.link_linkorder in Hp as [Hp1 Hp2].
      destruct Hp2 as (A & B & C). apply B.
    - apply promote_clightp; eauto.
    - apply promote_clightp; eauto.
    - apply link_clightp_erase in Hp.
      apply Linking.link_linkorder in Hp. apply Hp.
    - apply link_clightp_erase in Hp.
      apply Linking.link_linkorder in Hp. apply Hp.
    - eapply clight_in.
    - apply eclightp_out.
  Qed.

End COMP.
