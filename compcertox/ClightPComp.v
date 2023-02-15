From compcert Require Import
     AST Coqlib Maps Values Integers Errors Events
     LanguageInterface Smallstep Globalenvs Memory Floats.
From compcert Require Import
     CategoricalComp.
From compcertox Require Import
     TensorComp Lifting
     ClightP Encapsulation.
From compcert Require Import Join.
Require Import Lia.

Generalizable All Variables.

(** ------------------------------------------------------------------------- *)
(** simulation conventions *)

(** The simulation conventions, however, that we actually use *)

(* TODO: define initial states and prove the properties*)
Variable m0 : list (ident * Z) -> Genv.symtbl -> mem.
Variable p0 : list (ident * Z) -> ClightP.penv.

Hypothesis id_skel_least: forall sk, Linking.linkorder CategoricalComp.id_skel sk.
Variable vars_of_program : ClightP.program -> list (ident * Z).
Hypothesis vars_init :
  forall p se, ClightP.penv_mem_match
            p.(ClightP.prog_comp_env) se
                (p0 (vars_of_program p))
                (m0 (vars_of_program p) se).

Variable exclusive_vars: list (ident * Z) -> list (ident * Z) -> Prop.
Hypothesis exclusive_init_mem:
  forall se vars1 vars2,
    exclusive_vars vars1 vars2 ->
    join (m0 vars1 se) (m0 vars2 se) (m0 (vars1 ++ vars2) se).

Instance mem_pset (vars: list (ident * Z)) : PSet mem :=
  { pset_init se := m0 vars se }.
Instance penv_pset (vars: list (ident * Z)) : PSet ClightP.penv :=
  { pset_init _ := p0 vars }.
Instance symtbl_pset : PSet Genv.symtbl :=
  { pset_init se := se }.

Instance mem_world (vars: list (ident * Z)): World mem :=
  {|
    w_state := mem;
    w_pset := mem_pset vars;
    (* maybe we need unchanged_on *)
    w_int_step := {| rel := fun m1 m2 => True |};
    w_ext_step := {| rel := eq |};
  |}.

Instance se_world : World Genv.symtbl :=
  {|
    w_state := Genv.symtbl;
    w_pset := symtbl_pset;
    w_int_step := {| rel := eq |};
    w_ext_step := {| rel := eq |};
  |}.

(*
Inductive unp_out_query: Memory.mem -> query li_c -> query li_c -> Prop :=
| unp_out_query_intro vf sg vargs m msrc mtgt
    (MJOIN: join m msrc mtgt):
  unp_out_query m (cq vf sg vargs msrc) (cq vf sg vargs mtgt).

Inductive unp_out_reply: Memory.mem -> reply li_c -> reply li_c -> Prop :=
| unp_out_reply_intro rv m msrc mtgt
    (MJOIN: join m msrc mtgt):
  unp_out_reply m (cr rv msrc) (cr rv mtgt).

Program Definition unp_out (vars: list (ident * Z)): ST.callconv li_c li_c :=
  {|
    ST.ccworld := Memory.mem;
    ST.ccworld_world := mem_world vars;
    ST.match_senv _ se1 se2 := se1 = se2;
    ST.match_query := pout_query;
    ST.match_reply := pout_reply;
  |}.
Next Obligation. reflexivity. Qed.
Next Obligation. inv H0. reflexivity. Qed.
Next Obligation. inv H. reflexivity. Qed.
*)

Definition unp_out: ST.callconv li_c li_c := &pout.

(* TODO: define [join_query] and [join_reply] *)
Inductive unp_penv_query: Memory.mem -> query (li_c@ClightP.penv) -> query (li_c@ClightP.penv) -> Prop :=
| unp_penv_query_intro vf sg vargs m msrc mtgt pe
    (MJOIN: join m msrc mtgt):
  unp_penv_query m (cq vf sg vargs msrc, pe) (cq vf sg vargs mtgt, pe).

Inductive unp_penv_reply: Memory.mem -> reply (li_c@ClightP.penv) -> reply (li_c@ClightP.penv) -> Prop :=
| unp_penv_reply_intro rv m msrc mtgt pe
    (MJOIN: join m msrc mtgt):
  unp_penv_reply m (cr rv msrc, pe) (cr rv mtgt, pe).

Program Definition unp_penv' : callconv (li_c@ClightP.penv) (li_c@ClightP.penv) :=
  {|
    ccworld := Memory.mem;
    match_senv _ se1 se2 := se1 = se2;
    match_query := unp_penv_query;
    match_reply := unp_penv_reply;
  |}.
Next Obligation. reflexivity. Qed.
Next Obligation. inv H0. reflexivity. Qed.
Next Obligation. inv H. reflexivity. Qed.

Definition unp_penv: ST.callconv (li_c@ClightP.penv) (li_c@ClightP.penv)
  := &unp_penv'.

Inductive unp_in_query: Memory.mem -> query li_c -> query li_c -> Prop :=
| unp_in_query_intro vf sg vargs m msrc mtgt
    (MJOIN: join m msrc mtgt):
  unp_in_query m (cq vf sg vargs msrc) (cq vf sg vargs mtgt).

Inductive unp_in_reply: Memory.mem -> reply li_c -> reply li_c -> Prop :=
| unp_in_reply_intro rv m msrc mtgt
    (MJOIN: join m msrc mtgt):
  unp_in_reply m (cr rv msrc) (cr rv mtgt).

Program Definition unp_in vars : ST.callconv li_c li_c :=
  {|
    ST.ccworld := Genv.symtbl * mem;
    ST.ccworld_world := world_prod se_world (mem_world vars);
    ST.match_senv '(se, _) se1 se2 := se = se1 /\ se = se2;
    ST.match_query '(_, m) := unp_in_query m;
    ST.match_reply '(_, m) := unp_in_reply m;
  |}.
Next Obligation. reflexivity. Qed.
Next Obligation. inv H0. reflexivity. Qed.
Next Obligation. inv H. reflexivity. Qed.

Definition encap_prim (U: Type) `{PSet U} : li_c@U +-> li_c :=
  {|
    pstate := U;
    esem := 1%lts;
  |}.

Definition eclightp (p: ClightP.program) :=
  comp_esem'
    (@encap_prim ClightP.penv (penv_pset (vars_of_program p)))
    (semantics_embed (ClightP.clightp2 p))
    (ClightP.clightp_erase_program p).


(** ------------------------------------------------------------------------- *)
(** promote the result from [ClightP.v] to encapsulation version *)
Section ESIM.

  Context prog tprog (HT: transl_program prog = OK tprog).
  Let S := eclightp prog.
  Let T := semantics_embed (Clight.semantics2 tprog).
  Let vars := vars_of_program prog.
  Let ce := prog.(ClightP.prog_comp_env).
  Let sk := ClightP.clightp_erase_program prog.

  Inductive encap_ms se : mem -> ClightP.penv -> @state (li_c@ClightP.penv) (li_c@ClightP.penv) 1 -> @state li_c li_c 1 -> Prop :=
  | encap_ms_q m pe vf sg vargs msrc mtgt
      (MJOIN: join m msrc mtgt)
      (HPE: ClightP.penv_mem_match ce se pe m):
    encap_ms se m pe (@st_q (li_c@ClightP.penv) ((cq vf sg vargs msrc), pe)) (st_q (cq vf sg vargs mtgt))
  | encap_ms_r m pe rv msrc mtgt
      (MJOIN: join m msrc mtgt)
      (HPE: ClightP.penv_mem_match ce se pe m):
    encap_ms se m pe (@st_r (li_c@ClightP.penv) ((cr rv msrc), pe)) (st_r (cr rv mtgt)).

  Lemma penv_encap:
    E.forward_simulation
     (& (pin ce)) (unp_in vars)
     (@encap_prim ClightP.penv (penv_pset vars))
     (semantics_embed 1%lts).
  Proof.
    apply st_normalize_fsim. constructor.
    eapply ST.Forward_simulation with
      (ltof _ (fun (_: unit) => 0))
      (fun se0 _ _ _ '((se, m), (pe, _)) _ s1 s2 =>
         encap_ms se m pe s1 s2 /\ se0 = se)
      (fun _ '((se, m), (pe, _)) => ClightP.penv_mem_match ce se pe m);
      try easy.
    - intros. cbn in *. eprod_crush. eauto.
    - intros. cbn in *. apply vars_init.
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
    E.forward_simulation unp_out (unp_in vars) S T.
  Proof.
    rewrite <- (ccref_right_unit2 unp_out).
    rewrite (ccref_right_unit1 (unp_in vars)).
    eapply encap_fsim_vcomp.
    instantiate (1 := (comp_esem' (semantics_embed 1%lts) T sk)).
    - eapply encap_fsim_lcomp_sk.
      instantiate (1 := &(pin ce)).
      + apply penv_encap.
      + apply encap_fsim_embed.
        apply transl_program_correct. eauto.
      + apply id_skel_least.
      + apply Linking.linkorder_refl.
    - rewrite ccref_left_unit1 at 2.
      rewrite <- ccref_left_unit2 at 1.
      eapply encap_fsim_vcomp; eauto.
      instantiate (1 := semantics_embed _).
      2: { apply encap_fsim_embed_cat; apply CAT.left_unit_2. }
      assert (skel (Clight.semantics2 tprog) = sk).
      {
        apply transl_program_correct in HT as [X].
        symmetry. apply X.
      }
      unfold left_comp_id.
      rewrite H.
      apply encap_comp_embed.
  Qed.

End ESIM.

(** ------------------------------------------------------------------------- *)
(** Properties *)

Lemma join_associative_exist m1 m2 m3 m12 m123:
  join m1 m2 m12 -> join m12 m3 m123 ->
  exists m23, join m2 m3 m23 /\ join m1 m23 m123.
Admitted.

Section UNP_IN.

  Context (vars1 vars2: list (ident * Z)) (Hvs: exclusive_vars vars1 vars2).
  Let vars := vars1 ++ vars2.
  Inductive unp_in_inv:
    ST.ccstate (ST.cc_compose (unp_in vars1) (unp_in vars2)) ->
    ST.ccstate (unp_in vars) -> Prop :=
  | unp_in_inv_intro:
    forall m m1 m2 se, join m1 m2 m -> unp_in_inv ((se, m1), (se, m2)) (se, m).
  Inductive unp_in_ms se:
    ST.ccstate (ST.cc_compose (unp_in vars1) (unp_in vars2)) ->
    ST.ccstate (unp_in vars) -> @state li_c li_c 1 -> @state li_c li_c 1 -> Prop :=
  | unp_in_ms_query:
    forall q1 q2 m1 m2 m
      (MQ: ST.match_query (unp_in vars) (se, m) q1 q2)
      (MJ: join m1 m2 m),
      unp_in_ms se ((se, m1), (se, m2)) (se, m) (st_q q1) (st_q q2)
  | unp_in_ms_reply:
    forall r1 r2 m1 m2 m
      (MR: ST.match_reply (unp_in vars) (se, m) r1 r2)
      (MJ: join m1 m2 m),
      unp_in_ms se ((se, m1), (se, m2)) (se, m) (st_r r1) (st_r r2).

  Lemma unp_in_idemp:
    st_ccref (unp_in vars) (ST.cc_compose (unp_in vars1) (unp_in vars2)).
  Proof.
    apply st_normalize_fsim. constructor.
    eapply ST.Forward_simulation with
      (ltof _ (fun (_: unit) => 0)) (fun se _ _ wa wb _ => unp_in_ms se wa wb)
      (fun wa wb => unp_in_inv wa wb); try easy.
    - intros. cbn in *. eprod_crush. inv H. constructor; eauto.
    - cbn. intros se. constructor.
      apply exclusive_init_mem; eauto.
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

  Context (p: Clight.program) (vars: list (ident * Z)).

  Lemma clight_expr_lvalue_join mx ge:
    forall e le m1 m2,
      join mx m1 m2 ->
      (forall expr v,
          Clight.eval_expr ge e le m1 expr v ->
          Clight.eval_expr ge e le m2 expr v)
      /\
      (forall expr b ofs,
         Clight.eval_lvalue ge e le m1 expr b ofs ->
         Clight.eval_lvalue ge e le m2 expr b ofs).
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
    forall e le m1 m2 expr b ofs,
      join mx m1 m2 ->
      Clight.eval_lvalue ge e le m1 expr b ofs ->
      Clight.eval_lvalue ge e le m2 expr b ofs.
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

  Inductive clight_ms se:
    ST.ccstate (unp_in vars) ->
    ST.ccstate (ST.callconv_lift (unp_in vars) unit unit) ->
    state (Clight.semantics1 p) -> state (Clight.semantics1 p) -> Prop :=
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

  Inductive clight_inv : ST.ccstate (unp_in vars) -> ST.ccstate (ST.callconv_lift (unp_in vars) unit unit) -> Prop :=
  | clight_inv_intro m se:
    clight_inv (se, m) ((se, m), (tt, tt)).

  Lemma clight_in_step se wa wb ge:
    forall s1 t s1',
    Clight.step1 ge s1 t s1' ->
    forall s2, clight_ms se wa wb s1 s2 ->
    exists s2', Clight.step1 ge s2 t s2' /\
    clight_ms se wa wb s1' s2'.
  Proof.
    induction 1; intros S1 HS; inv HS;
      try solve [ eexists _; split; econstructor; eauto ].
    - exploit clight_lvalue_join; eauto. intros A.
      exploit clight_expr_join; eauto. intros B.
      exploit sem_cast_join; eauto.
      rewrite H1. intros C. inv C.
      exploit assign_loc_join; eauto. intros (? & D & E).
      eexists _. split; econstructor; eauto.
    - exploit clight_expr_join; eauto. intros A.
      eexists _. split; econstructor; eauto.
    - exploit clight_expr_join; eauto. intros A.
      exploit clight_exprlist_join; eauto; intros B.
      eexists _. split; econstructor; eauto.
    - admit.
    - exploit clight_expr_join; eauto. intros A.
      exploit bool_val_join; eauto.
      rewrite H0. intros B. inv B.
      eexists _. split; econstructor; eauto.
    - exploit free_list_join; eauto.
      rewrite H. intros A. inv A.
      eexists _. split; econstructor; eauto.
    - exploit clight_expr_join; eauto. intros A.
      exploit sem_cast_join; eauto.
      rewrite H0. intros B. inv B.
      exploit free_list_join; eauto.
      rewrite H1. intros C. inv C.
      eexists _. split; econstructor; eauto.
    - exploit free_list_join; eauto.
      rewrite H0. intros A. inv A.
      eexists _. split; econstructor; eauto.
    - exploit clight_expr_join; eauto. intros A.
      eexists _. split; econstructor; eauto.
    - admit.
    - admit.
  Admitted.

  Lemma clight_in: E.forward_simulation (unp_in vars) (unp_in vars)
                     (semantics_embed (Clight.semantics1 p))
                     (semantics_embed (Clight.semantics1 p)).
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
      eexists (_, m1), ((_, m1), (tt, tt)). split. reflexivity.
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
      eexists (_, _), (_, m2, (tt, tt)). split. reflexivity.
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
          ClightP.eval_expr ge e le pe m1 expr v ->
          ClightP.eval_expr ge e le pe m2 expr v)
      /\
      (forall expr b ofs,
         ClightP.eval_lvalue ge e le pe m1 expr b ofs ->
         ClightP.eval_lvalue ge e le pe m2 expr b ofs)
      /\
      (forall expr id l,
        ClightP.eval_loc ge e le pe m1 expr id l ->
        ClightP.eval_loc ge e le pe m2 expr id l ).
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
      ClightP.eval_expr ge e le pe m1 expr v ->
      ClightP.eval_expr ge e le pe m2 expr v.
  Proof.
    intros. eapply clightp_expr_lvalue_loc_join in H.
    destruct H. apply H; eauto.
  Qed.

  Lemma clightp_lvalue_join mx ge:
    forall e le m1 m2 pe expr b ofs,
      join mx m1 m2 ->
      ClightP.eval_lvalue ge e le pe m1 expr b ofs ->
      ClightP.eval_lvalue ge e le pe m2 expr b ofs.
  Proof.
    intros. eapply clightp_expr_lvalue_loc_join in H.
    destruct H as (A & B & C). apply B; eauto.
  Qed.

  Lemma clightp_loc_join mx ge:
    forall e le m1 m2 pe expr id l,
      join mx m1 m2 ->
      ClightP.eval_loc ge e le pe m1 expr id l ->
      ClightP.eval_loc ge e le pe m2 expr id l.
  Proof.
    intros. eapply clightp_expr_lvalue_loc_join in H.
    destruct H as (A & B & C). apply C; eauto.
  Qed.

  Lemma clightp_exprlist_join mx ge:
    forall e le m1 m2 pe al tyargs vargs,
      join mx m1 m2 ->
      ClightP.eval_exprlist ge e le pe m1 al tyargs vargs ->
      ClightP.eval_exprlist ge e le pe m2 al tyargs vargs.
  Proof.
    intros * HM HX. induction HX; cbn.
    - constructor.
    - exploit clightp_expr_join; eauto. intros A.
      exploit sem_cast_join; eauto. rewrite H0.
      intros B. inv B.
      econstructor; eauto.
  Qed.

  Lemma clightp_out_step mx ge:
    forall s1 t s1',
      ClightP.step2 ge s1 t s1' ->
      forall s2, clightp_ms mx s1 s2 ->
      exists s2', ClightP.step2 ge s2 t s2' /\
      clightp_ms mx s1' s2'.
  Proof.
    induction 1; intros S2 MS; inv MS;
      try solve [ eexists (_, _); split; econstructor; eauto ].
    - exploit clightp_lvalue_join; eauto. intros A.
      exploit clightp_expr_join; eauto. intros B.
      exploit sem_cast_join; eauto.
      rewrite H1. intros C. inv C.
      exploit assign_loc_join; eauto. intros (? & D & E).
      eexists (_, _). split; econstructor; eauto.
    - exploit clightp_expr_join; eauto. intros A.
      eexists (_, _). split; econstructor; eauto.
    - exploit clightp_loc_join; eauto. intros A.
      exploit clightp_expr_join; eauto. intros B.
      eexists (_, _). split; econstructor; eauto.
    - exploit clightp_expr_join; eauto. intros A.
      exploit clightp_exprlist_join; eauto; intros B.
      eexists _. split; econstructor; eauto.
    - admit.
    - exploit clightp_expr_join; eauto. intros A.
      exploit bool_val_join; eauto.
      rewrite H0. intros B. inv B.
      eexists (_, _). split; econstructor; eauto.
    - exploit free_list_join; eauto.
      rewrite H. intros A. inv A.
      eexists (_, _). split; econstructor; eauto.
    - exploit clightp_expr_join; eauto. intros A.
      exploit sem_cast_join; eauto.
      rewrite H0. intros B. inv B.
      exploit free_list_join; eauto.
      rewrite H1. intros C. inv C.
      eexists (_, _). split; econstructor; eauto.
    - exploit free_list_join; eauto.
      rewrite H0. intros A. inv A.
      eexists (_, _). split; econstructor; eauto.
    - exploit clightp_expr_join; eauto. intros A.
      eexists (_, _). split; econstructor; eauto.
    - admit.
    - admit.
  Admitted.

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

  Inductive penv_ms (vars: list (ident * Z)):
    ST.ccworld (@ST.callconv_lift _ _ unp_out ClightP.penv (penv_pset vars) ClightP.penv (penv_pset vars)) ->
    @state (li_c@ClightP.penv) (li_c@ClightP.penv) 1%lts ->
    @state (li_c@ClightP.penv) (li_c@ClightP.penv) 1%lts -> Prop :=
  | penv_ms_query:
    forall q1 q2 m pe0 pe,
      ST.match_query unp_out m q1 q2 ->
      penv_ms vars (m, (pe0, pe0))
        (@st_q (li_c@ClightP.penv) (q1, pe))
        (@st_q (li_c@ClightP.penv) (q2, pe))
  | penv_ms_reply:
    forall r1 r2 m pe0 pe,
      ST.match_reply unp_out m r1 r2 ->
      penv_ms vars (m, (pe0, pe0))
        (@st_r (li_c@ClightP.penv) (r1, pe))
        (@st_r (li_c@ClightP.penv) (r2, pe)).

  Lemma encap_prim_out vars:
    E.forward_simulation unp_penv unp_out
      (@encap_prim ClightP.penv (penv_pset vars))
      (@encap_prim ClightP.penv (penv_pset vars)).
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
    - cbn. apply id_skel_least.
    - cbn. apply Linking.linkorder_refl.
  Qed.

End CLICHTP_OUT.

Section COMP.

  Context (S1: li_c +-> li_c) (S2: li_c +-> li_c)
    (T1: li_c +-> li_c) (T2: li_c +-> li_c)
    (vars1 vars2: list (ident * Z))
    (Hvs: exclusive_vars vars1 vars2)
    (H1: E.forward_simulation unp_out (unp_in vars1) S1 T1)
    (H2: E.forward_simulation unp_out (unp_in vars2) S2 T2).
  Context (sk: AST.program unit unit)
    (Hsk1: Linking.linkorder (skel S1) sk)
    (Hsk2: Linking.linkorder (skel S2) sk).

  Hypothesis P1:
    forall vars, E.forward_simulation (unp_in vars) (unp_in vars) T1 T1.
  Hypothesis P2: E.forward_simulation unp_out unp_out S2 S2.

  Let vars := vars1 ++ vars2.

  Theorem clightp_comp:
    E.forward_simulation unp_out (unp_in vars)
      (comp_esem' S1 S2 sk) (comp_esem' T1 T2 sk).
  Proof.
    rewrite <- unp_out_idemp.
    unfold vars. rewrite unp_in_idemp.
    eapply encap_fsim_lcomp_sk; eauto.
    instantiate (1 := (ST.cc_compose unp_out (unp_in vars2))).
    - eapply encap_fsim_vcomp; eauto.
    - eapply encap_fsim_vcomp; eauto.
    - eauto.
  Qed.

End COMP.

(** ------------------------------------------------------------------------- *)
(** simulation conventions in paper *)
(**  *)

Inductive cc_join_query: query li_c * mem -> query li_c -> Prop :=
| jq_intro vf sg args m1 m2 m:
  join m1 m m2 ->
  cc_join_query (cq vf sg args m1, m) (cq vf sg args m2).

Inductive cc_join_reply: reply li_c * mem -> reply li_c -> Prop :=
| jr_intro rv m1 m2 m:
  join m1 m m2 ->
  cc_join_reply (cr rv m1, m) (cr rv m2).

Program Definition cc_join: callconv (li_c@mem) li_c :=
  {|
    ccworld := unit;
    match_senv _ := eq;
    match_query _ := cc_join_query;
    match_reply _ := cc_join_reply;
  |}.
Next Obligation. reflexivity. Qed.
Next Obligation. inv H0. reflexivity. Qed.
Next Obligation. inv H. reflexivity. Qed.

Program Definition cc_keep (U: Type): callconv li_c (li_c@U) :=
  {|
    ccworld := U;
    match_senv _ := eq;
    match_query u1 q1 '(q2, u2) := q1 = q2 /\ u1 = u2;
    match_reply u1 r1 '(r2, u2) := r1 = r2 /\ u1 = u2;
  |}.
Next Obligation. reflexivity. Qed.
Next Obligation. reflexivity. Qed.
Next Obligation. reflexivity. Qed.


(** To strictly follow the paper, we are suppposed to use [cc_out]. But it is
more straightforward to work on [cc_out'] instead. *)
Definition cc_out: ST.callconv li_c li_c := ST.cc_compose &(cc_keep mem) &cc_join.

Program Definition cc_conjoint : ST.callconv li_c (li_c@mem) :=
  {|
    ST.ccworld := mem;
    ST.match_query m1 q1 '(q2, m2) := q1 = q2 /\ m1 = m2;
    ST.match_reply m1 r1 '(r2, m2) := r1 = r2 /\ m1 = m2;
  |}.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.

Definition cc_in: ST.callconv li_c li_c := ST.cc_compose cc_conjoint &cc_join.
