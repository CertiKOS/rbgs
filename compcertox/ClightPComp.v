From compcert Require Import
     AST Coqlib Maps Values Integers Errors Events
     LanguageInterface Smallstep Globalenvs Memory Floats.
From compcert Require Import
     CategoricalComp.
From compcertox Require Import
     TensorComp Lifting
     ClightP Encapsulation.
From compcert Require Import Join.

(** ------------------------------------------------------------------------- *)
(** simulation conventions *)

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

Variable m0 : mem.
Variable p0: ClightP.penv.

Instance mem_pset : PSet mem := { pset_init := m0 }.
Instance penv_pset : PSet ClightP.penv := { pset_init := p0 }.

(** To strictly follow the paper, we are suppposed to use [cc_out]. But it is
more straightforward to work on [cc_out'] instead. *)
Definition cc_out: ST.callconv li_c li_c := ST.cc_compose &(cc_keep mem) &cc_join.
Definition cc_out': ST.callconv li_c li_c := &pout.

Inductive pout_penv_query: Memory.mem -> query (li_c@ClightP.penv) -> query (li_c@ClightP.penv) -> Prop :=
| pout_penv_query_intro vf sg vargs m msrc mtgt pe
    (MJOIN: join m msrc mtgt):
  pout_penv_query m (cq vf sg vargs msrc, pe) (cq vf sg vargs mtgt, pe).

Inductive pout_penv_reply: Memory.mem -> reply (li_c@ClightP.penv) -> reply (li_c@ClightP.penv) -> Prop :=
| pout_penv_reply_intro rv m msrc mtgt pe
    (MJOIN: join m msrc mtgt):
  pout_penv_reply m (cr rv msrc, pe) (cr rv mtgt, pe).

Program Definition pout_penv: callconv (li_c@ClightP.penv) (li_c@ClightP.penv) :=
  {|
    ccworld := Memory.mem;
    match_senv _ se1 se2 := se1 = se2;
    match_query := pout_penv_query;
    match_reply := pout_penv_reply;
  |}.
Next Obligation. reflexivity. Qed.
Next Obligation. inv H0. reflexivity. Qed.
Next Obligation. inv H. reflexivity. Qed.

Definition cc_out_penv': ST.callconv (li_c@ClightP.penv) (li_c@ClightP.penv)
  := &pout_penv.

Program Definition cc_conjoint : ST.callconv li_c (li_c@mem) :=
  {|
    ST.ccworld := mem;
    ST.match_query m1 q1 '(q2, m2) := q1 = q2 /\ m1 = m2;
    ST.match_reply m1 r1 '(r2, m2) := r1 = r2 /\ m1 = m2;
  |}.

Definition cc_in: ST.callconv li_c li_c := ST.cc_compose cc_conjoint &cc_join.

Inductive cc_in_query: Memory.mem -> query li_c -> query li_c -> Prop :=
| cc_in_query_intro vf sg vargs m msrc mtgt
    (MJOIN: join m msrc mtgt):
  cc_in_query m (cq vf sg vargs msrc) (cq vf sg vargs mtgt).

Inductive cc_in_reply: Memory.mem -> reply li_c -> reply li_c -> Prop :=
| cc_in_reply_intro rv m msrc mtgt
    (MJOIN: join m msrc mtgt):
  cc_in_reply m (cr rv msrc) (cr rv mtgt).

Program Definition cc_in' : ST.callconv li_c li_c :=
  {|
    ST.ccworld := mem;
    ST.match_query := cc_in_query;
    ST.match_reply := cc_in_reply;
  |}.

Variable skel: AST.program unit unit.

Definition encap_prim (U: Type) `{PSet U}: li_c@U +-> li_c :=
  {|
    pstate := U;
    esem := id_semantics skel;
  |}.

Definition eclightp (p: ClightP.program) :=
  comp_esem' (encap_prim (ClightP.penv)) (semantics_embed (ClightP.clightp1 p)) (ClightP.clightp_erase_program p).

(** ------------------------------------------------------------------------- *)
(** Properties *)

Section CC_IN.
(** [cc_in] is supposed to be parametrized over an init memory fragment *)

  Inductive cc_in_inv: ST.ccworld (ST.cc_compose cc_in' cc_in') -> ST.ccworld cc_in' -> Prop :=
  | cc_in_inv_intro:
    forall m m1 m2, join m1 m2 m -> cc_in_inv (m1, m2) m.
  Inductive cc_in_ms: ST.ccworld (ST.cc_compose cc_in' cc_in') -> ST.ccworld cc_in' -> @state li_c li_c 1 -> @state li_c li_c 1 -> Prop :=
  | cc_in_ms_query:
    forall q1 q2 m1 m2 m,
      ST.match_query cc_in' m q1 q2 ->
      join m1 m2 m ->
      cc_in_ms (m1, m2) m (st_q q1) (st_q q2)
  | cc_in_ms_reply:
    forall r1 r2 m1 m2 m,
      ST.match_reply cc_in' m r1 r2 ->
      join m1 m2 m ->
      cc_in_ms (m1, m2) m (st_r r1) (st_r r2).

  Lemma cc_in_idemp:
    st_ccref cc_in' (ST.cc_compose cc_in' cc_in').
  Proof.
    apply st_normalize_fsim. constructor.
    eapply ST.Forward_simulation with
      (ltof _ (fun (_: unit) => 0)) (fun _ wa wb _ => cc_in_ms wa wb)
      (fun wa wb => cc_in_inv wa wb); try easy.
    - admit.
    - admit.
    - intros wa wb se I. inv I. constructor.
      + intros q1 q2 s1 wb1 Hb Hq Hx. exists tt, (st_q q2).
        inv Hx. inv Hb. inv Hq.
        split. constructor.
        eexists (_, _), _. repeat split; eauto.
        constructor; eauto.
        constructor. eauto.
      + intros wa1 wb1 [] s1 s2 r1 HS HF. inv HF. inv HS.
        inv H1.
        eexists. split. econstructor.
        eexists _. split. reflexivity.
        split. 2: constructor; eauto.
        constructor. eauto.
      + intros wa wb1 [ ] s1 s2 q1 HS HE.
        inv HE. inv HS. inv H1.
        eexists. split. constructor.
        eexists (_, _). split. reflexivity.
        split.
        apply join_commutative in H4.
        edestruct join_associative_exist as (mx & A & B).
        apply H4. apply MJOIN.
        eexists. split; constructor; eauto.
        intros r1 r2 s1' wa1 HA HR HE.
        destruct wa1. inv HA. inv H0. inv H1.
        inv HE.
        destruct HR as (rx & A & B). inv A. inv B.
        eexists tt, _. split. constructor.
        apply join_commutative in MJOIN0.
        apply join_commutative in MJOIN1.
        edestruct join_associative_exist as (mx & A & B).
        apply MJOIN0. apply MJOIN1.
        eexists (_, _), mx. split. reflexivity.
        split. constructor.
        constructor; eauto.
        constructor. apply join_commutative. eauto.
      + easy.
  Admitted.

End CC_IN.

Section CC_OUT.

  Inductive cc_out_inv: ST.ccworld cc_out' -> ST.ccworld (ST.cc_compose cc_out' cc_out') -> Prop :=
  | cc_out_inv_intro:
    forall m m1 m2, join m1 m2 m -> cc_out_inv m (m1, m2).
  Inductive cc_out_ms: ST.ccworld cc_out' -> ST.ccworld (ST.cc_compose cc_out' cc_out') -> @state li_c li_c 1 -> @state li_c li_c 1 -> Prop :=
  | cc_out_query:
    forall q1 q2 m1 m2 m,
      ST.match_query cc_out' m q1 q2 ->
      join m1 m2 m ->
      cc_out_ms m (m1, m2) (st_q q1) (st_q q2)
  | cc_out_reply:
    forall r1 r2 m1 m2 m,
      ST.match_reply cc_out' m r1 r2 ->
      join m1 m2 m ->
      cc_out_ms m (m1, m2) (st_r r1) (st_r r2).

  Lemma cc_out_idemp:
    st_ccref (ST.cc_compose cc_out' cc_out') cc_out'.
  Proof.
    apply st_normalize_fsim. constructor.
    eapply ST.Forward_simulation with
      (ltof _ (fun (_: unit) => 0)) (fun _ wa wb _ => cc_out_ms wa wb)
      (fun wa wb => cc_out_inv wa wb); try easy.
    - admit.
    - admit.
    - intros wa wb se I. inv I. constructor.
      + intros q1 q2 s1 wb1 Hb Hq Hx. exists tt, (st_q q2).
        inv Hx. destruct wb1. inv Hb. inv H0. inv H1.
        destruct Hq as (qx & A & B).
        inv A. inv B.
        split. constructor.
        eexists _, (_, _). repeat split; eauto.
        constructor; eauto.
        eexists.
        apply join_commutative.
        eapply join_associative.
        apply join_commutative; eauto.
        apply join_commutative; eauto. eauto.
      + intros wa1 wb1 [] s1 s2 r1 HS HF. inv HF. inv HS.
        inv H1.
        eexists. split. econstructor.
        eexists (_, _). split; eauto.
        reflexivity. split. 2: constructor; eauto.
        edestruct join_associative_exist as (mx & A & B).
        apply join_commutative in H4.
        apply H4. apply MJOIN.
        eexists. split.
        econstructor. apply A.
        econstructor. apply B.
      + intros wa1 wb [ ] s1 s2 q1 HS HE.
        inv HE. inv HS. inv H1.
        eexists. split. constructor.
        eexists. split. reflexivity.
        split. constructor. apply MJOIN.
        intros r1 r2 s1' wa2 HA HR HE. inv HA.
        inv HE. inv HR.
        eexists tt, _. split. constructor.
        assert (exists n1 n2, join n1 n2 wa2) as (n1 & n2 & HN).
        admit.
        eexists _, (_, _). split. reflexivity.
        split. constructor; constructor.
        constructor. constructor. eauto. apply HN.
      + easy.
  Admitted.

End CC_OUT.

Section YYY.

  Context (p: Clight.program).

  Inductive clight_ms : ST.ccworld cc_in' -> ST.ccworld (ST.callconv_lift cc_in' unit unit) -> state (Clight.semantics1 p) -> state (Clight.semantics1 p) -> Prop :=
  | clight_ms_State:
    forall f s k e le m1 m2 mx,
      join mx m1 m2 ->
      clight_ms mx (mx, tt, tt) (Clight.State f s k e le m1) (Clight.State f s k e le m2)
  | clight_ms_Callstate:
    forall vf args k m1 m2 mx,
      join mx m1 m2 ->
      clight_ms mx (mx, tt, tt) (Clight.Callstate vf args k m1) (Clight.Callstate vf args k m2)
  | clight_ms_Returnstate:
    forall rv k m1 m2 mx,
      join mx m1 m2 ->
      clight_ms mx (mx, tt, tt) (Clight.Returnstate rv k m1) (Clight.Returnstate rv k m2).

  Inductive clight_inv : ST.ccworld cc_in' -> ST.ccworld (ST.callconv_lift cc_in' unit unit) -> Prop :=
  | clight_inv_intro m:
    clight_inv m (m, tt, tt).

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

  Lemma clight_in_step wa wb ge:
    forall s1 t s1',
      Clight.step1 ge s1 t s1' ->
      forall s2, clight_ms wa wb s1 s2 ->
            exists s2', Clight.step1 ge s2 t s2' /\
                     clight_ms wa wb s1' s2'.
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

  Lemma clight_in: E.forward_simulation cc_in' cc_in'
                     (semantics_embed (Clight.semantics1 p))
                     (semantics_embed (Clight.semantics1 p)).
  Proof.
    apply st_normalize_fsim. cbn. constructor.
    eapply ST.Forward_simulation with
      (ltof _ (fun (_: unit) => 0)) (fun _ wa wb _ => clight_ms wa wb)
      (fun wa wb => clight_inv wa wb); try easy.
    intros. inv H. destruct wB' as [[w []] []].
    destruct H0. destruct H. inv H. constructor.
    intros wa wb se INV.
    destruct wb as [[mx []] []]. inv INV.
    constructor.
    - intros [q1 []] [q2 []] s1 [[m []] []] HW HQ HX.
      destruct HW as [[HW []] []]. inv HW.
      inv HX. inv HQ. inv H4. inv H3.
      eexists tt, _. split.
      econstructor; eauto.
      apply mjoin_nextblock in MJOIN.
      rewrite MJOIN.
      unfold Ple in *.
      etransitivity; eauto.
      apply Pos.le_max_r.
      eexists m, (m, tt, tt). split. reflexivity.
      split. reflexivity.
      constructor. eauto.
    - intros wa [[wb []] []] [] s1 s2 [r1 []] HS HX.
      destruct HX as (rx & HX & HY). inv HX. inv HY. inv HS.
      eexists (_, tt). split. eexists. split; constructor.
      eexists (wb, tt, tt). split. reflexivity.
      split. constructor; constructor; eauto.
      constructor.
    - intros wa [[wb []] []] [] s1 s2 q1 HS HX.
      inv HX. cbn in H1. unfold id in H1. subst. inv HS.
      eexists. split. econstructor. eauto.
      eexists. split. reflexivity.
      split. constructor. eauto.
      intros r1 r2 s1' wa1 HA HR HX. inv HA.
      destruct HX as (rx & HX & HY).
      cbn in HX. unfold id in HX. subst. inv HY. inv HR.
      eexists tt, _. split. eexists. split; constructor.
      eexists _, (wa1, tt, tt). split. reflexivity.
      split. repeat constructor.
      constructor. eauto.
    - intros s1 t s1' HX wa [[wb []] []] [] s2 HS.
      cbn in *. exploit clight_in_step; eauto.
      intros (s2' & HY & HZ).
      eexists tt, s2'. split.
      left. apply plus_one. apply HY.
      eexists _, (_, tt, tt). repeat constructor; eauto.
  Qed.

End YYY.

Section ZZZ.

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
      ClightP.step1 ge s1 t s1' ->
      forall s2, clightp_ms mx s1 s2 ->
            exists s2', ClightP.step1 ge s2 t s2' /\
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

  Lemma clightp_out: forward_simulation pout pout_penv
                       (ClightP.clightp1 p) (ClightP.clightp1 p).
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

  Inductive penv_inv: ST.ccworld cc_out_penv' ->
                      ST.ccworld (ST.callconv_lift cc_out' ClightP.penv ClightP.penv) -> Prop :=
  | penv_inv_intro m pe:
    penv_inv m (m, pe, pe).

  Inductive penv_ms: ST.ccworld cc_out_penv' ->
                     ST.ccworld (ST.callconv_lift cc_out' ClightP.penv ClightP.penv) ->
                     @state (li_c@ClightP.penv) (li_c@ClightP.penv) (id_semantics skel) ->
                     @state (li_c@ClightP.penv) (li_c@ClightP.penv) (id_semantics skel) -> Prop :=
  | penv_ms_query:
    forall q1 q2 m pe,
      ST.match_query cc_out' m q1 q2 ->
      penv_ms m (m, pe, pe)
        (@st_q (li_c@ClightP.penv) (q1, pe))
        (@st_q (li_c@ClightP.penv) (q2, pe))
  | penv_ms_reply:
    forall r1 r2 m pe,
      ST.match_reply cc_out' m r1 r2 ->
      penv_ms m (m, pe, pe)
        (@st_r (li_c@ClightP.penv) (r1, pe))
        (@st_r (li_c@ClightP.penv) (r2, pe)).

  Lemma encap_prim_out:
    E.forward_simulation cc_out_penv' cc_out' (encap_prim ClightP.penv) (encap_prim ClightP.penv).
  Proof.
    apply st_normalize_fsim. cbn. constructor.
    eapply ST.Forward_simulation with
      (ltof _ (fun (_: unit) => 0)) (fun _ wa wb _ => penv_ms wa wb)
      (fun wa wb => penv_inv wa wb); try easy.
    - intros. cbn in *. eprod_crush. subst. eauto.
    - intros. inv H. constructor.
      + intros. cbn in *. eprod_crush. subst. inv H1. inv H0.
        eexists tt, _. split. constructor.
        eexists _, (_, _, _). split; eauto.
        split. repeat constructor.
        constructor. constructor; eauto.
      + intros. cbn in *. eprod_crush. inv H. inv H0. inv H0. inv H7.
        eexists (_, _). split. constructor.
        eexists (_, _, _). split. repeat constructor.
        split. split. constructor. eauto.
        split; eauto. constructor.
      + intros. cbn in *. eprod_crush. inv H0. inv H. inv H7.
        eexists (_, _). split. constructor.
        eexists _. split; eauto.
        split. constructor; eauto.
        intros. eprod_crush. inv H1. inv H0.
        eexists tt, _. split. constructor.
        eexists _, (_, _, _). split; eauto.
        split. repeat constructor.
        constructor. constructor. eauto.
      + easy.
  Qed.

  Lemma eclightp_out: E.forward_simulation cc_out' cc_out' (eclightp p) (eclightp p).
  Proof.
    unfold eclightp.
    eapply encap_fsim_lcomp_sk; eauto.
    instantiate (1 := cc_out_penv').
    - apply encap_prim_out.
    - apply encap_fsim_embed.
      apply clightp_out.
  Admitted.

End ZZZ.

Section COMP.

  Context (S1: li_c +-> li_c) (S2: li_c +-> li_c)
    (T1: li_c +-> li_c) (T2: li_c +-> li_c)
    (H1: E.forward_simulation cc_out' cc_in' S1 T1)
    (H2: E.forward_simulation cc_out' cc_in' S2 T2).
  Variable sk: AST.program unit unit.

  Hypothesis P1: E.forward_simulation cc_in' cc_in' T1 T1.
  Hypothesis P2: E.forward_simulation cc_out' cc_out' S2 S2.

  Theorem clightp_comp:
    E.forward_simulation cc_out' cc_in' (comp_esem' S1 S2 sk) (comp_esem' T1 T2 sk).
  Proof.
    rewrite <- cc_out_idemp. rewrite cc_in_idemp.
    eapply encap_fsim_lcomp_sk; eauto.
    instantiate (1 := (ST.cc_compose cc_out' cc_in')).
    - eapply encap_fsim_vcomp; eauto.
    - eapply encap_fsim_vcomp; eauto.
    - admit.
    - admit.
  Admitted.

End COMP.

(** promote the result from [ClightP.v] to encapsulation version *)
Section ESIM.

  Context (S: semantics li_c (li_c @ ClightP.penv))
    (T: semantics li_c li_c) (ce: Ctypes.composite_env)
    (H: forward_simulation pout (pin ce) S T).

  Lemma promote_clightp sk:
    E.forward_simulation cc_out' cc_in'
      (comp_esem' (encap_prim (ClightP.penv)) (semantics_embed S) sk)
      (semantics_embed T).
  Proof.
    rewrite <- (ccref_right_unit2 cc_out').
    rewrite (ccref_right_unit1 cc_in').
    eapply encap_fsim_vcomp.
    instantiate (1 := (comp_esem' (semantics_embed (id_semantics sk)) (semantics_embed T) sk) ).
    eapply encap_fsim_lcomp_sk.
  Admitted.

End ESIM.
