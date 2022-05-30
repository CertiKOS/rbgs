From Coq Require Import
     Relations RelationClasses List.
From compcertox Require Import
     Lifting AbRel.
From compcert.lib Require Import
     Coqlib Maps.
From compcert.common Require Import
     LanguageInterface Events
     Globalenvs Smallstep
     Linking Memory Values
     CallconvAlgebra.

Ltac prod_crush :=
  repeat
    (match goal with
     | [ H: ?a * ?b |- _ ] => destruct H;cbn [fst snd] in *; subst
     | [ H: (?a, ?b) = (?c, ?d) |- _ ] => inv H
     | [ H: (?x * ?y)%rel _ _ |- _] => destruct H; cbn [fst snd] in *; subst
     | [ H: ?x /\ ?y |- _] => destruct H
     end).

Class MemPcm : Type :=
  mk_mem_pcm {
      join: mem -> mem -> mem -> Prop;
      empty: mem;

      pcm_unit_l: forall m, join empty m m;
      pcm_unit_r: forall m, join m empty m;
      pcm_comm: forall a b c, join a b c <-> join b a c;
      pcm_assoc:
      forall m1 m2 m3 m,
      (exists m12, join m1 m2 m12 /\ join m12 m3 m) <->
      (exists m23, join m1 m23 m /\ join m2 m3 m23);
    }.
Arguments join {_}.

Notation " a |+| b == c " := (join a b c) (at level 70).

Context {MP: MemPcm}.

Axiom alloc_frame_rel:
  forall mr lo hi b ms ms' mf,
    ms |+| mr == mf ->
    Mem.alloc ms lo hi = (ms', b) ->
    exists mf', ms' |+| mr == mf' /\
             Mem.alloc mf lo hi = (mf', b).

Axiom free_frame_rel:
  forall mr lo hi b ms ms' mf,
    ms |+| mr == mf ->
    Mem.free ms b lo hi = Some ms' ->
    exists mf', ms' |+| mr == mf' /\
             Mem.free mf b lo hi = Some mf'.

Axiom store_frame_rel:
  forall mr ch ms ms' mf b ofs v,
    ms |+| mr == mf ->
    Mem.store ch ms b ofs v = Some ms' ->
    exists mf', ms' |+| mr == mf' /\
             Mem.store ch mf b ofs v = Some mf'.

Axiom load_frame_rel:
  forall mr ch ms mf b ofs v,
    ms |+| mr == mf ->
    Mem.load ch ms b ofs = Some v ->
    Mem.load ch mf b ofs = Some v.

Axiom storebytes_frame_rel:
  forall mr vs ms ms' mf b ofs,
    ms |+| mr == mf ->
    Mem.storebytes ms b ofs vs = Some ms' ->
    exists mf', ms' |+| mr == mf' /\
           Mem.storebytes mf b ofs vs = Some mf'.

Axiom loadbytes_frame_rel:
  forall mr vs ms mf b lo hi,
    ms |+| mr == mf ->
    Mem.loadbytes ms b lo hi = Some vs ->
    Mem.loadbytes mf b lo hi = Some vs.

Axiom perm_frame_rel:
  forall mr ms mf b ofs k p,
    ms |+| mr == mf ->
    Mem.perm ms b ofs k p ->
    Mem.perm mf b ofs k p.

Axiom frame_nextblock:
  forall mr ms mf,
    ms |+| mr == mf ->
    Ple (Mem.nextblock ms) (Mem.nextblock mf).

Section ABREL_CC.
  Context {Ks Kf} (R: abrel Ks Kf).

  Inductive abrel_pcc_query: mem * Genv.symtbl -> query (li_c @ Ks) -> query (li_c @ Kf) -> Prop :=
  | abrel_pcc_query_intro se (ms mf mr: mem) vf sg vargs ks kf
      (HM: ms |+| mr == mf)
      (ABS: R se ks (mr, kf)):
    abrel_pcc_query (mr, se) (cq vf sg vargs ms, ks) (cq vf sg vargs mf, kf).

  Inductive abrel_pcc_reply: mem * Genv.symtbl -> reply (li_c @ Ks) -> reply (li_c @ Kf) -> Prop :=
  | abrel_pcc_reply_intro se (ms mf mr: mem) vr ks kf
      (HM: ms |+| mr == mf)
      (ABS: R se ks (mr, kf)):
    abrel_pcc_reply (mr, se) (cr vr ms, ks) (cr vr mf, kf).

  Instance abrel_pcc_kf: KLR.KripkeFrame unit (mem * Genv.symtbl) :=
    {| KLR.acc _ '(_, se1) '(_, se2) := se1 = se2; |}.

  Program Definition abrel_pcc: callconv (li_c @ Ks) (li_c @ Kf) :=
    {|
      ccworld := mem * Genv.symtbl;
      match_senv '(_, se) := fun se1 se2 => se = se1 /\ se = se2;
      match_query := abrel_pcc_query;
      match_reply := (KLR.klr_diam tt) abrel_pcc_reply;
    |}.
  Next Obligation. reflexivity. Qed.
  Next Obligation. inv H0. reflexivity. Qed.
  Next Obligation. inv H. reflexivity. Qed.

End ABREL_CC.

Axiom join_unchanged_on:
  forall m1 m2 m m' P,
    m1 |+| m2 == m -> Mem.unchanged_on P m m' ->
    exists m1' m2', m1' |+| m2' == m'
               /\ Mem.unchanged_on P m1 m1'
               /\ Mem.unchanged_on P m2 m2'.

(* These should be derivable *)
Axiom join_valid_block_l:
  forall m1 m2 m b,
    m1 |+| m2 == m -> Mem.valid_block m1 b -> Mem.valid_block m b.
Axiom join_valid_block_r:
  forall m1 m2 m b,
    m1 |+| m2 == m -> Mem.valid_block m2 b -> Mem.valid_block m b.


Program Definition abrel_comp {Ks Kn Kf} (R: abrel Ks Kn) (S: abrel Kn Kf) :=
  {|
    abrel_pred (se: Genv.symtbl) ks '(m, kf) :=
      exists kn mr ms, R se ks (mr, kn) /\ S se kn (ms, kf) /\ mr |+| ms == m;
    abrel_footprint := abrel_footprint R ++ abrel_footprint S;
  |}.
Next Obligation.
  edestruct join_unchanged_on as (A & B & ? & ? & ?); eauto.
  exists H, A, B. repeat split; eauto.
  - eapply abrel_invar; eauto.
    eapply Mem.unchanged_on_implies; eauto.
    intros. rewrite locsp_app. now left.
  - eapply abrel_invar; eauto.
    eapply Mem.unchanged_on_implies; eauto.
    intros. rewrite locsp_app. now right.
Qed.
Next Obligation.
  rewrite locsp_app in *. destruct H0.
  - eapply abrel_valid in H3; eauto. eapply join_valid_block_l; eauto.
  - eapply abrel_valid in H4; eauto. eapply join_valid_block_r; eauto.
Qed.
(* we might not need abrel_perm *)
Next Obligation.
  rewrite locsp_app in *. destruct H0.
  - eapply abrel_perm in H3; eauto. eapply perm_frame_rel; eauto.
  - eapply abrel_perm in H4; eauto.
    eapply perm_frame_rel. apply pcm_comm. all: eauto.
Qed.

Lemma abrel_pcc_comp {Ks Kn Kf} (R: abrel Ks Kn) (S: abrel Kn Kf):
  cceqv (abrel_pcc (abrel_comp R S)) (abrel_pcc R @ abrel_pcc S)%cc.
Proof.
  split.
  - intros [mx se]. intros * Hse Hq. inv Hse. rename se2 into se.
    inv Hq. destruct ABS as (A & B & C & D & E & F).
    eexists (se, (B, se), (C, se)). repeat split.
    + edestruct pcm_assoc as [X _]. apply pcm_comm in F.
      edestruct X as (H & Y & Z). exists mx. split; eauto. apply pcm_comm; eauto.
      econstructor. split; econstructor; eauto. all: apply pcm_comm; eauto.
    + intros. inv H. prod_crush. clear - H H0.
      destruct H as ((my & se1) & D & E). inv D. inv E.
      destruct H0 as ((mz & se2) & D & E). inv D. inv E. rename se2 into se.
      edestruct pcm_assoc as [X _]. apply pcm_comm in HM0.
      edestruct X as (H & Y & Z). exists mf. split; eauto. apply pcm_comm; eauto.
      eexists (H, _). split; constructor; eauto.
      eexists _, _, _. repeat split; eauto.
  - intros [[se (m1 & se1)] (m2 & se2)].
    cbn. intros. split_hyps. subst. prod_crush.
    inv H1. inv H0.
    edestruct pcm_assoc as [X _]. edestruct X as (Y & A & B).
    exists ms; split; eauto. eexists (Y, _). repeat split; eauto.
    eexists _, _, _. repeat split; eauto.
    intros. prod_crush. clear -H.
    destruct H as ((m&se) & A & B). inv A. inv B.
    cbn in ABS. split_hyps. edestruct pcm_assoc as [_ X].
    edestruct X as (Z & A & B). exists m; split; eauto.
    eexists (cr _ _, _). split.
    + eexists (_, _). repeat split; eauto.
    + eexists (_, _). repeat split; eauto.
Qed.

Program Definition abrel_tens {Ks1 Ks2 Kf1 Kf2} (R1: abrel Ks1 Kf1) (R2: abrel Ks2 Kf2)
  : abrel (Ks1 * Ks2) (Kf1 * Kf2) :=
  {|
    abrel_pred (se: Genv.symtbl) '(ks1, ks2) '(m, (kf1, kf2)) :=
      exists mr ms, R1 se ks1 (mr, kf1) /\ R2 se ks2 (ms, kf2) /\ mr |+| ms == m;
    abrel_footprint := abrel_footprint R1 ++ abrel_footprint R2;
  |}.
Next Obligation.
  edestruct join_unchanged_on as (A & B & ? & ? & ?); eauto.
  exists A, B. repeat split; eauto.
  - eapply abrel_invar; eauto.
    eapply Mem.unchanged_on_implies; eauto.
    intros. rewrite locsp_app. now left.
  - eapply abrel_invar; eauto.
    eapply Mem.unchanged_on_implies; eauto.
    intros. rewrite locsp_app. now right.
Qed.
Next Obligation.
  rewrite locsp_app in *. destruct H0.
  - eapply abrel_valid in H2; eauto. eapply join_valid_block_l; eauto.
  - eapply abrel_valid in H3; eauto. eapply join_valid_block_r; eauto.
Qed.
(* we might not need abrel_perm *)
Next Obligation.
  rewrite locsp_app in *. destruct H0.
  - eapply abrel_perm in H2; eauto. eapply perm_frame_rel; eauto.
  - eapply abrel_perm in H3; eauto.
    eapply perm_frame_rel. apply pcm_comm. all: eauto.
Qed.

Section CLIGHT.

  Import Clight.
  Import OptionRel.

  Definition mem_frame_rel mr : mem -> mem -> Prop := fun mx my => mx |+| mr == my.

  Inductive state_frame_rel mr : state -> state -> Prop :=
  | State_frame_rel:
    Monotonic (State) (- ==> - ==> - ==> - ==> - ==> mem_frame_rel mr ++> state_frame_rel mr)
  | Callstate_frame_rel:
    Monotonic (Callstate) (- ==> - ==> - ==> mem_frame_rel mr ++> state_frame_rel mr)
  | Returnstate_frame_rel:
    Monotonic (Returnstate) (- ==> - ==> mem_frame_rel mr ++> state_frame_rel mr).

  Global Instance valid_pointer_frame_rel mr:
    Monotonic
      (@Mem.valid_pointer)
      (mem_frame_rel mr ++> - ==> - ==> Bool.leb).
  Proof.
    rstep. rstep. rstep. rstep.
    destruct Mem.valid_pointer eqn: X.
    - simpl. revert X. rewrite !Mem.valid_pointer_nonempty_perm.
      eapply perm_frame_rel. eauto.
    - easy.
  Qed.

  Global Instance weak_valid_pointer_frame_rel mr:
    Monotonic
      (@Mem.weak_valid_pointer)
      (mem_frame_rel mr ++> - ==> - ==> Bool.leb).
  Proof.
    unfold Mem.weak_valid_pointer.
    rstep. rstep. rstep. rstep.
    destruct orb eqn: X.
    - simpl. apply orb_true_iff in X. apply orb_true_iff.
      destruct X;
        [ left | right ]; rewrite !Mem.valid_pointer_nonempty_perm in *;
                 eapply perm_frame_rel; eauto.
    - easy.
  Qed.

  Global Instance bool_val_frame_rel mr:
    Monotonic
      (@Cop.bool_val)
      (- ==> - ==> mem_frame_rel mr ++> option_le eq).
  Proof. unfold Cop.bool_val. rauto. Qed.

  Global Instance sem_unary_operation_frame_rel mr:
    Monotonic
      (@Cop.sem_unary_operation)
      (- ==> - ==> - ==> mem_frame_rel mr ++> option_le eq).
  Proof.
    unfold Cop.sem_unary_operation.
    unfold
      Cop.sem_notbool,
      Cop.sem_notint,
      Cop.sem_absfloat,
      Cop.sem_neg.
    repeat rstep. f_equal. congruence.
  Qed.
  Hint Rewrite <- sem_unary_operation_frame_rel using eauto : rel_base.

  Global Instance sem_cast_frame_rel mr:
    Monotonic
      (@Cop.sem_cast)
      (- ==> - ==> - ==> mem_frame_rel mr ++> option_le eq).
  Proof. unfold Cop.sem_cast. repeat rstep. Qed.

  Global Instance sem_binarith_frame_rel mr:
    Monotonic
      (@Cop.sem_binarith)
      (- ==> - ==> - ==> - ==> - ==> - ==> - ==> - ==> mem_frame_rel mr ++> option_le eq).
  Proof. unfold Cop.sem_binarith. repeat rstep. Qed.

  Global Instance cmp_ptr_match mr:
    Related
      (@Cop.cmp_ptr)
      (@Cop.cmp_ptr)
      (mem_frame_rel mr ++> - ==> - ==> - ==> option_le eq).
  Proof.
    rstep. rstep. rstep. rstep. rstep.
    unfold Cop.cmp_ptr. rstep. rstep. rewrite H0. reflexivity. rstep.
    - rstep. unfold Val.cmplu_bool. repeat rstep.
    - rstep. unfold Val.cmpu_bool. repeat rstep.
      Unshelve. all: eauto.
  Qed.

  Global Instance sem_cmp_match mr:
    Monotonic
      (@Cop.sem_cmp)
      (- ==> - ==> - ==> - ==> - ==> mem_frame_rel mr ++> option_le eq).
  Proof. unfold Cop.sem_cmp. repeat rstep. Qed.

  Global Instance sem_binary_operation_frame_rel mr:
    Monotonic
      (@Cop.sem_binary_operation)
      (- ==> - ==> - ==> - ==> - ==> - ==> mem_frame_rel mr ++> option_le eq).
  Proof.
    unfold Cop.sem_binary_operation.
    unfold
      Cop.sem_add,
      Cop.sem_add_ptr_int,
      Cop.sem_add_ptr_long,
      Cop.sem_sub,
      Cop.sem_mul,
      Cop.sem_div,
      Cop.sem_mod,
      Cop.sem_and,
      Cop.sem_or,
      Cop.sem_xor,
      Cop.sem_shl,
      Cop.sem_shr.
    repeat rstep.
  Qed.

  Global Instance load_frame_rel' mr:
    Monotonic
      (@Mem.load)
      (- ==> mem_frame_rel mr ++> - ==> - ==> option_le eq).
  Proof.
    repeat rstep. destruct Mem.load eqn: X.
    - erewrite load_frame_rel; eauto. now constructor.
    - constructor.
  Qed.

  Global Instance loadv_frame_rel mr:
    Monotonic
      (@Mem.loadv)
      (- ==> mem_frame_rel mr ++> - ==> option_le eq).
  Proof. unfold Mem.loadv. repeat rstep. Qed.

  Global Instance deref_loc_frame_rel mr a:
    Monotonic
      (@deref_loc a)
      (mem_frame_rel mr ++> - ==> - ==> - ==> impl).
  Proof.
    repeat rstep. intros A. inv A; eauto using @deref_loc_reference, @deref_loc_copy.
    transport H1. subst. eapply deref_loc_value; eauto.
  Qed.

  Lemma eval_expr_lvalue_frame_rel mr ge e le:
  forall ms mf, (mem_frame_rel mr) ms mf ->
  (forall expr v,
     eval_expr ge e le ms expr v ->
     eval_expr ge e le mf expr v) /\
  (forall expr b ofs,
     eval_lvalue ge e le ms expr b ofs ->
     eval_lvalue ge e le mf expr b ofs).
  Proof.
    intros ms mf Hm.
    apply eval_expr_lvalue_ind;
      try solve [ intros; econstructor; eauto ].
    - intros. econstructor; eauto. transport H1. congruence.
    - intros. econstructor; eauto.
      pose proof sem_binary_operation_frame_rel.
      exploit H4. apply Hm. rewrite H3. inversion 1. congruence.
    - intros. econstructor; eauto.
      transport H1. congruence.
    - intros. econstructor; eauto.
      exploit deref_loc_frame_rel; eauto.
  Qed.

  Instance eval_expr_transp mr ge e le m m' a v:
    Transport (mem_frame_rel mr) m m' (eval_expr ge e le m a v) (eval_expr ge e le m' a v).
  Proof. intros A B. eapply eval_expr_lvalue_frame_rel; eauto. Qed.

  Instance eval_lvalue_transp mr ge e le m m' a b ofs:
    Transport (mem_frame_rel mr) m m' (eval_lvalue ge e le m a b ofs) (eval_lvalue ge e le m' a b ofs).
  Proof. intros A B. eapply eval_expr_lvalue_frame_rel; eauto. Qed.

  Instance eval_exprlist_transp mr ge e le m m' al tl vl:
    Transport (mem_frame_rel mr) m m'
              (eval_exprlist ge e le m al tl vl) (eval_exprlist ge e le m' al tl vl).
  Proof.
    intros A B. induction B.
    - constructor.
    - transport_hyps. subst. econstructor; eauto.
  Qed.

  Instance alloc_variables_frame_rel mr:
    Monotonic
      (@alloc_variables)
      (- ==> - ==> mem_frame_rel mr ++> - ==> - ==> set_le (mem_frame_rel mr)).
  Proof.
    repeat rstep. intros m Hm.
    revert x0 x1 y H Hm; induction x2; intros ? ? ? ? Hm.
    - inv Hm. eexists; split; eauto. constructor.
    - inv Hm. edestruct alloc_frame_rel as (X & A & B); eauto.
      edestruct IHx2 as (Y & C & D). exact A. eauto.
      exists Y. split; eauto. econstructor; eauto.
  Qed.

  Instance function_entry2_frame_rel mr:
    Monotonic
      (@function_entry2)
      (- ==> - ==> - ==> mem_frame_rel mr ++> - ==> - ==> set_le (mem_frame_rel mr)).
  Proof.
    repeat rstep. intros m X. inv X.
    exploit alloc_variables_frame_rel; eauto.
    intros. split_hyps. eexists; split; eauto.
    constructor; eauto.
  Qed.

  Global Instance store_frame_rel' mr:
    Monotonic
      (@Mem.store)
      (- ==> mem_frame_rel mr ++> - ==> - ==> - ==> option_le (mem_frame_rel mr)).
  Proof.
    repeat rstep. destruct Mem.store eqn: X.
    - exploit store_frame_rel; eauto. intros (A & B & C).
      rewrite C. now constructor.
    - now constructor.
  Qed.

  Global Instance storev_frame_rel mr:
    Monotonic
      (@Mem.storev)
      (- ==> mem_frame_rel mr ++> - ==> - ==> option_le (mem_frame_rel mr)).
  Proof. unfold Mem.storev. repeat rstep. Qed.

  Global Instance loadbytes_frame_rel' mr:
    Monotonic
      (@Mem.loadbytes)
      (mem_frame_rel mr ++> - ==> - ==> - ==> option_le eq).
  Proof.
    repeat rstep. destruct Mem.loadbytes eqn: X.
    - exploit loadbytes_frame_rel; eauto.
      intros ->. now constructor.
    - constructor.
  Qed.

  Global Instance storebytes_frame_rel' mr:
    Monotonic
      (@Mem.storebytes)
      (mem_frame_rel mr ++> - ==> - ==> - ==> option_le (mem_frame_rel mr)).
  Proof.
    repeat rstep. destruct Mem.storebytes eqn: X.
    - exploit storebytes_frame_rel; eauto.
      intros. split_hyps. rewrite H1. constructor; eauto.
    - constructor.
  Qed.

  Global Instance assign_loc_frame_rel mr:
    Monotonic
      (@assign_loc)
      (- ==> - ==> mem_frame_rel mr ++> - ==> - ==> - ==> set_le (mem_frame_rel mr)).
  Proof.
    repeat rstep. intros m A. inv A.
    - transport H1. eexists; split; eauto.
      econstructor; eauto.
    - transport H4. subst.
      transport H5. eexists; split; eauto.
      eapply assign_loc_copy; eauto.
  Qed.

  Hint Extern 1 (Transport _ _ _ _ _) => set_le_transport @assign_loc : typeclass_instances.

  Lemma transport_in_goal_manual `{Transport}:
    forall (Q: Prop), (R a b) -> (PB -> Q) -> (PA -> Q).
  Proof. firstorder. Qed.

  Ltac transp H :=
    revert H;
    lazymatch goal with
    | |- ?PA -> ?Q =>
        eapply (transport_in_goal_manual (PA:=PA) Q)
    end;
    try solve [ rauto | rstep; eauto ]; intro H.

  Hint Extern 1 (state_frame_rel _ _ _) => constructor; eauto.

  Global Instance free_list_frame_rel mr:
    Monotonic
      (@Mem.free_list)
      (mem_frame_rel mr ++> - ==> option_le (mem_frame_rel mr)).
  Proof.
    repeat rstep. destruct Mem.free_list eqn: X.
    - revert x y m H X. induction x0; intros.
      + inv X. now constructor.
      + cbn in X. destruct a. destruct p.
        destruct Mem.free eqn: Y.
        * exploit free_frame_rel; eauto. intros. split_hyps.
          exploit IHx0; eauto. inversion 1. subst.
          cbn. rewrite H1. rewrite <- H4. now constructor.
        * inv X.
    - constructor.
  Qed.

  Global Instance external_call_frame_rel mr:
    Monotonic
      (@external_call)
      (- ==> - ==> - ==> mem_frame_rel mr ++> - ==> - ==> set_le (mem_frame_rel mr)).
  Proof.
    repeat rstep. intros m X.
  Admitted.
  Hint Extern 1 (Transport _ _ _ _ _) => set_le_transport @external_call : typeclass_instances.
  Hint Extern 1 (Transport _ _ _ _ _) => set_le_transport @function_entry2 : typeclass_instances.

  Lemma step2_frame_rel mr ge t ss ss' sf:
    state_frame_rel mr ss sf -> step2 ge ss t ss' ->
    exists sf', state_frame_rel mr ss' sf' /\ step2 ge sf t sf'.
  Proof.
    intros H H1.
    induction H1; inv H;
      try solve [ transport_hyps; subst; eexists; split; [ eauto | econstructor; eauto ] ].
    - transport H0. transport H1.
      transport H2. subst. transp H3. split_hyps.
      eexists; split. constructor; eauto.
      eapply step_assign; eauto.
  Qed.

End CLIGHT.

Section SIM.

  Context {Ks Kf} (R: abrel Ks Kf).

  Lemma clight_psim p:
    forward_simulation (abrel_pcc R) (abrel_pcc R)
                       (Clight.semantics2 p @ Ks) (Clight.semantics2 p @ Kf).
  Proof.
    constructor. econstructor; eauto. intros i. reflexivity.
    intros se1 se2 [mr se] Hse Hse1. inv Hse. rename se2 into se.
    instantiate (1 := fun _ _ '(mr, se) => _).
    pose (ms := fun '(ss, ks) '(sf, kf) =>
                  exists mr, R se ks (mr, kf) /\ state_frame_rel mr ss sf).
    cbn -[Clight.semantics2].
    eapply forward_simulation_step with (match_states := ms); cbn;
      intros;  subst ms; cbn in *; prod_crush.
    - inv H. inv H0.
      eexists (_, _). repeat split; eauto.
      + econstructor; eauto.
        (* The Ple thing should mean that the symbols in ge are allocated in mem *)
        cbn in *. etransitivity; eauto.
        eapply frame_nextblock. eauto.
      + eexists. split; eauto. constructor; eauto.
    - destruct H as (X & A & B). inv H0. inv B.
      eexists (_, _). repeat split; eauto.
      eexists (_, _); split. reflexivity.
      constructor; eauto.
    - destruct H as (X & A & B). inv H0. inv B.
      eexists (_, _), (_, _). repeat apply conj; cbn; eauto.
      econstructor; eauto. econstructor; eauto.
      intros. destruct H0 as (Y & C & D). prod_crush.
      inv H0. inv D. eexists (_, _). repeat split; eauto.
      inv C. eexists; split; eauto. constructor; eauto.
    - subst. destruct H0 as (X & A & B).
      edestruct step2_frame_rel as (Y & C & D); eauto.
      eexists (_, _). repeat split; eauto.
    - apply well_founded_ltof.
  Qed.

End SIM.

Section SUM.

  Context {liA liB} {K1 K2}
          (L1: semantics (liA@K1) (liB@K1))
          (L2: semantics (liA@K2) (liB@K2)).

  Section WITH_SE.
    Context (se: Genv.symtbl).
    Variant tens_state :=
      | state_l : state L1 -> K2 -> tens_state
      | state_r : state L2 -> K1 -> tens_state.

    Inductive tens_step : tens_state -> trace -> tens_state -> Prop :=
    | step_l s t s' k:
      Step (L1 se) s t s' -> tens_step (state_l s k) t (state_l s' k)
    | step_r s t s' k:
      Step (L2 se) s t s' -> tens_step (state_r s k) t (state_r s' k).

    Inductive tens_initial_state : query (liB@(K1*K2)) -> tens_state -> Prop :=
    | initial_state_l q k1 k2 s:
      initial_state (L1 se) (q, k1) s ->
      tens_initial_state (q, (k1, k2)) (state_l s k2)
    | initial_state_r q k1 k2 s:
      initial_state (L2 se) (q, k2) s ->
      tens_initial_state (q, (k1, k2)) (state_r s k1).

    Inductive tens_at_external : tens_state -> query (liA@(K1*K2)) -> Prop :=
    | at_external_l q k1 k2 s:
      at_external (L1 se) s (q, k1) ->
      tens_at_external (state_l s k2) (q, (k1, k2))
    | at_external_r q k1 k2 s:
      at_external (L2 se) s (q, k2) ->
      tens_at_external (state_r s k1) (q, (k1, k2)).

    Inductive tens_after_external : tens_state -> reply (liA@(K1*K2)) -> tens_state -> Prop :=
    | after_external_l s k1 k2 k2' r s':
      after_external (L1 se) s (r, k1) s' ->
      tens_after_external (state_l s k2) (r, (k1, k2')) (state_l s' k2')
    | after_external_r s k1 k2 k1' r s':
      after_external (L2 se) s (r, k2) s' ->
      tens_after_external (state_r s k1) (r, (k1', k2)) (state_r s' k1').

    Inductive tens_final_state : tens_state -> reply (liB@(K1*K2)) -> Prop :=
    | final_state_l s r k1 k2:
      final_state (L1 se) s (r, k1) ->
      tens_final_state (state_l s k2) (r, (k1, k2))
    | final_state_r s r k1 k2:
      final_state (L2 se) s (r, k2) ->
      tens_final_state (state_r s k1) (r, (k1, k2)).

    Program Definition tens_lts : lts (liA@(K1*K2)) (liB@(K1*K2)) tens_state :=
      {|
        step _ := tens_step;
        initial_state := tens_initial_state;
        at_external := tens_at_external;
        after_external := tens_after_external;
        final_state := tens_final_state;
        globalenv := tt;
      |}.

    Lemma star_internal_l s t s' k:
      Star (L1 se) s t s' ->
      star (fun _ => tens_step) tt (state_l s k) t (state_l s' k).
    Proof.
      induction 1; [eapply star_refl | eapply star_step]; eauto.
      constructor; auto.
    Qed.

    Lemma star_internal_r s t s' k:
      Star (L2 se) s t s' ->
      star (fun _ => tens_step) tt (state_r s k) t (state_r s' k).
    Proof.
      induction 1; [eapply star_refl | eapply star_step]; eauto.
      constructor; auto.
    Qed.

    Lemma plus_internal_l s t s' k:
      Plus (L1 se) s t s' ->
      plus (fun _ => tens_step) tt (state_l s k) t (state_l s' k).
    Proof.
      destruct 1; econstructor; eauto using step_l, star_internal_l.
    Qed.

    Lemma plus_internal_r s t s' k:
      Plus (L2 se) s t s' ->
      plus (fun _ => tens_step) tt (state_r s k) t (state_r s' k).
    Proof.
      destruct 1; econstructor; eauto using step_r, star_internal_r.
    Qed.

  End WITH_SE.

  Program Definition tens_semantics' sk: semantics (liA@(K1*K2)) (liB@(K1*K2)) :=
    {|
      activate se := tens_lts se; skel := sk;
      footprint i := footprint L1 i \/ footprint L2 i;
    |}.

  Definition tens_semantics :=
    option_map tens_semantics' (link (skel L1) (skel L2)).
End SUM.

Section LIFT_CC.

  Context {liA liB} (cc: callconv liA liB).
  Context {Ks Kf} (R: abrel Ks Kf).

  Program Definition cc_lift: callconv (liA@Ks) (liB@(mem*Kf)) :=
    {|
      ccworld := ccworld cc * Genv.symtbl;
      match_senv '(w, se) se1 se2 :=
        match_senv cc w se1 se2 /\ se = se1 /\ se = se2;
      match_query '(w, se) '(qs, ks) '(qf, (m, kf)) :=
        match_query cc w qs qf /\ R se ks (m, kf);
      match_reply '(w, se) '(rs, ks) '(rf, (m, kf)) :=
        match_reply cc w rs rf /\ R se ks (m, kf);
    |}.
  Next Obligation. reflexivity. Qed.
  Next Obligation. eapply match_senv_symbol_address; eauto. Qed.
  Next Obligation. eapply match_query_defined; eauto. Qed.

End LIFT_CC.

(*
Section CC_TENS.

  Context {Ks1 Ks2 Kf1 Kf2}
          (cc1: callconv (li_c@Ks1) (li_c@Kf1))
          (cc2: callconv (li_c@Ks2) (li_c@Kf2)).
  Program Definition cc_tens : callconv (li_c@(Ks1*Ks2)) (li_c@(Kf1*Kf2)) :=
    {|
      ccworld := ccworld cc1 * ccworld cc2;
      match_senv '(w1, w2) se1 se2 :=
        match_senv cc1 w1 se1 se2 /\ match_senv cc2 w2 se1 se2;
      match_query '(w1, w2) '(qs, (ks1, ks2)) '(qf, (kf1, kf2)) :=
        match_query cc1 w1 (qs, ks1) (qf, kf1) /\
        match_query cc2 w2 (qs, ks2) (qf, kf2);
      match_reply '(w1, w2) '(rs, (ks1, ks2)) '(rf, (kf1, kf2)) :=
        match_reply cc1 w1 (rs, ks1) (rf, kf1) /\
        match_reply cc2 w2 (rs, ks2) (rf, kf2);
    |}.
  Next Obligation. eapply match_senv_public_preserved; eauto. Qed.
  Next Obligation. eapply match_senv_valid_for; eauto. Qed.
  Next Obligation. eapply match_senv_symbol_address in H0; eauto. Qed.
  Next Obligation. eapply match_query_defined in H0; eauto. Qed.

  Program Definition cc_tens1 : callconv ((li_c@Ks1)@Ks2) ((li_c@Kf1)@Kf2) :=
    {|
      ccworld := ccworld cc1 * ccworld cc2;
      match_senv '(w1, w2) se1 se2 :=
        match_senv cc1 w1 se1 se2 /\ match_senv cc2 w2 se1 se2;
      match_query '(w1, w2) '(qs, ks1, ks2) '(qf, kf1, kf2) :=
        match_query cc1 w1 (qs, ks1) (qf, kf1) /\
        match_query cc2 w2 (qs, ks2) (qf, kf2);
      match_reply '(w1, w2) '(rs, ks1, ks2) '(rf, kf1, kf2) :=
        match_reply cc1 w1 (rs, ks1) (rf, kf1) /\
        match_reply cc2 w2 (rs, ks2) (rf, kf2);
    |}.
  Next Obligation. eapply match_senv_public_preserved; eauto. Qed.
  Next Obligation. eapply match_senv_valid_for; eauto. Qed.
  Next Obligation. eapply match_senv_symbol_address in H0; eauto. Qed.
  Next Obligation. eapply match_query_defined in H0; eauto. Qed.

End CC_TENS.
 *)

Section LIFT_SIM.

  Context {liA1 liA2 liB1 liB2} L1 L2
          (ccA: callconv liA1 liA2) (ccB: callconv liB1 liB2)
          (H: forward_simulation ccA ccB L1 L2).
  Context {Ks Kf} (R: abrel Ks Kf).

  Lemma lift_sim:
    forward_simulation (cc_lift ccA R) (cc_lift ccB R) (L1@Ks) (L2@(mem*Kf)).
  Proof.
    destruct H. constructor.
    eapply Forward_simulation with
      (fsim_order X)
      (fun se1 se2 '(w, se) i '(s1, k1) '(s2, (m, k2)) =>
         fsim_match_states X se1 se2 w i s1 s2 /\
           R se k1 (m, k2)).
    apply (fsim_skel X). apply (fsim_footprint X).
    intros se1 se2 [w se] Hse Hse1.
    destruct Hse as [Hse SE]. inv SE. rename se2 into se.
    clear H. pose proof (fsim_lts X) as H.
    specialize (H _ _ _ Hse Hse1).
    econstructor; intros; cbn in *; prod_crush.
    - exploit @fsim_match_initial_states. 1-3: eauto.
      intros (? & ? & ? & ?). eexists _, (_, (_, _)).
      repeat split; eauto.
    - exploit @fsim_match_final_states. 1-3: eauto.
      intros (? & ? & ?). eexists (_, (_, _)).
      repeat split; eauto.
    - exploit @fsim_match_external. 1-3: eauto.
      intros (? & ? & ?). prod_crush.
      eexists (_, _), (_, (_, _)). repeat split; eauto.
      intros; prod_crush. exploit H6; eauto.
      intros (? & ? & ? & ?). eexists _, (_, (_, _)).
      repeat split; eauto.
    - exploit @fsim_simulation. 1-3: eauto. subst.
      intros (? & ? & [|] & ?); eexists _, (_, (_, _)).
      + repeat split; eauto. left.
        apply lifting_step_plus; eauto.
      + repeat split; eauto. prod_crush. right.
        split; eauto. apply  lifting_step_star; eauto.
    - apply (fsim_order_wf X).
  Qed.

End LIFT_SIM.

Section FRAME_SIM.

  Context {K1 K2: Type}.

  Inductive cc_frame_query: query ((li_c @ K1) @ (mem * K2)) -> query ((li_c @ K1) @ K2) -> Prop :=
  | cc_fq_intro m1 m2 m vf sg vargs k1 k2
      (HM: m1 |+| m == m2):
    cc_frame_query ((cq vf sg vargs m1, k1), (m, k2)) (cq vf sg vargs m2, k1, k2).

  Inductive cc_frame_reply: reply ((li_c @ K1) @ (mem * K2)) -> reply ((li_c @ K1) @ K2) -> Prop :=
  | cc_fr_intro m1 m2 m vr k1 k2
      (HM: m1 |+| m == m2):
    cc_frame_reply ((cr vr m1, k1), (m, k2)) (cr vr m2, k1, k2).

  Program Definition cc_frame: callconv ((li_c @ K1) @ (mem * K2)) ((li_c @ K1) @ K2) :=
    {|
      ccworld := unit;
      match_senv _ := eq;
      match_query _ := cc_frame_query;
      match_reply _ := cc_frame_reply;
    |}.
  Next Obligation. reflexivity. Qed.
  Next Obligation. inv H0. reflexivity. Qed.
  Next Obligation. inv H. reflexivity. Qed.

  Class Frameable L:=
    frame_sim: forward_simulation cc_frame cc_frame (L @ (mem * K2)) (L @ K2).

End FRAME_SIM.

Section CC_ASSOC.

  Context {liA liB A1 A2 B1 B2} (cc: callconv (liA@(A1*A2)) (liB@(B1*B2))).
  Program Definition cc_assoc: callconv ((liA@A1)@A2) ((liB@B1)@B2) :=
    {|
      ccworld := ccworld cc;
      match_senv := match_senv cc;
      match_query w '(qa,a1,a2) '(qb,b1,b2) := match_query cc w (qa,(a1,a2)) (qb,(b1,b2));
      match_reply w '(ra,a1,a2) '(rb,b1,b2) := match_reply cc w (ra,(a1,a2)) (rb,(b1,b2));
    |}.
  Next Obligation. eapply match_senv_public_preserved; eauto. Qed.
  Next Obligation. eapply match_senv_valid_for; eauto. Qed.
  Next Obligation. eapply match_senv_symbol_address in H0; eauto. Qed.
  Next Obligation. eapply match_query_defined in H; eauto. Qed.

End CC_ASSOC.

Section TENS_SIM.

  Context {Ks1 Ks2 Kf1 Kf2: Type} (R: abrel Ks1 Kf1) (S: abrel Ks2 Kf2).

  Lemma lift_frame_cc:
    cceqv (cc_assoc (abrel_pcc (abrel_tens R S))) (cc_lift (abrel_pcc R) S @ cc_frame)%cc.
  Proof.
    split.
    - intros x. cbn in *. intros. prod_crush. subst.
      inv H0. inv ABS. split_hyps.
      eexists (_, (_, _, _), tt).
      repeat split; eauto.
      + edestruct pcm_assoc as [_ X].
        edestruct X as (Z & A & B). exists m; split; eauto.
        eexists (_, _, (_, _)). repeat split; eauto.
      + clear. intros. split_hyps. prod_crush.
        inv H. prod_crush. inv H. inv H0. inv H2.
        edestruct pcm_assoc as [X _].
        edestruct X as (Z & A & B). exists m2; split; eauto.
        eexists (_, _). repeat split; eauto.
        eexists _, _. repeat split; eauto.
    - intros x. cbn in *. intros. prod_crush. subst.
      split_hyps. prod_crush. inv H. inv H0.
      edestruct pcm_assoc as [X _].
      edestruct X as (Z & A & B). exists mf; split; eauto.
      eexists (_, _). repeat split; eauto.
      + eexists _, _. repeat split; eauto.
      + clear. intros. prod_crush. inv H.
        prod_crush. inv H. inv H0.
        cbn in *. split_hyps.
        edestruct pcm_assoc as [_ X].
        edestruct X as (Y & A & B). exists m0; split; eauto.
        eexists (_, _, (_, _)). repeat split; eauto.
        eexists (_, _). repeat split; eauto.
  Qed.

  Context Ls Lf (H: forward_simulation (abrel_pcc R) (abrel_pcc R) Ls Lf)
          (HF: Frameable (K2:=Kf2) Lf).

  Lemma lift_sim':
    forward_simulation (cc_assoc (abrel_pcc (abrel_tens R S)))
                       (cc_assoc (abrel_pcc (abrel_tens R S)))
                       (Ls @ Ks2) (Lf @ Kf2).
  Proof.
    eapply lift_sim with (R0:=S) in H.
    eapply open_fsim_ccref. apply lift_frame_cc. apply lift_frame_cc.
    eapply compose_forward_simulations. eauto.
    eapply frame_sim.
  Qed.

End TENS_SIM.

Section FRAME_CC.

End FRAME_CC.

Lemma lifting_step_star_inv {liA liB K} (L: Smallstep.semantics liA liB) se s1 t s2:
  Star(lifted_lts K (L se)) s1 t s2 ->
  Star (L se) (fst s1) t (fst s2) /\ snd s1 = snd s2.
Proof.
  induction 1.
  - split. apply star_refl. reflexivity.
  - prod_crush. subst. split.
    eapply star_step; eauto. inv H. apply H2.
    inv H. reflexivity.
Qed.

Lemma lifting_step_plus_inv {liA liB K} (L: Smallstep.semantics liA liB) se s1 t s2:
  Plus (lifted_lts K (L se)) s1 t s2 ->
  Plus (L se) (fst s1) t (fst s2) /\ snd s1 = snd s2.
Proof.
  destruct 1. prod_crush. split. econstructor; eauto.
  - inv H. apply H1.
  - eapply lifting_step_star_inv in H0. apply H0.
  - inv H. eapply lifting_step_star_inv in H0. easy.
Qed.

Section COMP.

  Generalizable All Variables.
  Context `(R1: abrel K1s K1f) `(R2: abrel K2s K2f)
          `(X1 : fsim_components (cc_assoc (abrel_pcc (abrel_tens R1 R2)))
                                 (cc_assoc (abrel_pcc (abrel_tens R1 R2))) (L1s @ K2s) (L1f @ K2f))
          `(X2 : fsim_components (cc_assoc (abrel_pcc (abrel_tens R2 R1)))
                                 (cc_assoc (abrel_pcc (abrel_tens R2 R1))) (L2s @ K1s) (L2f @ K1f))
          (se: Genv.symtbl) (m: mem).
  Hypothesis (Hse: match_senv (abrel_pcc (abrel_tens R1 R2)) (m, se) se se)
             (Hse1: Genv.valid_for (skel L1s) se) (Hse2: Genv.valid_for (skel L2s) se).

  Arguments state_l {_ _ _ _ _ _}.
  Arguments state_r {_ _ _ _ _ _}.
  Variant tindex := index_l: fsim_index X1 -> tindex | index_r: fsim_index X2 -> tindex.
  Variant torder : tindex -> tindex -> Prop :=
    | torder_l x y : fsim_order X1 x y -> torder (index_l x) (index_l y)
    | torder_r x y : fsim_order X2 x y -> torder (index_r x) (index_r y).
  Variant tmatch : tindex -> tens_state L1s L2s -> tens_state L1f L2f -> Prop :=
    | tmatch_l i ss sf k2s k2f:
      fsim_match_states X1 se se (m, se) i (ss, k2s) (sf, k2f) ->
      tmatch (index_l i) (state_l ss k2s) (state_l sf k2f)
    | tmatch_r i ss sf k1s k1f:
      fsim_match_states X2 se se (m, se) i (ss, k1s) (sf, k1f) ->
      tmatch (index_r i) (state_r ss k1s) (state_r sf k1f).

  Lemma tens_fsim' sk1 sk2:
    fsim_properties (abrel_pcc (abrel_tens R1 R2)) (abrel_pcc (abrel_tens R1 R2))
                    se se (m, se)
                    (tens_semantics' L1s L2s sk1 se)
                    (tens_semantics' L1f L2f sk2 se)
                    tindex torder tmatch.
  Proof.
    split; cbn.
    - intros. prod_crush. inv H0.
      + edestruct @fsim_match_initial_states as (i & x & Hi & Hx). apply X1; eauto.
        instantiate (2 := (c0, k1, k2)). instantiate (1 := (c, k, k0)). apply H.
        instantiate (1 := (_, _)). constructor; cbn; eauto.
        destruct x. inv Hi. cbn in *. subst.
        eexists (index_l _), (state_l _ _).
        split; constructor; eauto.
      + edestruct @fsim_match_initial_states as (i & x & Hi & Hx). apply X2; eauto.
        instantiate (2 := (c0, k2, k1)). instantiate (1 := (c, k0, k)).
        inv H. constructor; eauto. cbn in ABS. split_hyps. eexists _, _; repeat  split; eauto.
        apply pcm_comm; eauto.
        instantiate (1 := (_, _)). constructor; cbn; eauto.
        destruct x. inv Hi. cbn in *. subst.
        eexists (index_r _), (state_r _ _).
        split; constructor; eauto.
    - intros. prod_crush. inv H.
      + inv H0. edestruct @fsim_match_final_states as (r & Ha & Hb). apply X1; eauto.
        apply H1. constructor. instantiate (1 := (_, _)). all: eauto. reflexivity. clear Hse.
        inv Ha. cbn in *. prod_crush.
        inv Hb. prod_crush. inv H0.
        eexists (_, (_, _)). repeat split; eauto.
        constructor; eauto. eexists (_, _). split; try constructor. eauto.
      + inv H0. edestruct @fsim_match_final_states as (r & Ha & Hb). apply X2; eauto.
        apply H1. constructor. instantiate (1 := (_, _)). all: eauto. reflexivity. clear Hse.
        inv Ha. cbn in *. prod_crush.
        inv Hb. prod_crush. inv H0.
        eexists (_, (_, _)). repeat split; eauto.
        constructor; eauto. eexists (_, _). split; try constructor.
        inv H3. econstructor; eauto. cbn in ABS. split_hyps. eexists _, _. repeat split; eauto.
        apply pcm_comm; eauto.
    - intros. prod_crush. inv H.
      + inv H0. edestruct @fsim_match_external as (w & x & Hw & Hx & Ha & HH). apply X1; eauto.
        apply H1. instantiate (1 := (_, _)). constructor; cbn; eauto.
        destruct w as (X & Y). inv Ha. clear H0 Hse.
        cbn in *. prod_crush.
        eexists (X, _), (_, (_, _)). repeat split; eauto.
        constructor. eauto.
        intros. prod_crush. inv H3. inv H0. prod_crush.
        edestruct HH as (? & ? & ? & ?).
        instantiate (2 := (_, _, _)). instantiate (1 := (_, _, _)). cbn.
        eexists (_, _). split; eauto. instantiate (1 := (_, _)). split; eauto. reflexivity.
        prod_crush. eexists (index_l _), (state_l _ _).
        split; constructor; eauto.
      + inv H0. edestruct @fsim_match_external as (w & x & Hw & Hx & Ha & HH). apply X2; eauto.
        apply H1. instantiate (1 := (_, _)). constructor; cbn; eauto.
        destruct w as (X & Y). inv Ha. clear H0 Hse.
        cbn in *. prod_crush.
        eexists (X, _), (_, (_, _)). repeat split; eauto.
        constructor. eauto.
        inv Hx. split; eauto. cbn in ABS. split_hyps.
        eexists _, _. repeat split; eauto. apply pcm_comm; eauto.
        intros. prod_crush. inv H3. inv H0. prod_crush.
        inv H3. cbn in ABS. split_hyps.
        edestruct HH as (? & ? & ? & ?).
        instantiate (2 := (_, _, _)). instantiate (1 := (_, _, _)). cbn.
        eexists (_, _). split; eauto.
        econstructor; eauto. eexists _, _. repeat split; eauto. apply pcm_comm; eauto.
        instantiate (1 := (_, _)). split; eauto. reflexivity.
        prod_crush. eexists (index_r _), (state_r _ _).
        split; constructor; eauto.
    - intros. inv H0.
      + inv H. edestruct @fsim_simulation as (x & A & B & C). apply X1; eauto.
        instantiate (3 := (_, _)). instantiate (1 := (_, _)).
        constructor; eauto. eauto. destruct A.
        eexists (index_l _), (state_l _ _). split.
        * destruct B; [ left | right ].
          -- apply plus_internal_l. instantiate (1 := s).
             eapply lifting_step_plus_inv in p. apply p.
          -- split. eapply star_internal_l.
             destruct a. eapply lifting_step_star_inv in H. apply H.
             constructor. apply a.
        * constructor. replace k2f with k. apply C.
          destruct B.
          -- eapply lifting_step_plus_inv in H. easy.
          -- destruct H. eapply lifting_step_star_inv in H. easy.
      + inv H. edestruct @fsim_simulation as (x & A & B & C). apply X2; eauto.
        instantiate (3 := (_, _)). instantiate (1 := (_, _)).
        constructor; eauto. eauto. destruct A.
        eexists (index_r _), (state_r _ _). split.
        * destruct B; [ left | right ].
          -- apply plus_internal_r. instantiate (1 := s).
             eapply lifting_step_plus_inv in p. apply p.
          -- split. eapply star_internal_r.
             destruct a. eapply lifting_step_star_inv in H. apply H.
             constructor. apply a.
        * constructor. replace k1f with k. apply C.
          destruct B.
          -- eapply lifting_step_plus_inv in H. easy.
          -- destruct H. eapply lifting_step_star_inv in H. easy.
  Qed.

End COMP.

Lemma tens_fsim {K1s K2s K1f K2f} (R1: abrel K1s K1f) (R2: abrel K2s K2f)
      L1s L2s Ls L1f L2f Lf
  (HL1: forward_simulation (abrel_pcc R1) (abrel_pcc R1) L1s L1f)
  (HL2: forward_simulation (abrel_pcc R2) (abrel_pcc R2) L2s L2f)
  (Hs: tens_semantics L1s L2s = Some Ls)
  (Hf: tens_semantics L1f L2f = Some Lf)
  (F1: Frameable (K2:=K2f) L1f) (F2: Frameable (K2:=K1f) L2f):
  forward_simulation (abrel_pcc (abrel_tens R1 R2)) (abrel_pcc (abrel_tens R1 R2)) Ls Lf.
Proof.
  eapply lift_sim' with (S:=R2) in HL1.
  eapply lift_sim' with (S:=R1) in HL2.
  unfold tens_semantics in Hs, Hf.
  destruct (link (skel L1s) (skel L2s)) eqn: HLK1; inv Hs.
  destruct (link (skel L1f) (skel L2f)) eqn: HLK2; inv Hf.
  destruct HL1 as [X1].
  destruct HL2 as [X2].
  constructor.
  eapply Forward_simulation
    with (torder R1 R2 X1 X2) (fun se1 se2 '(m, se) => tmatch R1 R2 X1 X2 se m).
  - pose proof (fsim_skel X1). pose proof (fsim_skel X2).
    cbn in *. congruence.
  - pose proof (fsim_footprint X1). pose proof (fsim_footprint X2).
    cbn in *. intros i. rewrite H. rewrite H0. reflexivity.
  - intros. destruct wB as [m se].
    inv H. rename se2 into se.
    eapply tens_fsim'. constructor; eauto.
    + eapply Genv.valid_for_linkorder; eauto.
      eapply link_linkorder in HLK1; apply HLK1.
    + eapply Genv.valid_for_linkorder; eauto.
      eapply link_linkorder in HLK1; apply HLK1.
  - clear - X1 X2. intros x. destruct x.
    + induction (fsim_order_wf X1 f).
      constructor. intros. inv H1. eauto.
    + induction (fsim_order_wf X2 f).
      constructor. intros. inv H1. eauto.
  - apply F2.
  - apply F1.
Qed.
