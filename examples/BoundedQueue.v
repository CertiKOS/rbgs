Require Import Classical.
Require Import Program.Equality.
Require Import LogicalRelations.
Require Import Poset.
Require Import Lattice.
Require Import Downset.
Require Import IntStrat.
Require Import Classical_Prop.
Require Import Coqlib.

From compcert.common Require Import LanguageInterface Smallstep Globalenvs.
From compcert.clightp Require Import Example.
Import Memory Values Integers ListNotations.
Require Import CompCertStrat.
Close Scope list.

Lemma rsq_de {E F U} (τ: strat E F ready) (u0: U):
  rsq (de u0) (de u0) rs_ready τ (tstrat tp_ready τ slens_id).
Proof.
Admitted.

(** * Example *)

Ltac eprod_crush :=
  repeat
    (match goal with
     | [ H: ?a * ?b |- _ ] => destruct H;cbn [fst snd] in *; subst
     | [ H: (?a * ?b)%embed |- _ ] => destruct H;cbn [fst snd] in *; subst
     | [ H: (?a, ?b) = (?c, ?d) |- _ ] => inv H
     | [ H: (?x * ?y)%rel _ _ |- _] => destruct H; cbn [fst snd] in *; subst
     | [ H: ?x /\ ?y |- _] => destruct H
     | [ H: (exists _, _) |- _] => destruct H
     | [ H: unit |- _] => destruct H
     end).

Section LIFT_CONVERT.

  Context (li: language_interface) (S: Type).

  Inductive lift_convert_mq: op (li @ S) -> op (Lifting.lifted_li S li) -> Prop :=
  | lift_convert_mq_intro q se (s: S):
    lift_convert_mq ((se, q)%embed, s) (se, Datatypes.pair q s)%embed.
  Inductive lift_convert_mr: forall (m1: op (li @ S)) (m2: op (Lifting.lifted_li S li)), ar m1 -> ar m2 -> Prop :=
  | lift_convert_mr_intro m1 m2 r s:
    lift_convert_mr m1 m2 (r, s) (r, s).

  Definition lift_convert_rel:
    esig_rel (li @ S) (Lifting.lifted_li S li) :=
      {| match_query := lift_convert_mq; match_reply := lift_convert_mr |}.

End LIFT_CONVERT.

Lemma rsq_lift_convert sk {li S} L:
  rsq (lift_convert_rel li S) (lift_convert_rel li S)
      rs_ready ((lts_strat_sk sk L) @ S)%strat
      (lts_strat_sk sk (Lifting.lifted_semantics S L)).
Admitted.

Definition join_conv : conv (li_c @ Mem.mem) li_c :=
  vcomp (lift_convert_rel li_c Mem.mem) join_cc.

(** * Strategy-level definitions *)

Definition val := Values.val.
Definition N := Example.N.

Inductive bq_op := enq: val -> bq_op | deq: bq_op.
Canonical Structure E_bq : esig :=
  {|
    op := bq_op;
    ar op := match op with | enq _ => unit | deq => val end;
  |}.
Inductive rb_op :=
| set : nat -> val -> rb_op | get : nat -> rb_op
| inc1 : rb_op | inc2 : rb_op.
Canonical Structure E_rb : esig :=
  {|
    op := rb_op;
    ar op :=
      match op with
      | set _ _ => unit | get _ => val | inc1 | inc2 => nat
      end;
  |}.

Definition M_enq_play (v: val) (i: nat): @play E_rb E_bq ready :=
  oq (enq v) ::
  pq inc2 ::
  @oa _ _ _ inc2 i ::
  pq (set i v) ::
  @oa _ _ _ (set i v) tt ::
  @pa _ _ (enq v) tt :: pnil_ready.
Definition M_deq_play (v: val) (i: nat): @play E_rb E_bq ready :=
  oq deq ::
  pq inc1 ::
  @oa _ _ _ inc1 i ::
  pq (get i) ::
  @oa _ _ _ (get i) v ::
  @pa _ _ deq v :: pnil_ready.
Definition M_enq_strat: strat E_rb E_bq ready := sup v, sup {i | (i < N)%nat}, down (M_enq_play v i).
Definition M_deq_strat: strat E_rb E_bq ready := sup {v | Cop.val_casted v tint}, sup { i | (i < N)%nat}, down (M_deq_play v i).
Definition M_bq : strat E_rb E_bq ready := closure (join M_enq_strat M_deq_strat).

Definition S_bq : Type := bq_state.
Definition S_rb : Type := rb_state.
Definition bq_rb_rel : rel S_bq S_rb := rb_bq.

Definition L_enq_play (v: val) (q: S_bq): @play 0 (E_bq @ S_bq) ready :=
  oq (enq v, q) :: @pa _ _ (enq v, q) (tt, app q (cons v nil)) :: pnil_ready.
Definition L_deq_play (v: val) (q: S_bq): @play 0 (E_bq @ S_bq) ready :=
  oq (deq, cons v q) :: @pa _ _ (deq, cons v q) (v, q) :: pnil_ready.
Definition L_enq_strat: strat 0 (E_bq @ S_bq) ready :=
  sup {v | Cop.val_casted v tint}, sup {q | (List.length q < N)%nat}, down (L_enq_play v q).
Definition L_deq_strat: strat 0 (E_bq @ S_bq) ready :=
  sup {v | Cop.val_casted v tint}, sup q, down (L_deq_play v q).
Definition L_bq : strat empty_sig (E_bq @ S_bq) ready := closure (join L_enq_strat L_deq_strat).

Definition L_inc1_play (f: nat -> val) (c1 c2: nat): @play 0 (E_rb @ S_rb) ready :=
  oq (inc1, (f, c1, c2)) :: @pa _ _ (inc1, (f, c1, c2)) (c1, (f, ((S c1) mod N)%nat, c2)) :: pnil_ready.
Definition L_inc2_play (f: nat -> val) (c1 c2: nat): @play 0 (E_rb @ S_rb) ready :=
  oq (inc2, (f, c1, c2)) :: @pa _ _ (inc2, (f, c1, c2)) (c2, (f, c1, ((S c2) mod N)%nat)) :: pnil_ready.
Definition L_get_play (f: nat -> val) (c1 c2: nat) (i: nat): @play 0 (E_rb @ S_rb) ready :=
  oq (get i, (f, c1, c2)) :: @pa _ _ (get i, (f, c1, c2)) (f i, (f, c1, c2)) :: pnil_ready.
Definition L_set_play (f: nat -> val) (c1 c2: nat) (i: nat) (v: val): @play 0 (E_rb @ S_rb) ready :=
  oq (set i v, (f, c1, c2)) :: @pa _ _ (set i v, (f, c1, c2)) (tt , (fun j => if Nat.eq_dec i j then v else f j, c1, c2)) :: pnil_ready.
Definition L_inc1_strat: strat 0 (E_rb @ S_rb) ready := sup f, sup c1, sup c2, down (L_inc1_play f c1 c2).
Definition L_inc2_strat: strat 0 (E_rb @ S_rb) ready := sup f, sup c1, sup c2, down (L_inc2_play f c1 c2).
Definition L_get_strat: strat 0 (E_rb @ S_rb) ready := sup { f | forall n, Cop.val_casted (f n) tint }, sup c1, sup c2, sup i, down (L_get_play f c1 c2 i).
Definition L_set_strat: strat 0 (E_rb @ S_rb) ready := sup f, sup c1, sup c2, sup i, sup v, down (L_set_play f c1 c2 i v).
Definition L_rb : strat empty_sig (E_rb @ S_rb) ready := closure (join (join L_inc1_strat L_inc2_strat) (join L_get_strat L_set_strat)).

Local Instance L_rb_regular : Regular L_rb. Admitted.

Local Transparent join.

(* L_bq ⊑ (M_bq @ S_rb) ∘ L_rb *)
Lemma ϕ1 :
  rsq conv_id (tconv conv_id bq_rb_rel) rs_ready
    L_bq (compose cpos_ready (M_bq @ S_rb)%strat L_rb).
Proof.
  unfold M_bq. rewrite <- closure_lift.
  rewrite <- @closure_comp_ref2. 2: typeclasses eauto.
  apply rsq_closure; eauto with typeclass_instances.
  intros s (i & Hs). destruct i.
  - (* enq *)
    destruct Hs as ((v & Hv) & (bq & Hbq) & Hs). cbn in Hs. rewrite Hs. clear Hs.
    setoid_rewrite tstrat_sup_l. setoid_rewrite compose_sup_l.
    apply rsp_sup_exist. exists true.
    unfold L_enq_play. apply rsp_oq.
    { repeat econstructor. Unshelve. refine v. exists 0%nat. lia. }
    intros (q & rb) (Hq1 & Hq2).
    cbn in Hq1. dependent destruction Hq1.
    cbn in Hq2. dependent destruction Hq2.
    destruct rb as [[f c1] c2].
    set (fx := (fun j : nat => if Nat.eq_dec c2 j then v else f j)).
    eapply rsp_pa with (r2 := (tt, (fx, c1, S c2 mod N)%nat)).
    { (* match reply *)
      intros HX. Local Opaque N. cbn in HX.
      destruct HX as (? & ? & HX). clear - HX Hv Hbq. destruct HX as [HX|HX].
      - dependent destruction HX. congruence.
      - dependent destruction HX. apply HA.
        apply refine_correct2; eauto. }
    apply rsp_ready.
    cbn - [compose tstrat M_enq_strat].
    eexists _, _. repeat apply conj.
    3: { (* incoming question *) apply comp_oq.
      (* call inc *) apply comp_lq. apply comp_ra.
      (* call set *) apply comp_lq. apply comp_ra.
      (* return *) apply comp_la. instantiate (1 := pnil_ready). apply comp_ready. }
    2: { eapply closure_has_cons; [ | | apply seq_comp_oq; apply seq_comp_pa; eauto ].
      2: eapply closure_has_cons; [ | | apply seq_comp_oq; apply seq_comp_pa; eauto ].
      3: eauto.
      - exists true. exists false. cbn. exists f, c1, c2. repeat econstructor.
      - exists false. exists false. cbn. exists f, c1, (S c2 mod N)%nat, c2, v. cbn. repeat econstructor. }
    eexists _, _. repeat apply conj.
    + repeat econstructor.
    + cbn. assert (Hc2: (c2 < N)%nat). { inv HQ. apply Nat.mod_upper_bound. lia. }
      exists v, (exist _ c2 Hc2). cbn. reflexivity.
    + cbn. repeat econstructor.
  - (* deq *)
    destruct Hs as (v & bq & Hs). cbn in Hs. rewrite Hs. clear Hs.
    setoid_rewrite tstrat_sup_l. setoid_rewrite compose_sup_l.
    apply rsp_sup_exist. exists false.
    unfold L_deq_play. apply rsp_oq.
    { repeat econstructor. Unshelve. refine v.
      exists 0%nat. Local Transparent N. unfold N. unfold Example.N. lia. }
    Local Opaque N.
    intros (q & rb) (Hq1 & Hq2).
    cbn in Hq1. dependent destruction Hq1.
    cbn in Hq2. dependent destruction Hq2.
    destruct rb as [[f c1] c2].
    eapply rsp_pa with (r2 := (f c1, (f, (S c1 mod N)%nat, c2))).
    { (* match reply *)
      intros HX. cbn in HX.
      destruct HX as (? & ? & HX). apply refine_correct1 in HQ.
      destruct HX as [HX|HX].
      - dependent destruction HX. destruct HQ. congruence.
      - dependent destruction HX. apply HA. apply HQ. }
    apply rsp_ready.
    cbn - [compose tstrat M_enq_strat].
    eexists _, _. repeat apply conj.
    3: { (* incoming question *) apply comp_oq.
      (* call inc *) apply comp_lq. apply comp_ra.
      (* call get *) apply comp_lq. apply comp_ra.
      (* return *) apply comp_la. instantiate (1 := pnil_ready). apply comp_ready. }
    2: { eapply closure_has_cons; [ | | apply seq_comp_oq; apply seq_comp_pa; eauto ].
      2: eapply closure_has_cons; [ | | apply seq_comp_oq; apply seq_comp_pa; eauto ].
      3: eauto.
      - exists true. exists true. cbn. exists f, c1, c2. repeat econstructor.
      - exists false. exists true. cbn.
        assert (Hf: forall i : nat, Cop.val_casted (f i) tint).
        { inv HQ; eauto. }
        eexists (exist _ f Hf), (S c1 mod N)%nat, c2, c1.
        cbn. repeat econstructor. }
    eexists _, _. repeat apply conj.
    + repeat econstructor.
    + cbn.
      assert (Hfc: Cop.val_casted (f c1) tint). { inv HQ; eauto. }
      assert (Hc1: (c1 < N)%nat). { inv HQ; eauto. }
      exists (exist _ (f c1) Hfc), (exist _ c1 Hc1). reflexivity.
    + cbn. repeat econstructor.
Qed.

Definition rb0: rb_state := (fun _ => Vint (Int.zero), 0, 0)%nat.
Definition bq0: bq_state := nil.

Definition Π_rb := encap rb0 L_rb.
Definition Π_bq := encap bq0 L_bq.

(* Π_bq ⊑ M_bq ∘ Π_rb *)
Lemma ϕ1' : Π_bq [= compose cpos_ready M_bq Π_rb.
Proof.
  unfold Π_bq, Π_rb. unfold encap.
  rewrite <- compose_assoc with (p1 := cpos_ready) (p2 := cpos_ready).
  rewrite <- encap_lift.
  rewrite compose_assoc with (p3 := cpos_ready) (p4 := cpos_ready).
  apply rsq_id_conv with (p := rs_ready).
  eapply rsq_comp. constructor.
  (* deterministic *) admit.
  (* deterministic *) admit.
  apply representation_independence with (R := rb_bq).
  { eapply bq_rb_intro with (n := 0%nat).
    Local Transparent N.
    all: eauto; unfold N, Example.N; try lia. }
  apply ϕ1.
Admitted.

(** * Proving strategies are implemented by Clight programs *)

Import Maps Clight Ctypes AST Linking.

Context rbc (HT2: ClightP.transl_program rb_program = Errors.OK rbc).
Definition bqc := BQ.bq_program.
Context sk (Hsk: link (AST.erase_program bqc) (AST.erase_program rbc) = Some sk).
Definition se_valid1 se := Genv.valid_for sk se.
Definition sk_bq := skel bq_spec.
Definition sk_rb := AST.erase_program rbc.
Lemma linkorder_bq: linkorder sk_bq sk.
Proof. edestruct @link_linkorder. apply Hsk. apply H. Qed.
Lemma linkorder_rb: linkorder sk_rb sk.
Proof. edestruct @link_linkorder. apply Hsk. apply H0. Qed.
Lemma se_valid_sk_bq se: se_valid1 se -> Genv.valid_for sk_bq se.
Proof.
  unfold se_valid1. intros H.
  eapply Genv.valid_for_linkorder; eauto. apply linkorder_bq.
Qed.
Lemma se_valid_sk_rb se: se_valid1 se -> Genv.valid_for sk_rb se.
Proof.
  unfold se_valid1. intros H.
  eapply Genv.valid_for_linkorder; eauto. apply linkorder_rb.
Qed.

Local Definition embed_lts_with_sk {liA liB} (L: semantics liA liB) := lts_strat_sk sk L.
Local Coercion embed_lts_with_sk : semantics >-> poset_carrier.

Context (penv0 : PEnv.penv) (Hpenv0 : rb_penv_rel rb0 penv0).
Context (m0 : Mem.mem) (arr_b cnt1_b cnt2_b: positive).
Definition se_valid2 se :=
  Genv.find_symbol se arr_id = Some arr_b /\
  Genv.find_symbol se cnt1_id = Some cnt1_b /\
  Genv.find_symbol se cnt2_id = Some cnt2_b.
Definition id_in_penv id := id = arr_id \/ id = cnt1_id \/ id = cnt2_id.
Definition ce := ClightP.ClightP.prog_comp_env rb_program.
Context (Hm0: forall se, se_valid2 se -> PEnv.penv_mem_match ce se penv0 m0)
  (Hse_valid2_inv: forall se pe m, PEnv.penv_mem_match ce se pe m -> se_valid2 se).
Context (match_rb_id_in_penv:
  forall rb pe id v, rb_penv_rel rb pe -> pe!id = Some v -> id_in_penv id).

Lemma se_valid2_in_penv_agree se1 se2 id:
  se_valid2 se1 -> se_valid2 se2 -> id_in_penv id ->
  Genv.find_symbol se1 id = Genv.find_symbol se2 id.
Proof.
  intros (A & B & C) (D & E & F) [H1|[H1|H1]]; congruence.
Qed.

(** ** Bq correctness *)

Section C_CONV.
  Import ListNotations.
  Local Open Scope embed_scope.
  Import Values Integers Memory.

  Inductive E_bq_conv_mq : op E_bq -> op li_c -> Prop :=
  | E_bq_conv_mq_enq v vf sg (se: Genv.symtbl) m b
    (HVF: vf = Vptr b Ptrofs.zero) (HB: Genv.find_symbol se enq_id = Some b)
    (HLE: Ple (Genv.genv_next se) (Mem.nextblock m))
    (HV: Cop.val_casted v tint) (HSG: sg = enq_sg)
    (HSE1: se_valid1 se) (HSE2: se_valid2 se) (HFLAG: Mem.alloc_flag m = true):
    E_bq_conv_mq (enq v) (se, cq vf sg [ v ] m)
  | E_bq_conv_mq_deq vf sg (se: Genv.symtbl) m b
    (HVF: vf = Vptr b Ptrofs.zero) (HB: Genv.find_symbol se deq_id = Some b)
    (HLE: Ple (Genv.genv_next se) (Mem.nextblock m)) (HSG: sg = deq_sg)
    (HSE1: se_valid1 se) (HSE2: se_valid2 se) (HFLAG: Mem.alloc_flag m = true):
    E_bq_conv_mq deq (se, cq vf sg [ ] m).

  Inductive E_bq_conv_mr : forall (m1: op E_bq) (m2: op li_c), ar m1 -> ar m2 -> Prop :=
  | E_bq_conv_mr_enq v se q m (HM: m = cq_mem q):
    E_bq_conv_mr (enq v) (se, q) tt (cr Vundef m)
  | E_bq_conv_mr_deq v se q m (HM: m = cq_mem q):
    E_bq_conv_mr deq (se, q) v (cr v m).

  Inductive E_rb_conv_mq : op E_rb -> op li_c -> Prop :=
  | E_rb_conv_mq_set i v vf sg (se: Genv.symtbl) c_i m b
    (HVF: vf = Vptr b Ptrofs.zero) (HB: Genv.find_symbol se set_id = Some b)
    (HLE: Ple (Genv.genv_next se) (Mem.nextblock m))
    (HI: c_i = Vint (Int.repr (Z.of_nat i))) (HIN: (i < N)%nat)
    (HFLAG: Mem.alloc_flag m = true) (HSE1: se_valid1 se)
    (HV: Cop.val_casted v tint) (HSG: sg = set_sg) (HSE: se_valid2 se):
    E_rb_conv_mq (set i v) (se, cq vf sg [ c_i; v ] m)
  | E_rb_conv_mq_get i vf sg (se: Genv.symtbl) c_i m b
    (HVF: vf = Vptr b Ptrofs.zero) (HB: Genv.find_symbol se get_id = Some b)
    (HLE: Ple (Genv.genv_next se) (Mem.nextblock m)) (HSE1: se_valid1 se)
    (HI: c_i = Vint (Int.repr (Z.of_nat i))) (HIN: (i < N)%nat)
    (HSG: sg = get_sg) (HSE: se_valid2 se) (HFLAG: Mem.alloc_flag m = true):
    E_rb_conv_mq (get i) (se, cq vf sg [ c_i ] m)
  | E_rb_conv_mq_inc1 vf sg (se: Genv.symtbl) m b
    (HVF: vf = Vptr b Ptrofs.zero) (HB: Genv.find_symbol se inc1_id = Some b)
    (HLE: Ple (Genv.genv_next se) (Mem.nextblock m)) (HSE1: se_valid1 se)
    (HSG: sg = inc1_sg) (HSE: se_valid2 se) (HFLAG: Mem.alloc_flag m = true):
    E_rb_conv_mq inc1 (se, cq vf sg [ ] m)
  | E_rb_conv_mq_inc2 vf sg (se: Genv.symtbl) m b
    (HVF: vf = Vptr b Ptrofs.zero) (HB: Genv.find_symbol se inc2_id = Some b)
    (HLE: Ple (Genv.genv_next se) (Mem.nextblock m)) (HSE1: se_valid1 se)
    (HSG: sg = inc2_sg) (HSE: se_valid2 se) (HFLAG: Mem.alloc_flag m = true):
    E_rb_conv_mq inc2 (se, cq vf sg [ ] m).

  Inductive E_rb_conv_mr : forall (m1: op E_rb) (m2: op li_c), ar m1 -> ar m2 -> Prop :=
  | E_rb_conv_mr_set i v se q m (HM: m = cq_mem q):
    E_rb_conv_mr (set i v) (se, q) tt (cr Vundef m)
  | E_rb_conv_mr_get i v se q m (HM: m = cq_mem q):
    E_rb_conv_mr (get i) (se, q) v (cr v m)
  | E_rb_conv_mr_inc1 se q c_i i m (HM: m = cq_mem q)
      (HI: c_i = Vint (Int.repr (Z.of_nat i))):
    E_rb_conv_mr inc1 (se, q) i (cr c_i m)
  | E_rb_conv_mr_inc2 se q c_i i m (HM: m = cq_mem q)
      (HI: c_i = Vint (Int.repr (Z.of_nat i))):
    E_rb_conv_mr inc2 (se, q) i (cr c_i m).

End C_CONV.

Definition E_bq_conv : esig_rel E_bq li_c :=
  {| match_query := E_bq_conv_mq; match_reply := E_bq_conv_mr |}.
Definition E_rb_conv : esig_rel E_rb li_c :=
  {| match_query := E_rb_conv_mq; match_reply := E_rb_conv_mr |}.

Local Hint Constructors E_rb_conv_mq E_rb_conv_mr : core.
Local Hint Constructors bq_initial_state bq_at_external bq_final_state bq_step bq_after_external : core.

Lemma ϕ_bq0 : rsq E_rb_conv E_bq_conv rs_ready M_bq bq_spec.
Proof.
  apply rsq_closure; eauto with typeclass_instances.
  intros s (i & Hs). destruct i.
  - (* enq *)
    cbn in Hs. destruct Hs as (v & (i & Hi) & Hs). rewrite Hs. clear Hs.
    unfold M_enq_play. apply rsp_oq.
    { repeat econstructor. }
    intros cq Hq. cbn in Hq. dependent destruction Hq. inv HM.
    exploit inc2_block. apply se_valid_sk_bq. apply HSE1.
    intros (b1 & Hb1 & Hbb1).
    eapply rsp_pq with (m2 := (se, cq (Vptr b1 Ptrofs.zero) inc2_sg nil m)%embed).
    { constructor. cbn; eauto. }
    eapply rsp_oa.
    { eapply lts_strat_has_intro; cbn; eauto.
      eapply state_strat_has_internal. { apply star_one. cbn; eauto. }
      eapply state_strat_has_external_suspend; cbn; eauto. }
    cbn. intros r Hr. destruct r as [c_i rm].
    apply esig_rel_mr_elim in Hr; cbn; eauto.
    cbn in Hr. dependent destruction Hr.
    rewrite regular_conv; eauto.
    2: { constructor. econstructor; eauto. }
    2: { apply esig_rel_mr_intro. constructor; eauto. }
    exploit set_block. apply se_valid_sk_bq. apply HSE1.
    intros (b2 & Hb2 & Hbb2).
    eapply rsp_pq with
      (m2 := (se, cq (Vptr b2 Ptrofs.zero) set_sg [Vint (Int.repr (Z.of_nat i)); v] rm)%embed).
    { constructor. cbn; eauto. }
    eapply rsp_oa.
    { eapply lts_strat_has_intro; cbn; eauto.
      eapply state_strat_has_internal. { apply star_one. cbn; eauto. }
      eapply state_strat_has_external; cbn; eauto.
      eapply state_strat_has_internal. { apply star_one. cbn; eauto. }
      eapply state_strat_has_external_suspend; cbn; eauto. }
    cbn. intros r2 Hr2.
    apply esig_rel_mr_elim in Hr2. 2: { cbn; eauto. }
    cbn in Hr2. dependent destruction Hr2.
    eapply rsp_pa with (cr Vundef rm).
    { apply esig_rel_mr_intro. cbn; econstructor. eauto. }
    apply rsp_ready. cbn.
    eapply lts_strat_has_intro; cbn; eauto.
    eapply state_strat_has_internal. { apply star_one. cbn; eauto. }
    eapply state_strat_has_external; cbn; eauto.
    eapply state_strat_has_internal. { apply star_one. cbn; eauto. }
    eapply state_strat_has_external; cbn; eauto.
    eapply state_strat_has_internal. { apply star_one. cbn; eauto. }
    eapply state_strat_has_final; cbn; eauto.
  - (* deq *)
    cbn in Hs. destruct Hs as ((v & Hv) & (i & Hi) & Hs). rewrite Hs. clear Hs.
    unfold M_enq_play. apply rsp_oq.
    { repeat econstructor. }
    intros cq Hq. cbn in Hq. dependent destruction Hq. inv HM.
    exploit inc1_block. apply se_valid_sk_bq. apply HSE1. 
    intros (b1 & Hb1 & Hbb1).
    eapply rsp_pq with (m2 := (se, cq (Vptr b1 Ptrofs.zero) inc1_sg nil m)%embed).
    { constructor. cbn; eauto. }
    eapply rsp_oa.
    { eapply lts_strat_has_intro; cbn; eauto.
      eapply state_strat_has_internal. { apply star_one. cbn; eauto. }
      eapply state_strat_has_external_suspend; cbn; eauto. }
    cbn. intros r Hr. destruct r as [c_i rm].
    apply esig_rel_mr_elim in Hr; cbn; eauto.
    cbn in Hr. dependent destruction Hr.
    rewrite regular_conv; eauto.
    2: { constructor. econstructor; eauto. }
    2: { apply esig_rel_mr_intro. constructor; eauto. }
    exploit get_block. apply se_valid_sk_bq. apply HSE1.
    intros (b2 & Hb2 & Hbb2).
    eapply rsp_pq with
      (m2 := (se, cq (Vptr b2 Ptrofs.zero) get_sg [Vint (Int.repr (Z.of_nat i))] rm)%embed).
    { constructor. econstructor; eauto. }
    eapply rsp_oa.
    { eapply lts_strat_has_intro; cbn; eauto.
      eapply state_strat_has_internal. { apply star_one. cbn; eauto. }
      eapply state_strat_has_external; cbn; eauto.
      eapply state_strat_has_internal. { apply star_one. cbn; eauto. }
      eapply state_strat_has_external_suspend; cbn; eauto. }
    cbn. intros r2 Hr2.
    apply esig_rel_mr_elim in Hr2. 2: { cbn; eauto. }
    cbn in Hr2. dependent destruction Hr2.
    eapply rsp_pa with (cr v rm).
    { apply esig_rel_mr_intro. cbn; econstructor. eauto. }
    apply rsp_ready. cbn.
    eapply lts_strat_has_intro; cbn; eauto.
    eapply state_strat_has_internal. { apply star_one. cbn; eauto. }
    eapply state_strat_has_external; cbn; eauto.
    eapply state_strat_has_internal. { apply star_one. cbn; eauto. }
    eapply state_strat_has_external; cbn; eauto.
    eapply state_strat_has_internal. { apply star_one. cbn; eauto. }
    eapply state_strat_has_final; cbn; eauto.
Qed.

Definition E_rb_m0_conv_explicit : conv E_rb (li_c @ Mem.mem) := deencap m0 E_rb_conv.
Definition E_bq_m0_conv_explicit : conv E_bq (li_c @ Mem.mem) := deencap m0 E_bq_conv.

Definition E_rb_m0_conv : conv E_rb li_c := vcomp E_rb_m0_conv_explicit join_conv.
Definition E_bq_m0_conv : conv E_bq li_c := vcomp E_bq_m0_conv_explicit join_conv.

Definition ϕ_bq_conv_1 :=
  vcomp (vcomp (deencap m0 E_rb_conv) (lift_convert_rel li_c mem)) join_cc.
Definition ϕ_bq_conv_2 :=
  vcomp (vcomp (deencap m0 E_bq_conv) (lift_convert_rel li_c mem)) join_cc.

Lemma ϕ_bq_with_internals : rsq ϕ_bq_conv_1 ϕ_bq_conv_2 rs_ready M_bq (Clight.semantics2 BQ.bq_program).
Proof.
  eapply rsq_vcomp. constructor. 1-2: admit.
  2: { apply fsim_rsq_sk. admit. apply fp. apply linkorder_bq. }
  eapply rsq_vcomp. constructor. 1-2: admit.
  2: { apply rsq_lift_convert. }
  eapply rsq_vcomp. constructor. 1-2: admit.
  2: apply rsq_de.
  rewrite <- (vcomp_right_id E_rb_conv).
  rewrite <- (vcomp_right_id E_bq_conv).
  eapply rsq_vcomp. constructor. 1-2: admit.
  apply ϕ_bq0. rewrite <- !cc_conv_id.
  apply fsim_rsq_sk. admit.
  apply BQ.bq_correct0. apply linkorder_bq.
Admitted.

(** ** Rb correctness *)

Definition E_rb_S_rb_conv : conv (E_rb @ S_rb) (Lifting.lifted_li rb_state li_c) :=
  vcomp (tconv E_rb_conv conv_id) (lift_convert_rel li_c rb_state).

Global Instance E0_conv_regular {E}:
  RegularConv (@E0_conv E).
Proof. split. intros. easy. Qed.

Local Opaque N.

Local Hint Constructors rb_final_state rb_step rb_initial_state : core.

Lemma ϕ_rb0 : rsq E0_conv E_rb_S_rb_conv rs_ready L_rb rb_spec.
Proof.
  apply rsq_closure; eauto with typeclass_instances.
  intros s (i & Hs). destruct i; destruct Hs as [[|] Hs].
  - (* inc1 *)
    cbn in Hs. destruct Hs as (f & c1 & c2 & Hs). rewrite Hs. clear Hs.
    unfold L_inc1_play. apply rsp_oq.
    { repeat econstructor. }
    intros (se & cq & rb) ((se' & cq' & rb') & (Hq1 & Hq2) & Hq3).
    cbn in *. dependent destruction Hq1. inv HM.
    dependent destruction Hq2. dependent destruction Hq3. inv HM.
    set (c1_i := Vint (Int.repr (Z.of_nat c1))).
    eapply rsp_pa with ((cr c1_i m), (f, (S c1 mod N)%nat, c2)).
    { intros ((se' & cq' & rb') & (Hr1 & Hr2) & Hr3 & Hr4). cbn in *.
      dependent destruction Hr2. dependent destruction Hr3. inv HM.
      specialize (Hr4 ((cr c1_i m), (f, (S c1 mod N)%nat, c2))).
      cbn in Hr4. destruct Hr4 as [(Hra & Hrb & [Hrc | Hrc])|Hr4].
      - xinv Hrc. apply HA. econstructor; eauto.
      - xinv Hrc. easy.
      - xinv Hr4. apply HA. cbn. constructor. }
    apply rsp_ready. cbn.
    econstructor 2; cbn; eauto. 
    econstructor 4. { apply star_one. cbn; eauto. }
    econstructor 3; cbn; eauto.
  - (* inc1 *)
    cbn in Hs. destruct Hs as (f & c1 & c2 & Hs). rewrite Hs. clear Hs.
    unfold L_inc1_play. apply rsp_oq.
    { repeat econstructor. }
    intros (se & cq & rb) ((se' & cq' & rb') & (Hq1 & Hq2) & Hq3).
    cbn in *. dependent destruction Hq1. inv HM.
    dependent destruction Hq2. dependent destruction Hq3. inv HM.
    set (c2_i := Vint (Int.repr (Z.of_nat c2))).
    eapply rsp_pa with ((cr c2_i m), (f, c1, (S c2 mod N)%nat)).
    { intros ((se' & cq' & rb') & (Hr1 & Hr2) & Hr3 & Hr4). cbn in *.
      dependent destruction Hr2. dependent destruction Hr3. inv HM.
      specialize (Hr4 ((cr c2_i m), (f, c1, (S c2 mod N)%nat))).
      cbn in Hr4. destruct Hr4 as [(Hra & Hrb & [Hrc | Hrc])|Hr4].
      - xinv Hrc. apply HA. econstructor; eauto.
      - xinv Hrc. easy.
      - xinv Hr4. apply HA. cbn. constructor. }
    apply rsp_ready. cbn.
    econstructor 2; cbn; eauto.
    econstructor 4. { apply star_one. cbn; eauto. }
    econstructor 3; cbn; eauto.
  - (* get *)
    cbn in Hs. destruct Hs as ((f & Hf) & c1 & c2 & i & Hs). rewrite Hs. clear Hs.
    cbn. unfold L_get_play. apply rsp_oq.
    { repeat econstructor. }
    intros (se & cq & rb) ((se' & cq' & rb') & (Hq1 & Hq2) & Hq3).
    cbn in *. dependent destruction Hq1. inv HM.
    dependent destruction Hq2. dependent destruction Hq3. inv HM.
    eapply rsp_pa with ((cr (f i) m), (f, c1, c2)).
    { intros ((se' & cq' & rb') & (Hr1 & Hr2) & Hr3 & Hr4). cbn in *.
      dependent destruction Hr2. dependent destruction Hr3. inv HM.
      specialize (Hr4 ((cr (f i) m), (f, c1, c2))).
      cbn in Hr4. destruct Hr4 as [(Hra & Hrb & [Hrc | Hrc])|Hr4].
      - xinv Hrc. apply HA. econstructor; eauto.
      - xinv Hrc. easy.
      - xinv Hr4. apply HA. cbn. constructor. }
    apply rsp_ready. cbn.
    econstructor 2; cbn; eauto.
    econstructor 4. { apply star_one. econstructor; eauto. }
    econstructor 3; cbn; eauto.
  - (* set *)
    cbn in Hs. destruct Hs as (f & c1 & c2 & i & v & Hs). rewrite Hs. clear Hs.
    cbn. unfold L_set_play. apply rsp_oq.
    { repeat econstructor. }
    intros (se & cq & rb) ((se' & cq' & rb') & (Hq1 & Hq2) & Hq3).
    cbn in *. dependent destruction Hq1. inv HM.
    dependent destruction Hq2. dependent destruction Hq3. inv HM.
    set (g := fun j => if Nat.eq_dec i j then v else f j).
    eapply rsp_pa with ((cr Vundef m), (g, c1, c2)).
    { intros ((se' & cq' & rb') & (Hr1 & Hr2) & Hr3 & Hr4). cbn in *.
      dependent destruction Hr2. dependent destruction Hr3. inv HM.
      specialize (Hr4 ((cr Vundef m), (g, c1, c2))).
      cbn in Hr4. destruct Hr4 as [(Hra & Hrb & [Hrc | Hrc])|Hr4].
      - xinv Hrc. apply HA. econstructor; eauto.
      - xinv Hrc. easy.
      - xinv Hr4. apply HA. cbn. constructor. }
    apply rsp_ready. cbn.
    econstructor 2; cbn; eauto.
    econstructor 4. { apply star_one. constructor; eauto. }
    econstructor 3; cbn; eauto.
Qed.

Definition E_rb_rb0_conv : conv E_rb (li_c @ S_rb) := deencap rb0 E_rb_conv.
Definition E_rb_rb0_conv' : conv E_rb (Lifting.lifted_li S_rb li_c) :=
  vcomp E_rb_rb0_conv (lift_convert_rel li_c S_rb).

Lemma de_rcnext {E U} (m: op E) n (u u': U):
  rcnext m (m, u) n (n, u') (de u) = de u'.
Proof.
  apply antisymmetry.
  - intros c Hc. cbn in *.
    simple inversion Hc; try congruence.
    apply rcp_cont_inv in H0. eprod_crush. xsubst. inv H0. eauto.
  - intros c Hc. cbn in *. constructor. eauto.
Qed.

Lemma de_vcomp_ref {E F U} (R: conv E F) (u0: U):
  deencap u0 R [= vcomp (de u0) (tconv R conv_id).
Proof.
  intros c Hc. revert R u0 Hc. induction c.
  - intros; cbn in *.
    destruct Hc as (f & Hf1 & Hf2). destruct m2. xinv Hf2.
    exists (m1, u). repeat apply conj; try constructor; eauto.
  - intros. cbn in *.
    destruct Hc as (f & Hf1 & Hf2 & Hf3). destruct m2. xinv Hf2.
    cbn in *. destruct n2.
    exists (m1, u). repeat apply conj. 1-3: try econstructor; eauto.
    cbn. intros [x y]. apply not_imply_or. intros Hr.
    repeat apply conj; eauto.
    apply not_imply_or. intros Hr1.
    econstructor. intros <-. specialize (Hf3 a) as [Hf3|Hf3].
    + apply Hr. constructor. congruence.
    + simple inversion Hf3; try congruence.
      apply rcp_forbid_inv in H1. eprod_crush. xsubst. inv H0. easy.
  - intros R u0 Hc. cbn in *.
    destruct Hc as (f & Hf1 & Hf2 & Hf3). destruct m2. xinv Hf2.
    cbn in *. destruct n2.
    exists (m1, u). repeat apply conj. 1-3: try econstructor; eauto.
    cbn. intros [x y]. apply not_imply_or. intros Hr.
    apply not_imply_or. intros Hr1.
    apply not_and_or in Hr1 as [Hr1|Hr1]. easy.
    apply not_and_or in Hr1 as [Hr1|Hr1]. exfalso. apply Hr1. constructor.
    apply not_or_and in Hr1 as [Hr1 Hr2].
    rewrite @rcnext_tconv; eauto.
    rewrite (regular_conv (R := conv_id)); eauto. 2: constructor.
    assert (x = n1). { apply NNPP. intros Hx. apply Hr. constructor. congruence. }
    subst.
    specialize (Hf3 a) as [A|[A|A]]; try easy.
    + exfalso. simple inversion A; try congruence.
      apply rcp_forbid_inv in H1. eprod_crush. xsubst. inv H0. easy.
    + rewrite de_rcnext in A. rewrite de_rcnext. apply IHc.
      assert (y = u0). apply NNPP. intros Hx. apply Hr2. constructor. eauto.
      subst. eauto.
Qed.

Lemma ϕ_rb1 : rsq E0_conv E_rb_rb0_conv' rs_ready Π_rb rb_spec.
Proof.
  unfold E_rb_rb0_conv', E_rb_rb0_conv, E_rb_S_rb_conv.
  rewrite de_vcomp_ref.
  rewrite vcomp_assoc.
  rewrite <- (vcomp_left_id (@E0_conv li_c)).
  eapply rsq_vcomp. constructor. admit. admit.
  apply deencap_rsq. apply ϕ_rb0.
Admitted.

Definition ϕ_rb_conv := vcomp (vcomp E_rb_rb0_conv' rb_cc) (ClightP.pin ce).

Lemma ϕ_rb_with_internals : rsq E0_conv ϕ_rb_conv rs_ready Π_rb (Clight.semantics2 rbc).
Proof.
  unfold ϕ_rb_conv. erewrite E0_conv_vcomp.
  eapply rsq_vcomp. constructor. admit. admit.
  2: { eapply fsim_rsq_sk. admit.
       apply ClightP.transl_program_correct. apply HT2.
       cbn. erewrite ClightP.clightp_skel_correct.
       apply linkorder_rb. apply HT2. }
  erewrite E0_conv_vcomp. eapply rsq_vcomp. constructor. admit. admit.
  2: { eapply fsim_rsq_sk. admit. apply rb_correct2.
       cbn. erewrite ClightP.clightp_skel_correct.
       apply linkorder_rb. apply HT2. }
  apply ϕ_rb1.
Admitted.

(** ** Putting things together *)

Inductive rb_m_mq : op (li_c @ S_rb) -> op (li_c @ mem) -> Prop :=
| rb_m_mq_intro rb m q se pe
    (HRB: rb_penv_rel rb pe) (HM: PEnv.penv_mem_match ce se pe m):
  rb_m_mq ((se, q)%embed, rb) ((se, q)%embed, m).
Inductive rb_m_mr (m1: op (li_c @ S_rb)) (m2: op (li_c @ mem)): ar m1 -> ar m2 -> Prop :=
| rb_m_mr_intro rb m r se q pe (HRB: rb_penv_rel rb pe)
    (HM: PEnv.penv_mem_match ce se pe m):
  (se, q)%embed = fst m1 ->
  rb_m_mr m1 m2 (r, rb) (r, m).
Definition rb_m_esig_rel : esig_rel (li_c @ S_rb) (li_c @ mem) :=
  {| match_query := rb_m_mq; match_reply := rb_m_mr |}.

Definition m_rb_ref:
  vcomp E_rb_conv (de m0) [= vcomp (vcomp E_rb_conv (de rb0)) rb_m_esig_rel.
Proof.
  cbn. intros c.
  assert (rb_penv_rel rb0 penv0 /\
            forall se, se_valid2 se -> PEnv.penv_mem_match ce se penv0 m0) as H.
  { split. apply Hpenv0. intros se Hse. apply Hm0. eauto. }
  revert H. generalize rb0 penv0 m0. induction c.
  - intros rb pe m [Hpe1 Hpe2].
    cbn. intros ((se & q) & Hq1 & Hq2). xinv Hq1. xinv Hq2.
    exists ((se, q)%embed, rb). split.
    2: { constructor. econstructor; eauto. xinv HM; eauto. }
    exists (se, q)%embed. split. constructor. eauto. constructor.
  - intros rb pe m [Hpe1 Hpe2].
    cbn. intros ((se & q) & Hq1 & Hq2 & Ha). xinv Hq1. xinv Hq2.
    exists ((se, q)%embed, rb). split.
    exists (se, q)%embed. split. constructor. eauto. constructor.
    split. { constructor. econstructor; eauto. xinv HM; eauto. }
    intros [cr rb1]. apply or_commut. apply not_imply_or. intros Hr.
    exists (se, q)%embed. split. { constructor. eauto. }
    split. { constructor. }
    intros cr1. apply or_commut. apply not_imply_or. intros Hr1.
    specialize (Ha cr1) as [Ha|Ha]; eauto.
    eapply esig_rel_mr_elim in Hr.
    2: { econstructor; eauto. xinv HM; eauto. }
    xinv Hr. cbn in *. inv H2.
    xinv Ha. constructor. cbn. eauto.
    intros Hx. apply Hr1. constructor. eauto.
  - intros rb pe m [Hpe1 Hpe2].
    cbn. intros ((se & q) & Hq1 & Hq2 & Ha). xinv Hq1. xinv Hq2.
    exists ((se, q)%embed, rb). split.
    exists (se, q)%embed. split. constructor. eauto. constructor.
    split. { constructor. econstructor; eauto. xinv HM; eauto. }
    intros [cr rb1]. apply not_imply_or. intros Hr.
    apply not_imply_or. intros Hr1.
    eapply esig_rel_mr_elim in Hr1.
    2: { econstructor; eauto. xinv HM; eauto. }
    xinv Hr1. cbn in *. inv H2.
    specialize (Ha cr) as [Ha|[Ha|Ha]].
    + exfalso. xinv Ha. apply Hr.
      exists (se, q)%embed. split. { constructor. eauto. }
      split. { constructor. }
      intros cr1. apply or_commut. apply not_imply_or.
      intros Ha. constructor; eauto.
      intros Hra. apply Ha. constructor. intros <-. easy.
    + exfalso. xinv Ha. easy.
    + assert (Hrc1: rcnext ((se, q)%embed, rb) ((se, q)%embed, m) (cr, rb1) (cr, m2) rb_m_esig_rel = rb_m_esig_rel).
      { apply regular_conv.
        - econstructor. econstructor; eauto. xinv HM; eauto.
        - intros Hx. xinv Hx. apply HA. econstructor; eauto. reflexivity. }
      rewrite Hrc1.
      assert (Hrc2: rcnext (se, q)%embed ((se, q)%embed, m) cr (cr, m2) (de m) = de m2).
      { clear. apply antisymmetry.
        - intros c Hc. cbn in *. xinv Hc. eauto.
        - intros c Hc. constructor. eauto. }
      rewrite Hrc2 in Ha.
      assert (Hrc3: rcnext m1 (se, q)%embed n1 cr E_rb_conv = E_rb_conv).
      { apply regular_conv.
        - constructor. cbn. easy.
        - intros Hra. xinv Hra. apply Hr.
          exists (se, q)%embed. split. { constructor. eauto. }
          split. { constructor. }
          intros cr1. apply or_commut. apply not_imply_or.
          intros Hxa. constructor; eauto.
          intros Hra. apply Hxa. constructor. intros <-. easy. }
      rewrite Hrc3 in Ha.
      assert (Hrc4: rcnext (se, q)%embed ((se, q)%embed, rb) cr (cr, rb1) (de rb) = de rb1).
      { clear. apply antisymmetry.
        - intros c Hc. cbn in *. xinv Hc. eauto.
        - intros c Hc. constructor. eauto. }
      assert (Hrc5: rcnext m1 ((se, q)%embed, rb) n1 (cr, rb1) (vcomp E_rb_conv (de rb)) = vcomp E_rb_conv (de rb1)).
      { apply antisymmetry.
        - intros d Hd. cbn in Hd. cbn.
          eprod_crush. xinv H. cbn in HM. xinv H0. inv H4.
          specialize (H1 cr).
          destruct H1 as [H1|[H1|H1]].
          + exfalso. xinv H1. apply Hr.
            exists (se, q)%embed. split. { constructor. eauto. }
            split. { constructor. }
            intros cr1. apply or_commut. apply not_imply_or.
            intros Hxa. constructor; eauto.
            intros Hra. apply Hxa. constructor. intros <-. easy.
          + exfalso. xinv H1. easy.
          + congruence.
        - intros d Hd. cbn.
          exists (se, q)%embed. split. { constructor. now cbn. }
          split. { constructor. }
          intros cr1. apply not_imply_or. intros Hxa.
          apply not_imply_or. intros Hxb.
          assert (cr = cr1).
          { apply NNPP. intros HA. apply Hxb. constructor. congruence. }
          eapply esig_rel_mr_elim in Hxa.
          2: { cbn. eauto. } subst cr1.
          rewrite Hrc3. rewrite Hrc4. apply Hd. }
      rewrite Hrc5. eapply IHc; eauto.
      split; eauto. intros. clear - HM0 HRB H.
      exploit Hse_valid2_inv. eauto. intros Hx.
      constructor. intros id v Hv.
      inv HM0. specialize (MPE _ _ Hv) as (b & Hb & Hbb).
      exists b. split; eauto.
      rewrite <- Hb. apply se_valid2_in_penv_agree; eauto.
      eapply match_rb_id_in_penv; eauto.
Qed.

Section PIN_NO_JOIN.

  Import Lifting PEnv.
  Inductive pin_query R: Memory.mem * Genv.symtbl -> query (li_c @ penv) -> query (li_c @ mem) -> Prop :=
  | pin_query_intro se m q pe (MPE: R se pe m):
    pin_query R (m, se) (q, pe) (q, m).
  Inductive pin_reply R: Memory.mem * Genv.symtbl -> reply (li_c @ penv) -> reply (li_c @ mem) -> Prop :=
  | pin_reply_intro se r m pe (MPE: R se pe m):
    pin_reply R (m, se) (r, pe) (r, m).
  Program Definition pin_no_join ce: callconv (li_c @ penv) (li_c @ mem) :=
    {|
      ccworld := Memory.mem * Genv.symtbl;
      match_senv '(_, se) se1 se2 := se = se1 /\ se = se2;
      LanguageInterface.match_query := pin_query (penv_mem_match ce);
      LanguageInterface.match_reply '(_, se) r1 r2 := exists m, pin_reply (penv_mem_match ce) (m, se) r1 r2;
    |}.
  Next Obligation. reflexivity. Qed.
  Next Obligation. inv H0. reflexivity. Qed.
  Next Obligation. inv H. reflexivity. Qed.

End PIN_NO_JOIN.

Local Opaque ce.

Lemma pin_join_ref :
  vcomp (pin_no_join ce) join_cc [= ClightP.pin ce.
Proof.
  intros c Hc. induction c.
  - cbn in *. eprod_crush. xinv H. xinv H0.
    xinv HM. xinv HM0. xinv HSE0. xinv HSE.
    econstructor. instantiate (1 := (m, s)).
    cbn. easy. constructor; eauto.
  - cbn in *. eprod_crush. xinv H. xinv H0.
    xinv HM. xinv HM0. xinv HSE0. xinv HSE.
    econstructor. instantiate (1 := (m, s)).
    cbn. easy. constructor; eauto.
    intros Hr. xinv Hr. inv H. cbn in *.
    destruct (H1 (cr rv msrc0, x)) as [Hr|Hr].
    + xinv Hr. destruct w. destruct HSE. subst.
      apply HN. econstructor. econstructor. eauto.
    + xinv Hr. apply HN. constructor. eauto.
  -  cbn in *. eprod_crush. xinv H. xinv H0.
    xinv HM. xinv HM0. xinv HSE0. xinv HSE.
    econstructor. instantiate (1 := (m, s)).
    cbn. easy. constructor; eauto.
    intros Hr. xinv Hr. inv H. cbn in *.
    apply IHc. clear IHc.
    destruct (H1 (cr rv msrc0, x)) as [Hr|[Hr|Hr]].
    + exfalso. xinv Hr. destruct w. destruct HSE. subst.
      apply HN. econstructor. econstructor. eauto.
    + exfalso. xinv Hr. apply HN. constructor. eauto.
    + erewrite !regular_conv in Hr; eauto.
      * econstructor. econstructor. econstructor; eauto.
      * intros Hx. xinv Hx. apply HN. econstructor. eauto.
      * econstructor. instantiate (1 := (m, s)).
        constructor; eauto. constructor. eauto.
      * intros Hx. xinv Hx. apply HN.
        destruct w. inv HSE. econstructor. econstructor. eauto.
        Unshelve.
        cbn. exact tt.
Qed.

Lemma ϕ_rb_conv_ref1: ϕ_bq_conv_1 [= ϕ_rb_conv.
Proof.
  unfold ϕ_bq_conv_1, ϕ_rb_conv, E_rb_rb0_conv', E_rb_rb0_conv, deencap.
  rewrite <- pin_join_ref.
  rewrite <- !vcomp_assoc.
  apply vcomp_ref. 2: reflexivity.
  rewrite m_rb_ref.
  rewrite !vcomp_assoc.
  apply vcomp_ref. reflexivity.
  apply vcomp_ref. reflexivity.
  intros c Hc. induction c.
  - cbn in *. eprod_crush. xinv H. xinv HM. xinv H0. xinv HM.
    exists (s, Datatypes.pair c r)%embed. split. repeat constructor.
    exists (s, Datatypes.pair c pe)%embed. split.
    + econstructor; econstructor; eauto.
    + econstructor. instantiate (1 := (_, s)). cbn. easy.
      cbn. econstructor; eauto.
  - cbn in *. eprod_crush. xinv H. xinv HM. xinv H0. xinv HM.
    exists (s, Datatypes.pair c1 r0)%embed. split. repeat constructor.
    split. exists (s, Datatypes.pair c1 pe)%embed. split.
    { econstructor; econstructor; eauto. }
    { econstructor. instantiate (1 := (_, s)). cbn. easy.
      cbn. econstructor; eauto. }
    intros [cr rb1]. apply not_imply_or. intros Hr.
    exists (s, Datatypes.pair c1 pe)%embed. split.
    { econstructor; econstructor; eauto. } split.
    { econstructor. instantiate (1 := (_, s)). cbn. easy.
      cbn. econstructor; eauto. }
    intros [cr1 p1]. apply not_imply_or. intros Hr1.
    econstructor. instantiate (1 := (_, s)). cbn. easy.
    cbn. constructor. eauto.
    intros Hr2. cbn in *. destruct Hr2 as (mx & Hmx). inv Hmx.
    eapply esig_rel_mr_elim in Hr. 2: { econstructor.  }
    eapply @rcp_forbid_mr with (w := tt) in Hr1.
    2: { cbn. easy. } 2: { constructor. eauto. }
    xinv Hr. xinv Hr1.
    specialize (H1 (c, m)) as [H1 | H1].
    + xinv H1. apply HA. econstructor; eauto. reflexivity.
    + xinv H1. apply HA. econstructor.
  - cbn in *. eprod_crush. xinv H. xinv HM. xinv H0. xinv HM.
    exists (s, Datatypes.pair c2 r0)%embed. split. repeat constructor.
    split. exists (s, Datatypes.pair c2 pe)%embed. split.
    { econstructor; econstructor; eauto. }
    { econstructor. instantiate (1 := (_, s)). cbn. easy.
      cbn. econstructor; eauto. }
    intros [cr rb1]. apply not_imply_or. intros Hr.
    eapply esig_rel_mr_elim in Hr. 2: { econstructor. }
    xinv Hr. apply not_imply_or. intros Hx.
    eapply not_ex_all_not with (n := (s, Datatypes.pair c2 pe)%embed) in Hx.
    apply not_and_or in Hx as [Hx | Hx].
    { exfalso. apply Hx. econstructor. now cbn.
      cbn. econstructor; eauto. }
    apply not_and_or in Hx as [Hx | Hx].
    { exfalso. apply Hx. econstructor.
      instantiate (1 := (_, s)). now cbn.
      cbn. econstructor; eauto. }
    apply not_all_ex_not in Hx as ((cr3 & p3) & Hx).
    apply not_or_and in Hx as [Hx1 Hx2].
    eapply @rcp_forbid_mr with (w := tt) in Hx1. xinv Hx1.
    2: { now cbn. } 2: { constructor; eauto. }
    eapply @rcp_forbid_mr with (w := (_, s)) in Hx2. xinv Hx2. inv H.
    2: { now cbn. } 2: { constructor; eauto. }
    specialize (H1 (c0, m)) as [H1|[H1|H1]].
    + exfalso. xinv H1. apply HA.
      econstructor; eauto. reflexivity.
    + exfalso. xinv H1. apply HA. econstructor.
    + rewrite !regular_conv in H1.
      rewrite !regular_conv. eauto.
      * econstructor. split. econstructor. cbn. eauto.
        constructor. eauto. econstructor.
        instantiate (1 := (_, s)). now cbn. constructor. eauto.
      * intros HA. cbn in HA.
        eprod_crush. specialize (H2 (c0, p3)) as [A | B].
        xinv A. apply HN. constructor. eauto.
        xinv B. apply HN. destruct w. econstructor.
        constructor. eauto. cbn in HSE. destruct HSE. subst. eauto.
      * repeat constructor.
      * intros HA. xinv HA. apply HA0. repeat constructor.
      * repeat constructor.
      * intros Hx. xinv Hx. apply HA. constructor.
      * constructor. econstructor; eauto.
      * intros HA. xinv HA. apply HA0.
        cbn. econstructor; eauto. reflexivity.
        Unshelve. all: cbn; exact tt.
Qed.

Lemma ϕ_bq_conv_ref1: ϕ_bq_conv_2 = E_bq_m0_conv.
Proof.
  unfold ϕ_bq_conv_2, E_bq_m0_conv, E_bq_m0_conv_explicit, join_conv, deencap.
  rewrite <- !vcomp_assoc. reflexivity.
Qed.

Import CategoricalComp.

Lemma ϕ_bq_rb:
  rsq E0_conv E_bq_m0_conv rs_ready Π_bq
    (comp_semantics' (Clight.semantics2 bqc) (Clight.semantics2 rbc) sk).
Proof.
  rewrite <- ϕ_bq_conv_ref1.
  unfold embed_lts_with_sk.
  setoid_rewrite <- cc_comp_ref. rewrite ϕ1'.
  eapply rsq_comp. constructor.
  1-2: admit.
  - apply ϕ_bq_with_internals.
  - rewrite ϕ_rb_conv_ref1.
    apply ϕ_rb_with_internals.
Admitted.

(* --------------------------------------- *)

Lemma ϕ_bq : rsq E_rb_m0_conv E_bq_m0_conv rs_ready M_bq (Clight.semantics2 BQ.bq_program).
Proof.
  pose proof BQ.bq_correct0 as HA.
  apply fsim_rsq in HA. 2: admit.
  eapply @rsq_vcomp in HA. 5: apply ϕ_bq0. 2: constructor. 2-3: admit.

  (* pose proof (ClightP.transl_program_correct _ _ HT1). *)
  (* assert (rsq (vcomp (vcomp E_rb_conv flag_cc) ClightP.pout) *)
  (*             (vcomp (vcomp E_bq_conv bq_cc) (ClightP.pin ce)) *)
  (*             rs_ready M_bq (Clight.semantics2 tbq)) as HX. *)
  (* { *)
  (*   eapply rsq_vcomp. constructor. admit. admit. 2: apply fsim_rsq; eauto. 2: admit. *)
  (*   eapply rsq_vcomp. constructor. admit. admit. apply ϕ_bq0. *)
  (*   apply fsim_rsq; eauto. admit. *)
  (* } *)
  eapply (rsq_deencap_target _ _ _ _ m0) in HA.
  pose proof (@rsq_lift_convert _ mem (Clight.semantics2 BQ.bq_program)) as HB.
  eapply @rsq_vcomp in HB. 5: apply HA. 2: constructor. 2-3: admit.
  pose proof (fp BQ.bq_program) as HC. apply fsim_rsq in HC. 2: admit.
  eapply @rsq_vcomp in HC. 5: apply HB. 2: constructor. 2-3: admit.
  (* rewrite ϕ_rb_conv_ref. *)
  (* rewrite <- !E0_conv_vcomp in HX. apply HX. *)
Admitted.

Lemma ϕ_rb_conv_ref:
  E_rb_m0_conv [= (vcomp (vcomp E_rb_rb0_conv' rb_cc) (ClightP.pin ce)).
Proof.
  unfold E_rb_m0_conv. unfold E_rb_m0_conv_explicit. unfold deencap.
  unfold E_rb_rb0_conv'. unfold E_rb_rb0_conv. unfold deencap.
  unfold join_conv.
  rewrite !vcomp_assoc.
  intros c Hc. revert Hc.

  (* destruct c. *)
  (* - cbn in *. *)
  (*   (* destruct Hc as [Hc1 Hc2]. *) *)
  (*   (* destruct Hc2 as ((se3 & (cq & m_frag1)) & Hc2 & Hc3). *) *)
  (*   (* xinv Hc2. xinv Hc3. cbn in *. subst. xinv HM. xinv Hc1. *) *)
  (*   admit. *)
  (* - cbn in *. *)
  (*   admit. *)
  (* -  *)

  (* rewrite vcomp_expand. intros c (((se1 & q1) & m_frag) & Hc). cbn in Hc. *)
  (* rewrite vcomp_expand. cbn. *)
  (* exists ((se1, q1)%embed, rb0). intros [[cr rb1]|]. *)
  (* 2: { *)
  (*   specialize (Hc None). destruct c; cbn in *. *)
  (*   - cbn. admit. *)
  (*   - admit. *)
  (*   - admit. *)
  (* } *)
  (* specialize (Hc (Some (cr, m_frag))). *)
  (* - cbn in *. admit. *)
  (* - cbn in *. *)

  (* eapply rsq_vcomp. constructor. admit. admit. *)
  (* assert (R: rel S_rb Mem.mem). admit. *)
  (* set (t := (tstrat tp_ready id R)). *)
  (* instantiate (1 := (tstrat tpos_ready id R)). *)

  (* cbn. intros c Hc. induction c. *)
  (* - rename m1 into mq. cbn in *. destruct m2 as (se & cqm). *)
  (*   destruct Hc as (((se1 & q1) & m_frag) & Hc1 & Hc3). *)
  (*   destruct Hc1 as ((se2 & q2) & Hc1 & Hc2). *)
  (*   destruct Hc3 as ((se3 & (cq & m_frag1)) & Hc3 & Hc4). *)
  (*   xinv Hc3. xinv HM. xinv Hc1. xinv Hc2. inv H2. xinv Hc4. cbn in *. subst. *)
  (*   exists (se, Datatypes.pair cq penv0)%embed. split. *)
  (*   2: { econstructor. instantiate (1 := (m0, se)). *)
  (*        - constructor; eauto. *)
  (*        - cbn. inv HM0. constructor; eauto. *)
  (*          apply Hm0. inv HM; eauto. } *)
  (*   exists (se, Datatypes.pair cq rb0)%embed. split. *)
  (*   2: { econstructor. reflexivity. cbn. *)
  (*        destruct cq. constructor. 2: apply Hpenv0. *)
  (*        inv HM0. eauto. } *)
  (*   exists ((se, cq)%embed, rb0). split. *)
  (*   2: { repeat econstructor. } *)
  (*   exists (se, cq)%embed. split. *)
  (*   { constructor. apply HM. } *)
  (*   constructor. *)
  (* - rename m1 into mq. cbn in Hc. destruct m2 as (se & cqm). *)
  (*   destruct Hc as (((se1 & q1) & m_frag) & Hc1 & Hc3 & Hr1). *)
  (*   destruct Hc1 as ((se2 & q2) & Hc1 & Hc2). *)
  (*   destruct Hc3 as ((se3 & (cq & m_frag1)) & Hc3 & Hc4). *)
  (*   xinv Hc3. xinv HM. xinv Hc1. xinv Hc2. inv H2. xinv Hc4. cbn in * |-. subst. *)
  (*   unfold vcomp_has at 1. *)
  (*   assert (HA: cc_conv_has rb_cc (@rcp_allow (Lifting.lifted_li S_rb li_c) (Lifting.lifted_li PEnv.penv li_c) (se, Datatypes.pair cq rb0)%embed (se, Datatypes.pair cq penv0)%embed)). *)
  (*   { econstructor. reflexivity. cbn. destruct cq. constructor. 2: apply Hpenv0. inv HM0. eauto. } *)
  (*   assert (HB: Downset.has E_rb_rb0_conv' (@rcp_allow E_rb (Lifting.lifted_li S_rb li_c) mq (se, Datatypes.pair cq rb0)%embed)). *)
  (*   { exists ((se, cq)%embed, rb0). split. *)
  (*     - exists (se, cq)%embed. split. { constructor. apply HM. } constructor. *)
  (*     - repeat econstructor. } *)
  (*   assert (HC: Downset.has (vcomp E_rb_rb0_conv' rb_cc) (@rcp_allow E_rb (Lifting.lifted_li PEnv.penv li_c) mq (se, Datatypes.pair cq penv0)%embed)). *)
  (*   { exists (se, Datatypes.pair cq rb0)%embed. split. apply HB. apply HA. } *)
  (*   assert (HD: cc_conv_has (ClightP.pin ce) (@rcp_allow (Lifting.lifted_li PEnv.penv li_c) li_c (se, (Datatypes.pair cq penv0))%embed (se, cqm)%embed)). *)
  (*   { econstructor. instantiate (1 := (m0, se)). { constructor; eauto. } *)
  (*     cbn. inv HM0. constructor; eauto. apply Hm0. inv HM; eauto. } *)
  (*   exists (se, Datatypes.pair cq penv0)%embed. split. apply HC. split. apply HD. *)
  (*   intros (cr & pe1). apply not_imply_or. intros Hx. *)
  (*   eapply @rcp_forbid_mr with (w:= (m0, se)) in Hx. cbn in Hx. *)
  (*   destruct Hx as (mx & Hx). *)
  (*   2: { split; eauto. } *)
  (*   2: { cbn. inv HM0. constructor; eauto. apply Hm0. inv HM; eauto. } *)
  (*   exists (se, Datatypes.pair cq rb0)%embed. split. apply HB. split. apply HA. *)
  (*   intros (cr1 & rrb1). apply not_imply_or. intros Hy. *)
  (*   eapply @rcp_forbid_mr with (w:= tt) in Hy. cbn in Hy. inv Hy. *)
  (*   2: { reflexivity. } *)
  (*   2: { inv HM0. constructor; eauto. apply Hpenv0. } *)
  (*   exists ((se, cq)%embed, rb0). split. 2: split. *)
  (*   { exists (se, cq)%embed. split. { constructor. apply HM. } constructor. } *)
  (*   { repeat econstructor. } *)
  (*   intros (cr2 & rrb2). apply not_imply_or. intros Hz. *)
  (*   eapply esig_rel_mr_elim in Hz. 2: { repeat constructor. } inv Hz. *)
  (*   exists (se, cq)%embed. split. { constructor. apply HM. } split. constructor. *)
  (*   intros cr3. cbn. apply or_commut. apply not_imply_or. intros Hw. *)
  (*   eapply esig_rel_mr_elim in Hw. 2: apply HM.  *)
  (*   remember ({| cr_retval := rv; cr_mem := m |}) as cr. *)
  (*   specialize (Hr1 (cr, mx)) as [Hr1|Hr1]. *)
  (*   + destruct Hr1 as ((?&?) & C1 & C2 & Hr1). xinv C1. xinv C2. inv H2. *)
  (*     specialize (Hr1 cr3) as [Hr1|Hr1]. *)
  (*     * dependent destruction Hr1. easy. *)
  (*     * dependent destruction Hr1. constructor; eauto. *)
  (*   + exfalso. destruct Hr1 as ((?&?) & C1 & C2 & Hr1). *)
  (*     specialize (Hr1 (cr, mx)). xinv C1. xinv C2. xinv HM1. *)
  (*     destruct Hr1 as [Hr1|Hr1]. *)
  (*     * dependent destruction Hr1. apply HA0. constructor. *)
  (*     * dependent destruction Hr1. apply HN. xinv Hx. *)
  (*       econstructor; eauto. *)
  (* - *)


Admitted.

Lemma ϕ_rb : rsq E0_conv E_rb_m0_conv rs_ready Π_rb (Clight.semantics2 trb).
Proof.
  pose proof rb_correct2.
  pose proof (ClightP.transl_program_correct _ _ HT2).
  assert (rsq (vcomp (vcomp E0_conv 1%cc) ClightP.pout)
              (vcomp (vcomp E_rb_rb0_conv' rb_cc) (ClightP.pin ce))
              rs_ready Π_rb (Clight.semantics2 trb)) as HX.
  {
    eapply rsq_vcomp. constructor. admit. admit. 2: apply fsim_rsq; eauto. 2: admit.
    eapply rsq_vcomp. constructor. admit. admit. apply ϕ_rb1.
    apply fsim_rsq; eauto. admit.
  }
  (* rewrite ϕ_rb_conv_ref. *)
  (* rewrite <- !E0_conv_vcomp in HX. apply HX. *)
Admitted.

