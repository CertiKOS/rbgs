Require Import Classical.
Require Import Program.Equality.
Require Import LogicalRelations.
Require Import Poset.
Require Import Lattice.
Require Import Downset.
Require Import IntStrat.
Require Import Classical_Prop.
Require Import Coqlib.
Require Import Determ.
Require Import Util.

From compcert.common Require Import Smallstep Globalenvs.
Require LanguageInterface.
Import -(notations) LanguageInterface.
Require Import Example.
Import Memory Values Integers ListNotations.
Require Import CompCertStrat.
Require Import BQUtil.
Close Scope list.

Require Import FunctionalExtensionality.

Require Import ClightPStrat.

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
Definition L_bq : strat 0 (E_bq @ S_bq) ready := closure (join L_enq_strat L_deq_strat).

Import Datatypes.

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
Definition L_rb : strat 0 (E_rb @ S_rb) ready := closure (join (join L_inc1_strat L_inc2_strat) (join L_get_strat L_set_strat)).

Local Hint Constructors no_reentrancy_play : core.

Local Instance L_rb_regular : Regular L_rb.
Proof.
  split. eexists. split. reflexivity.
  intros s Hs. destruct Hs as [[|] [[|] Hs]];
    cbn in Hs; eprod_crush; eapply no_reentrancy_play_ref;
    eauto;
    unfold L_inc1_play, L_inc2_play, L_get_play, L_set_play;
    eauto.
Qed.

Local Transparent join.
Local Hint Constructors no_reentrancy_play pcoh : core.
Local Opaque N.

Lemma no_reentrancy_play_ref {E F i} (p1 p2: @play E F i):
  p2 [= p1 -> no_reentrancy_play p1 -> no_reentrancy_play p2.
Proof.
  intros Hp Hp1. revert p2 Hp. induction Hp1; intros; cbn in Hp; try solve [ xinv Hp; eauto ].
  - dependent destruction Hp; eauto.
  - dependent destruction Hp; eauto.
  - dependent destruction Hp; eauto.
  - dependent destruction Hp. dependent destruction Hp. eauto.
Qed.

Lemma pcoh_ref {E F i} (s1 s2 t1 t2: @play E F i):
  s1 [= s2 -> t1 [= t2 -> pcoh s2 t2 -> pcoh s1 t1.
Proof.
  intros Hs Ht Hpcoh. revert s1 t1 Hs Ht. induction Hpcoh; intros; cbn in *.
  - dependent destruction Hs; eauto.
  - dependent destruction Ht; eauto.
  - dependent destruction Hs; eauto.
  - dependent destruction Ht; eauto.
  - dependent destruction Hs; dependent destruction Ht; eauto.
  - dependent destruction Hs; dependent destruction Ht; eauto.
  - dependent destruction Hs; dependent destruction Ht; eauto.
Qed.

Local Instance L_rb_deterministic: Deterministic L_rb.
Proof.
  Ltac solve_different_play :=
    match goal with
    | [ H1: pref _ _, H2: pref _ _ |- _ ] =>
        dependent destruction H0; eauto;
        dependent destruction H; eauto; apply pcons_pcoh_oq; easy
    end.
  Ltac solve_same_play :=
    match goal with
    | [ |- pcoh (oq ?x :: _) (oq ?y :: _) ] =>
        let H := fresh "H" in
        destruct (classic (x = y)); [ inv H | ]; eauto
    end.
  apply closure_determ.
  - split. intros * Hs Ht.
    destruct Hs as [[|] [[|] Hs]]; destruct Ht as [[|] [[|] Ht]]; cbn in *; eprod_crush;
      try solve [solve_different_play].
    + eapply pcoh_ref; eauto. unfold L_inc1_play. solve_same_play.
    + eapply pcoh_ref; eauto. unfold L_inc2_play. solve_same_play.
    + eapply pcoh_ref; eauto. unfold L_get_play. solve_same_play.
    + eapply pcoh_ref; eauto. unfold L_set_play. solve_same_play.
  - split. intros s Hs. destruct Hs as [[|] [[|] Hs]].
    + cbn in Hs. destruct Hs as (f & c1 & c2 & Hs).
      eapply no_reentrancy_play_ref; eauto. unfold L_inc1_play. eauto.
    + cbn in Hs. destruct Hs as (f & c1 & c2 & Hs).
      eapply no_reentrancy_play_ref; eauto. unfold L_inc2_play. eauto.
    + cbn in Hs. destruct Hs as ((f & Hf) & c1 & c2 & i & Hs).
      eapply no_reentrancy_play_ref; eauto. unfold L_get_play. eauto.
    + cbn in Hs. destruct Hs as (f & c1 & c2 & i & v & Hs).
      eapply no_reentrancy_play_ref; eauto. unfold L_set_play. eauto.
Qed.

Local Hint Constructors seq_comp_has closure_has : core.

(* L_bq ⊑ (M_bq @ S_rb) ∘ L_rb *)
Lemma ϕ1 :
  rsq vid (tconv vid bq_rb_rel) L_bq ((M_bq @ S_rb) ⊙ L_rb).
Proof.
  unfold M_bq. rewrite <- closure_lift.
  rewrite closure_comp. 2: typeclasses eauto.
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
      - destruct HX. apply H0. apply JMeq_refl.
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
      - destruct HX. destruct HQ. apply H2. rewrite H3. apply JMeq_refl.
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
Lemma ϕ1' : Π_bq [= M_bq ⊙ Π_rb.
Proof.
  unfold Π_bq, Π_rb. unfold encap.
  rewrite <- compose_assoc.
  rewrite <- encap_lift.
  rewrite compose_assoc.
  apply rsq_id_conv with (p := rs_ready).
  eapply rsq_comp_when. constructor.
  apply representation_independence with (R := rb_bq).
  { eapply bq_rb_intro with (n := 0%nat).
    Local Transparent N.
    all: eauto; unfold N, Example.N; try lia. }
  apply ϕ1.
Qed.


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
Local Coercion embed_lts_with_sk : semantics >-> strat.

Definition penv0 : PEnv.penv :=
  PTree.set arr_id (PEnv.Array Nz (ZMap.init (PEnv.Val (Vint (Int.repr 0)) tint)) (tarray tint Nz))
  (PTree.set cnt1_id (PEnv.Val (Vint (Int.repr 0)) tint)
  (PTree.set cnt2_id (PEnv.Val (Vint (Int.repr 0)) tint)
  (PTree.empty PEnv.val))).

Lemma Hpenv0 : rb_penv_rel rb0 penv0.
Proof.
  unfold penv0. econstructor; eauto.
  - rewrite PTree.gss. reflexivity.
  - rewrite PTree.gso. rewrite PTree.gss. reflexivity.
    intros H. inv H.
  - rewrite PTree.gso. rewrite PTree.gso. rewrite PTree.gss. reflexivity.
    intros H. inv H. intros H. inv H.
  - intros i Hi. eexists. repeat apply conj; eauto.
    rewrite ZMap.gi. reflexivity.
  - constructor. cbn. rewrite Int.unsigned_repr; cbn; lia.
  - unfold Example.N. lia.
  - constructor. cbn. rewrite Int.unsigned_repr; cbn; lia.
  - unfold Example.N. lia.
  - intros. do 3 (rewrite PTree.gso; eauto).
Qed.

Context (m0 : Mem.mem) (arr_b cnt1_b cnt2_b: positive).
Definition se_valid2 se :=
  Genv.find_symbol se arr_id = Some arr_b /\
  Genv.find_symbol se cnt1_id = Some cnt1_b /\
  Genv.find_symbol se cnt2_id = Some cnt2_b.
Definition id_in_penv id := id = arr_id \/ id = cnt1_id \/ id = cnt2_id.
Definition ce := ClightP.ClightP.prog_comp_env rb_program.
Context (Hm0: forall se, se_valid2 se -> PEnv.penv_mem_match ce se penv0 m0)
  (Hse_valid2_inv: forall se pe m, PEnv.penv_mem_match ce se pe m -> se_valid2 se).

Lemma match_rb_id_in_penv rb pe id v:
  rb_penv_rel rb pe -> pe!id = Some v -> id_in_penv id.
Proof.
  intros H1 H2. inv H1. unfold id_in_penv.
  destruct (peq id arr_id). firstorder.
  destruct (peq id cnt1_id). firstorder.
  destruct (peq id cnt2_id). firstorder.
  exploit HNONE; eauto. intros. congruence.
Qed.

Lemma se_valid2_in_penv_agree se1 se2 id:
  se_valid2 se1 -> se_valid2 se2 -> id_in_penv id ->
  Genv.find_symbol se1 id = Genv.find_symbol se2 id.
Proof.
  intros (A & B & C) (D & E & F) [H1|[H1|H1]]; congruence.
Qed.

(** ** Deterministic property  *)

Local Hint Constructors Events.match_traces : core.
Local Transparent Int.repr.
Lemma int_repr_of_nat_inj i j:
  (i < N)%nat -> (j < N)%nat ->
  Vint (Int.repr (Z.of_nat i)) = Vint (Int.repr (Z.of_nat j)) -> i = j.
Proof.
  intros Hi Hj Hij.
  assert (Int.repr (Z.of_nat i) = Int.repr (Z.of_nat j)).
  { congruence. }
  unfold Int.repr in H. inv H.
  rewrite !Int.Z_mod_modulus_eq in H1.
  rewrite !Zmod_small in H1.
  2: { unfold N, Example.N in *. unfold Int.modulus. unfold Int.wordsize.
       unfold Wordsize_32.wordsize. unfold two_power_nat. cbn. lia. }
  2: { unfold N, Example.N in *. unfold Int.modulus. unfold Int.wordsize.
       unfold Wordsize_32.wordsize. unfold two_power_nat. cbn. lia. }
  apply Nat2Z.inj; eauto.
Qed.

Local Instance rb_spec_deterministic: Deterministic rb_spec.
Proof.
  apply lts_strat_determ. intros se. split.
  - intros * Hs1 Hs2. inv Hs1; inv Hs2; split; eauto; try easy.
    + apply int_repr_of_nat_inj in H7; eauto. congruence.
    + apply int_repr_of_nat_inj in H9; eauto. subst. easy.
  - intros s t s' H. inv H; cbn; lia.
  - intros * Hq1 Hq2. inv Hq1; inv Hq2; try easy.
    + inv H5. exploit Genv.find_symbol_injective. apply H0. apply H7. easy.
    + inv H5. exploit Genv.find_symbol_injective. apply H0. apply H7. easy.
  - intros * Hq s t Hs. inv Hq; inv Hs.
  - intros * Ha1 Ha2. inv Ha1; inv Ha2.
  - intros * Ha1 Ha2. inv Ha1; inv Ha2.
  - intros * Ha1 s t Hs. inv Ha1; inv Hs.
  - intros * Hf He. inv Hf; inv He.
  - intros * Hf1 Hf2. inv Hf1; inv Hf2. easy.
Qed.

Local Instance bq_spec_deterministic: Deterministic bq_spec.
  apply lts_strat_determ. intros se. split.
  - intros * Hs1 Hs2. inv Hs1; inv Hs2; split; eauto; easy.
  - intros s t s' H. inv H; cbn; lia.
  - intros * Hq1 Hq2. inv Hq1; inv Hq2; easy.
  - intros * Hq s t Hs. inv Hq; inv Hs.
  - intros * Ha1 Ha2. inv Ha1; inv Ha2; try congruence.
  - intros * Ha1 Ha2. inv Ha1; inv Ha2; easy.
  - intros * Ha1 s t Hs. inv Ha1; inv Hs.
  - intros * Hf He. inv Hf; inv He.
  - intros * Hf1 Hf2. inv Hf1; inv Hf2. easy.
Qed.

Local Instance clightp_deterministic sk p:
  Deterministic (lts_strat_sk sk (ClightP.ClightP.clightp2 p)).
Proof. apply lts_strat_determ. apply clightp_determinate. Qed.

Local Instance clight_deterministic sk p:
 Deterministic (lts_strat_sk sk (semantics2 p)).
Proof. apply lts_strat_determ. apply clight_determinate. Qed.

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

(* ------------------------------------------------- *)
(** Direct relation between S_rb and mem *)

Inductive rb_m_mq : op (li_c @ S_rb) -> op (li_c @ mem) -> Prop :=
| rb_m_mq_intro rb m q se pe
    (HRB: rb_penv_rel rb pe) (HM: PEnv.penv_mem_match ce se pe m):
  rb_m_mq ((se, q)%embed, rb) ((se, q)%embed, m).
Inductive rb_m_mr (m1: op (li_c @ S_rb)) (m2: op (li_c @ mem)): ar m1 -> ar m2 -> Prop :=
| rb_m_mr_intro rb m r se q pe
    (HRB: rb_penv_rel rb pe) (HM: PEnv.penv_mem_match ce se pe m):
    (se, q)%embed = fst m1 ->
  rb_m_mr m1 m2 (r, rb) (r, m).
Definition rb_m_erel : esig_rel (li_c @ S_rb) (li_c @ mem) :=
  {| match_query := rb_m_mq; match_reply := rb_m_mr |}.

Inductive play_preserve_se : forall p, @play li_c li_c p -> Prop :=
| play_preserve_se_ready: play_preserve_se ready pnil_ready
| play_preserve_se_suspended q m: play_preserve_se (suspended q m) (pnil_suspended q m)
| play_preserve_se_oq q s:
  play_preserve_se (running q) s ->
  play_preserve_se ready (oq q :: s)
| play_preserve_se_pq se q m s:
  play_preserve_se (suspended (se, q)%embed (se, m)%embed) s ->
  play_preserve_se (running (se, q)%embed) (pq (se, m)%embed :: s)
| play_preserve_se_oa q m n s:
  play_preserve_se (running q) s ->
  play_preserve_se (suspended q m) (oa n :: s)
| play_preserve_se_pa q r s:
  play_preserve_se ready s ->
  play_preserve_se (running q) (pa r :: s).

Arguments play_preserve_se {_} _.
Definition strat_preserve_se {p} (σ: strat li_c li_c p) :=
  forall s, Downset.has σ s -> play_preserve_se s.

Lemma seq_comp_preserve_se {p} s1 s2 (s: @play _ _ p):
  seq_comp_has s1 s2 s ->
  play_preserve_se s1 -> play_preserve_se s2 -> play_preserve_se s.
Proof.
  induction 1; intros; eauto;
    dependent destruction H0; constructor; eauto.
Qed.

Lemma closure_preserve_se σ:
  strat_preserve_se σ -> strat_preserve_se (closure σ).
Proof.
  intros H s Hs. cbn in *. induction Hs.
  { apply play_preserve_se_ready. }
  eapply seq_comp_preserve_se; eauto.
Qed.

Lemma lts_preserve_se (L: semantics li_c li_c) sk:
  strat_preserve_se (lts_strat_sk sk L).
Proof.
  apply closure_preserve_se. intros s Hs.
  cbn in *. dependent destruction Hs.
  { apply play_preserve_se_ready. }
  apply play_preserve_se_oq. clear HVF INIT.
  induction HS; eauto; repeat constructor; eauto.
Qed.

Lemma next_strat_preserve_se {i j} (σ: strat li_c li_c i) (m: move i j):
  strat_preserve_se σ -> strat_preserve_se (next m σ).
Proof.
  intros H s Hs. cbn in *. specialize (H _ Hs). inv H; eauto.
Qed.

Local Hint Resolve next_strat_preserve_se : core.

Lemma rb_m_erel_rsq_when
  t1 ti2 i (ti: tpos t1 ti2 i)
     tj2 j (tj: tpos t1 tj2 j)
  (l1: lpos _ ti2) (l2: lpos _ tj2)
  (p: rspos i j) σ (Hσ: strat_preserve_se σ):
  match p with
  | rs_ready => True
  | rs_running ((se, q1)%embed, rb) ((se2, q2)%embed, m) =>
      rb_m_mq ((se, q1)%embed, rb) ((se2, q2)%embed, m) /\
      match l1, l2 with
      | lrunning _ _ _ rb, lrunning _ _ _ m =>
          exists pe, rb_penv_rel rb pe /\ PEnv.penv_mem_match ce se pe m
      | _, _ => False
      end
  | rs_suspended ((se, q1)%embed, rb) ((se2, q2)%embed, m)
      ((mse, m1)%embed, mrb) m2 =>
      rb_m_mq ((se, q1)%embed, rb) ((se2, q2)%embed, m) /\
      rb_m_mq ((mse, m1)%embed, mrb) m2 /\
      mse = se /\
      match l1, l2 with
      | lsuspended _ _ _ rb, lsuspended _ _ _ m =>
          exists pe, rb_penv_rel rb pe /\ PEnv.penv_mem_match ce se pe m
      | _, _ => False
      end
  end ->
  rsq_when rb_m_erel rb_m_erel p
    (tstrat_when ti σ (lens_strat_when lid l1))
    (tstrat_when tj σ (lens_strat_when lid l2)).
Proof.
  intros Hp s (s1 & s2 & Hs1 & Hs2 & Hs). cbn in *.
  revert ti2 i ti tj2 j tj l1 l2 p Hp σ s s2 Hs1 Hs2 Hs Hσ.
  induction s1.
  - intros. dependent destruction Hs1. dependent destruction p.
    eapply rsp_ready. dependent destruction tj.
    exists pnil_ready, pnil_ready.
    repeat split; eauto. constructor. cbn.
    dependent destruction l2. constructor.
  - intros. dependent destruction Hs1. dependent destruction p.
    eapply rsp_suspended. dependent destruction tj.
    eexists (pnil_suspended _ _), (pnil_suspended _ _).
    repeat split; eauto. constructor. cbn.
    dependent destruction l2. constructor.
  - intros.
    dependent destruction p;
      dependent destruction ti;
      dependent destruction tj;
      dependent destruction m.
    + (* oq *)
      dependent destruction l1; dependent destruction l2.
      dependent destruction Hs1. dependent destruction Hs.
      apply rsp_oq.
      { exists pnil_ready, pnil_ready. repeat apply conj.
        - constructor.
        - eapply Downset.closed; eauto. constructor.
        - constructor. }
      intros [qx mx] Hq. cbn in Hq. dependent destruction Hq.
      inv HM.
      setoid_rewrite tstrat_next_oq.
      setoid_rewrite lens_strat_next_oq.
      eapply IHs1; eauto. 2: reflexivity.
      split. { econstructor; eauto. }
      cbn. exists pe. split; eauto.
    + (* pq *)
      dependent destruction l1; dependent destruction l2.
      dependent destruction Hs1. dependent destruction Hs.
      destruct q0. destruct Hp as (Hq & pe & Hpe1 & Hpe2).
      destruct m. assert (s0 = s) as ->.
      { specialize (Hσ _ Hs2). inv Hσ. eauto. }
      eapply rsp_pq. instantiate (1 := ((_, _)%embed, u0)).
      { constructor. econstructor; eauto. }
      setoid_rewrite tstrat_next_pq.
      setoid_rewrite lens_strat_next_pq.
      eapply IHs1; eauto. repeat split; eauto.
      econstructor; eauto.
    + (* pa *)
      dependent destruction l1; dependent destruction l2.
      dependent destruction Hs1. dependent destruction Hs.
      destruct q0. destruct Hp as (Hq & pe & Hpe1 & Hpe2).
      eapply rsp_pa. instantiate (1 := (r, u0)).
      { intros Hr. inv Hr. apply HA. econstructor; eauto. reflexivity. }
      inv x0.
      (* XXX I don't understand when this can't work without [inv x0] *)
      setoid_rewrite (tstrat_next_pa (s, q)%embed q4 r u0).
      setoid_rewrite lens_strat_next_pa. 2: reflexivity.
      rewrite regular_conv.
      2: { constructor. apply Hq. }
      2: { cbn. intros Hr. inv Hr. apply HA.
           cbn. econstructor; eauto. reflexivity. }
      eapply IHs1; eauto.
    + (* oa *)
      dependent destruction l1; dependent destruction l2.
      dependent destruction Hs1. dependent destruction Hs.
      destruct q0. destruct m2.
      destruct Hp as (Hq & Hm & Hse & pe & Hpe1 & Hpe2). subst s0.
      eapply rsp_oa.
      { eexists (pnil_suspended _ _), (pnil_suspended _ _). repeat split.
        - constructor.
        - eapply Downset.closed; eauto. constructor.
        - constructor. }
      inv x0.
      intros [r mr] Hr. cbn in *.
      rewrite regular_conv; eauto. 2: { constructor; eauto. }
      apply esig_rel_mr_elim in Hr. 2: { cbn. eauto. }
      inv Hr. 
      setoid_rewrite tstrat_next_oa.
      setoid_rewrite lens_strat_next_oa.
      eapply IHs1; eauto.
      split. eauto.
      exists pe0. split; eauto. cbn in *. inv H0. eauto.
Qed.

Lemma rb_m_erel_rsq σ:
  strat_preserve_se σ ->
  rsq rb_m_erel rb_m_erel (σ @ lid) (σ @ lid).
Proof.
  intro. eapply rb_m_erel_rsq_when; eauto. 
Qed.

Definition m_rb_ref:
  E_rb_conv ;; (de m0) [= (E_rb_conv ;; (de rb0)) ;; rb_m_erel.
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
    + assert (Hrc1: rcnext ((se, q)%embed, rb) ((se, q)%embed, m) (cr, rb1) (cr, m2) rb_m_erel = rb_m_erel).
      { apply regular_conv.
        - econstructor. econstructor; eauto. xinv HM; eauto.
        - intros Hx. xinv Hx. apply HA. econstructor; eauto. reflexivity. }
      setoid_rewrite Hrc1.
      assert (Hrc2: rcnext (se, q)%embed ((se, q)%embed, m) cr (cr, m2) (de m) = de m2).
      { clear. apply antisymmetry.
        - intros c Hc. cbn in *. xinv Hc. eauto.
        - intros c Hc. constructor. eauto. }
      setoid_rewrite Hrc2 in Ha.
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
          + setoid_rewrite Hrc3 in H1.
            setoid_rewrite Hrc4 in H1. congruence.
        - intros d Hd. cbn.
          exists (se, q)%embed. split. { constructor. now cbn. }
          split. { constructor. }
          intros cr1. apply not_imply_or. intros Hxa.
          apply not_imply_or. intros Hxb.
          assert (cr = cr1).
          { apply NNPP. intros HA. apply Hxb. constructor. congruence. }
          eapply esig_rel_mr_elim in Hxa.
          2: { cbn. eauto. } subst cr1.
          rewrite Hrc3. setoid_rewrite Hrc4. apply Hd. }
      setoid_rewrite Hrc5. eapply IHc; eauto.
      split; eauto. intros. clear - HM0 HRB H.
      exploit Hse_valid2_inv. eauto. intros Hx.
      constructor. intros id v Hv.
      inv HM0. specialize (MPE _ _ Hv) as (b & Hb & Hbb).
      exists b. split; eauto.
      rewrite <- Hb. apply se_valid2_in_penv_agree; eauto.
      eapply match_rb_id_in_penv; eauto.
Qed.

Local Hint Constructors E_rb_conv_mq E_rb_conv_mr : core.
Local Hint Constructors bq_initial_state bq_at_external bq_final_state bq_step bq_after_external : core.

Lemma ϕ_bq0 : rsq E_rb_conv E_bq_conv M_bq bq_spec.
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

Definition ϕ_bq_conv_1 :=
  deencap rb0 E_rb_conv ;; rb_m_erel ;; join_conv.
Definition ϕ_bq_conv_2 :=
  deencap rb0 E_bq_conv ;; rb_m_erel ;; join_conv.

Global Existing Instance tstrat_when_monotonic.

Lemma ϕ_bq_with_internals : rsq ϕ_bq_conv_1 ϕ_bq_conv_2 M_bq (Clight.semantics2 BQ.bq_program).
Proof.
  eapply rsq_vcomp.
  3: { eapply rsq_vcomp.
       3: apply ϕ_bq0. 3: apply rsq_de.
       all: typeclasses eauto. }
  1-2: typeclasses eauto.

  eapply rsq_vcomp.
  4: { apply frame_property_ref_sk. apply linkorder_bq. }
  1-2: typeclasses eauto.
  assert (embed_lts_with_sk bq_spec [= embed_lts_with_sk (semantics2 BQ.bq_program)).
  { eapply rsq_id_conv.
    rewrite <- !cc_conv_id.
    apply fsim_rsq_sk. apply clight_determinate.
    apply BQ.bq_correct0. apply linkorder_bq. }
  unfold scomp_strat. rewrite H. apply rb_m_erel_rsq.
  apply lts_preserve_se.
Qed.

(* eapply rsq_vcomp. *)
(*   4: { apply frame_property_ref_sk. apply linkorder_bq. } *)
(*   1-2: typeclasses eauto.  *)

(*   eapply rsq_vcomp. *)
(*   4: apply rsq_de. *)
(*   1-2,4: typeclasses eauto. *)

(*   rewrite <- (vcomp_vid_r E_rb_conv). *)
(*   rewrite <- (vcomp_vid_r E_bq_conv). *)
(*   eapply rsq_vcomp.  *)
(*   3: apply ϕ_bq0. 1-2: typeclasses eauto. *)

(*   rewrite <- !cc_conv_id. *)
(*   apply fsim_rsq_sk. apply clight_determinate. *)
(*   apply BQ.bq_correct0. apply linkorder_bq. *)
(* Qed. *)
(* Admitted. *)

(** ** Rb correctness *)

Definition E_rb_S_rb_conv : conv (E_rb @ S_rb) (Lifting.lifted_li rb_state li_c) :=
  tconv E_rb_conv vid ;; lift_emor.

Global Instance E0_conv_regular {E}:
  RegularConv (@E0_conv E).
Proof. split. intros. easy. Qed.

Local Opaque N.

Local Hint Constructors rb_final_state rb_step rb_initial_state : core.

Lemma ϕ_rb0 : rsq E0_conv E_rb_S_rb_conv L_rb rb_spec.
Proof.
  apply rsq_closure; eauto with typeclass_instances.
  intros s (i & Hs). destruct i; destruct Hs as [[|] Hs].
  - (* inc1 *)
    cbn in Hs. destruct Hs as (f & c1 & c2 & Hs). rewrite Hs. clear Hs.
    unfold L_inc1_play. apply rsp_oq.
    { repeat econstructor. }
    intros (se & cq & rb) (((se' & cq') & rb') & (Hq1 & Hq2) & Hq3).
    cbn in *. dependent destruction Hq1. inv HM.
    dependent destruction Hq3. rename se' into se.
    set (c1_i := Vint (Int.repr (Z.of_nat c1))).
    eapply rsp_pa with ((cr c1_i m), (f, (S c1 mod N)%nat, c2)).
    { intros (((se' & cq') & rb') & (Hr1 & Hr2) & Hr3 & Hr4). cbn in *.
      dependent destruction Hr3. 
      specialize (Hr4 ((cr c1_i m), (f, (S c1 mod N)%nat, c2))).
      cbn in Hr4. destruct Hr4 as [(Hra & Hrb & [Hrc | Hrc])|Hr4].
      - xinv Hrc. apply HA. econstructor; eauto.
      - xinv Hrc. easy.
      - xinv Hr4. cbn in *. easy. }
    apply rsp_ready. cbn.
    econstructor 2; cbn; eauto. 
    econstructor 4. { apply star_one. cbn; eauto. }
    econstructor 3; cbn; eauto.
  - (* inc1 *)
    cbn in Hs. destruct Hs as (f & c1 & c2 & Hs). rewrite Hs. clear Hs.
    unfold L_inc1_play. apply rsp_oq.
    { repeat econstructor. }
    intros (se & cq & rb) (((se' & cq') & rb') & (Hq1 & Hq2) & Hq3).
    cbn in *. dependent destruction Hq1. inv HM.
    dependent destruction Hq3. rename se' into se.
    set (c2_i := Vint (Int.repr (Z.of_nat c2))).
    eapply rsp_pa with ((cr c2_i m), (f, c1, (S c2 mod N)%nat)).
    { intros (((se' & cq') & rb') & (Hr1 & Hr2) & Hr3 & Hr4). cbn in *.
      dependent destruction Hr3. 
      specialize (Hr4 ((cr c2_i m), (f, c1, (S c2 mod N)%nat))).
      cbn in Hr4. destruct Hr4 as [(Hra & Hrb & [Hrc | Hrc])|Hr4].
      - xinv Hrc. apply HA. econstructor; eauto.
      - xinv Hrc. easy.
      - xinv Hr4. cbn in *. easy. }
    apply rsp_ready. cbn.
    econstructor 2; cbn; eauto.
    econstructor 4. { apply star_one. cbn; eauto. }
    econstructor 3; cbn; eauto.
  - (* get *)
    cbn in Hs. destruct Hs as ((f & Hf) & c1 & c2 & i & Hs). rewrite Hs. clear Hs.
    cbn. unfold L_get_play. apply rsp_oq.
    { repeat econstructor. }
    intros (se & cq & rb) (((se' & cq') & rb') & (Hq1 & Hq2) & Hq3).
    cbn in *. dependent destruction Hq1. inv HM.
    dependent destruction Hq3. rename se' into se.
    eapply rsp_pa with ((cr (f i) m), (f, c1, c2)).
    { intros (((se' & cq') & rb') & (Hr1 & Hr2) & Hr3 & Hr4). cbn in *.
      dependent destruction Hr2. dependent destruction Hr3. 
      specialize (Hr4 ((cr (f i) m), (f, c1, c2))).
      cbn in Hr4. destruct Hr4 as [(Hra & Hrb & [Hrc | Hrc])|Hr4].
      - xinv Hrc. apply HA. econstructor; eauto.
      - xinv Hrc. easy.
      - xinv Hr4. cbn in *. easy. }
    apply rsp_ready. cbn.
    econstructor 2; cbn; eauto.
    econstructor 4. { apply star_one. econstructor; eauto. }
    econstructor 3; cbn; eauto.
  - (* set *)
    cbn in Hs. destruct Hs as (f & c1 & c2 & i & v & Hs). rewrite Hs. clear Hs.
    cbn. unfold L_set_play. apply rsp_oq.
    { repeat econstructor. }
    intros (se & cq & rb) (((se' & cq') & rb') & (Hq1 & Hq2) & Hq3).
    cbn in *. dependent destruction Hq1. inv HM.
    dependent destruction Hq3. rename se' into se.
    set (g := fun j => if Nat.eq_dec i j then v else f j).
    eapply rsp_pa with ((cr Vundef m), (g, c1, c2)).
    { intros (((se' & cq') & rb') & (Hr1 & Hr2) & Hr3 & Hr4). cbn in *.
      dependent destruction Hr2. dependent destruction Hr3. 
      specialize (Hr4 ((cr Vundef m), (g, c1, c2))).
      cbn in Hr4. destruct Hr4 as [(Hra & Hrb & [Hrc | Hrc])|Hr4].
      - xinv Hrc. apply HA. econstructor; eauto.
      - xinv Hrc. easy.
      - xinv Hr4. cbn in *. easy. }
    apply rsp_ready. cbn.
    econstructor 2; cbn; eauto.
    econstructor 4. { apply star_one. constructor; eauto. }
    econstructor 3; cbn; eauto.
Qed.

(** A version of [ϕ_rb0] where [lift_emor] is moved to the strategy *)

Definition rb_spec' : li_c ->> li_c @ S_rb := liftr_emor ⊙ rb_spec.

(* Local Instance rb_spec_deterministic': Deterministic rb_spec. *)
(* Proof. *)
(* Admitted. *)

(* Definition E_rb_S_rb_conv' : conv (E_rb @ S_rb) (li_c @ S_rb) := *)
(*   E_rb_conv @ glob S_rb. *)

Definition E_rb_S_rb_conv' : conv (E_rb @ S_rb) (li_c @ S_rb) :=
  E_rb_conv * vid.

Lemma lift_liftr {li S}:
    ecomp liftr_emor (@lift_emor li S) = eid.
Proof.
  apply functional_extensionality_dep. intros [[se q] s].
  unfold eid, ecomp. cbn. f_equal.
  apply functional_extensionality. intros [r s']. reflexivity.
Qed.

Lemma liftr_emor_property2 {li S}:
  rsq lift_emor vid (IntStrat.id _) (@liftr_emor li S).
Proof.
  rewrite <- (compose_id_r liftr_emor).
  rewrite <- lift_liftr at 1.
  rewrite emor_strat_ecomp.
  eapply rsq_comp.
  - apply rsq_id_conv. reflexivity.
  - apply emor_strat_elim.
Qed.

Lemma ϕ_rb0' : rsq E0_conv E_rb_S_rb_conv' L_rb rb_spec'.
Proof.
  unfold E_rb_S_rb_conv'.
  unfold rb_spec'.
  pose proof ϕ_rb0.
  unfold E_rb_S_rb_conv in H.
  rewrite <- (compose_id_l L_rb).
  eapply rsq_comp. 2: apply H. clear H.
  rewrite <- (vcomp_vid_r (E_rb_conv * vid)) at 2.
  eapply rsq_vcomp.
  3: { apply rsq_id_strat. reflexivity. }
  1-2: typeclasses eauto.
  apply liftr_emor_property2.
Qed.


Definition E_rb_rb0_conv : conv E_rb (li_c @ S_rb) := deencap rb0 E_rb_conv.
(* Definition E_rb_rb0_conv' : conv E_rb (Lifting.lifted_li S_rb li_c) := *)
(*   E_rb_rb0_conv ;; lift_emor. *)

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
  deencap u0 R [= de u0 ;; (tconv R vid).
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
    split; eauto. intros Hy. specialize (Hf3 a) as [Hf3|Hf3].
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
    setoid_rewrite @rcnext_tconv; eauto.
    rewrite (regular_conv (R := vid)); eauto. 2: constructor.
    assert (x = n1). { apply NNPP. intros Hx. apply Hr. constructor. congruence. }
    subst.
    specialize (Hf3 a) as [A|[A|A]]; try easy.
    + exfalso. simple inversion A; try congruence.
      apply rcp_forbid_inv in H1. eprod_crush. xsubst. inv H0. easy.
    + setoid_rewrite de_rcnext in A. setoid_rewrite de_rcnext. apply IHc.
      assert (y = u0). apply NNPP. intros Hx. apply Hr2.
      split; eauto. intros Hc. apply Hx. apply JMeq_eq; eauto.
      subst. eauto.
Qed.

Lemma ϕ_rb1 : rsq E0_conv E_rb_rb0_conv Π_rb rb_spec'.
Proof.
  unfold E_rb_rb0_conv.
  rewrite de_vcomp_ref.
  rewrite <- (vcomp_vid_l (@E0_conv li_c)).
  eapply rsq_vcomp.
  3: apply deencap_rsq. 3: apply ϕ_rb0'.
  1-2: typeclasses eauto.
Qed.

(* Definition rb_cc' : li_c @ S_rb <=> li_c @ PEnv.penv. Admitted. *)
(* Lemma rb_cc_eq: rb_cc' = lift_emor ;; rb_cc ;; liftr_emor. *)
(* Admitted. *)
(* Definition pin' (ce: Ctypes.composite_env) : li_c @ PEnv.penv <=> li_c. Admitted. *)
(* Lemma pin_eq ce: pin' ce = lift_emor ;; ClightP.pin ce. *)
(* Admitted. *)

(* Local Instance rb_spec_deterministic': Deterministic rb_spec'. *)
(* Admitted. *)

Definition ϕ_rb_conv := E_rb_rb0_conv ;; lift_emor ;; rb_cc ;; ClightP.pin ce.

(* Lemma rb_correct2': *)
(*   rsq vid rb_cc' rb_spec' (clightp_strat_sk rb_program sk). *)
(* Proof. *)
(*   pose proof rb_correct2. *)
(*   rewrite rb_cc_eq. *)
(*   unfold rb_spec', clightp_strat. *)
(*   eapply rsq_comp with (S := cc_conv rb_cc). *)
(*   2: { rewrite <- cc_conv_id. *)
(*        eapply fsim_rsq_sk; eauto. *)
(*        apply clightp_determinate. *)
(*        cbn. erewrite ClightP.clightp_skel_correct. *)
(*        apply linkorder_rb. apply HT2. } *)
(* Admitted. *)

Lemma ϕ_rb_with_internals : rsq E0_conv ϕ_rb_conv Π_rb (Clight.semantics2 rbc).
Proof.
  unfold ϕ_rb_conv. erewrite E0_conv_vcomp.
  eapply rsq_vcomp. 3: apply ϕ_rb1.
  1-2: typeclasses eauto.

  eapply rsq_vcomp.
  3: {
    unfold rb_spec'. eapply rsq_comp.
    - apply liftr_emor_property.
    - eapply rsq_id_conv. reflexivity.
  }
  1-2: typeclasses eauto.
  rewrite compose_id_l.

  eapply rsq_vcomp.
  3: {
    eapply fsim_rsq_sk. apply clightp_determinate.
    apply rb_correct2.
    cbn. erewrite ClightP.clightp_skel_correct.
    apply linkorder_rb. apply HT2.
  }
  1-2: typeclasses eauto.
  eapply fsim_rsq_sk. apply clight_determinate.
  apply ClightP.transl_program_correct. apply HT2.
  cbn. erewrite ClightP.clightp_skel_correct.
  apply linkorder_rb. apply HT2.
Qed.

  (* 3: apply rb_correct2'. *)
  (* 3: { *)
  (*   rewrite pin_eq. unfold ce. *)
  (*   eapply clightp_correct_sk. *)
  (*   apply HT2. *)
  (*   erewrite ClightP.clightp_skel_correct. *)
  (*   apply linkorder_rb. apply HT2. } *)
  (* 1-2: admit. *)


(*   unfold ϕ_rb_conv. erewrite E0_conv_vcomp. *)
(*   eapply rsq_vcomp. *)
(*   4: { *)
(*        eapply fsim_rsq_sk. apply clight_determinate. *)
(*        apply ClightP.transl_program_correct. apply HT2. *)
(*        cbn. erewrite ClightP.clightp_skel_correct. *)
(*        apply linkorder_rb. apply HT2. } *)
(*   1-2: typeclasses eauto. *)
(*   erewrite E0_conv_vcomp. eapply rsq_vcomp.  *)
(*   4: { eapply fsim_rsq_sk. apply clightp_determinate. *)
(*        apply rb_correct2. *)
(*        cbn. erewrite ClightP.clightp_skel_correct. *)
(*        apply linkorder_rb. apply HT2. } *)
(*   1-2: typeclasses eauto. *)
(*   apply ϕ_rb1. *)
(* Qed. *)

(** ** Putting things together *)

Local Opaque ce.

Lemma pin_join_ref :
  pin_no_join ce ;; join_cc [= cc_conv (ClightP.pin ce).
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

(* Section JOIN_CONV. *)

(*   Inductive join_erel_mq : op (li_c @ mem) -> op li_c -> Prop := *)
(*   | join_erel_mq_intro se vf sg vargs msrc mtgt m *)
(*       (MJOIN: Join.join m msrc mtgt): *)
(*     join_erel_mq ((se, cq vf sg vargs msrc)%embed, m) *)
(*       (se, cq vf sg vargs mtgt)%embed. *)

(*   Inductive join_erel_mr: op (li_c @ mem) -> op li_c -> reply li_c * mem -> reply li_c -> Prop := *)
(*   | join_erel_mr_intro q1 q2 rv m msrc mtgt *)
(*       (MJOIN: Join.join m msrc mtgt): *)
(*     join_erel_mr q1 q2 (cr rv msrc, m) (cr rv mtgt). *)

(*   Definition join_erel : esig_rel (li_c @ mem) li_c := *)
(*     {| match_query := join_erel_mq; match_reply := join_erel_mr |}. *)

(*   Lemma join_erel_eq: join_conv = join_erel. *)
(*   Proof. *)
(*     apply antisymmetry. *)
(*     - intros s Hs. induction s; cbn in *; eprod_crush. *)
(*       + inv H. cbn in *. inv H2. inv H0. *)
(*         cbn in *. subst. inv HM. *)
(*         econstructor. econstructor. eauto. *)
(*       + inv H. cbn in *. inv H3. inv H0. *)
(*         econstructor. *)
(*         { cbn in *. subst. inv HM. econstructor. eauto. } *)
(*         specialize (H1 (c, m)). destruct H1 as [H1|H1]. *)
(*         * exfalso. inv H1. cbn in *. easy. *)
(*         * dependent destruction H1. *)
(*           intros Hr. apply HN. *)
(*           cbn in Hr.  inv Hr. econstructor. eauto. *)
(*       + admit. *)
(*     - intros s Hs. induction s; cbn in *; eprod_crush. *)
(*       + inv Hs. eexists (_, Datatypes.pair _ _)%embed. *)
(*         split. rewrite lift_emor_operator. econstructor. *)
(*         inv HM. econstructor. reflexivity. cbn. *)
(*         constructor. eauto. *)
(*       + inv Hs. admit. *)
(*       + admit. *)
(*   Admitted. *)

(* End JOIN_CONV. *)

(* Section ASSOC. *)

(*   Lemma assoc1 {E} (R: conv E _): *)
(*     (R ;; rb_m_erel) ;; join_conv [= R ;; rb_m_erel ;; join_conv. *)
(*   Proof. *)
(*     rewrite join_erel_eq. *)
(*     intros s Hs. induction s. *)
(*     - cbn in *. destruct m2 as [se q4]. *)
(*       destruct Hs as ([[se' q3] mx] & Hq2 & Hq3). *)
(*       inv Hq3. cbn in HM. *)
(*       destruct Hq2 as ([[se'' q2] srb] & Hq1 & Hq2). *)
(*       inv Hq2. cbn in HM0. *)
(*       exists ((se'', q2)%embed, srb). split; eauto. *)
(*       exists ((se', q3)%embed, mx). split; constructor; eauto. *)
(*     - cbn in *. destruct m2 as [se q4]. *)
(*       destruct Hs as ([[se' q3] mx] & Hq2 & Hq3 & Hr). *)
(*       inv Hq3. cbn in HM. *)
(*       destruct Hq2 as ([[se'' q2] srb] & Hq1 & Hq2). *)
(*       inv Hq2. cbn in HM0. *)
(*       exists ((se'', q2)%embed, srb). split; eauto. *)
(*       split. exists ((se', q3)%embed, mx). split; constructor; eauto. *)
(*       assert (se = se'). { inv HM. eauto. } subst se'. *)
(*       assert (se = se''). { inv HM0. eauto. } subst se''. *)
(*       intros [rx rbx]. apply not_imply_or. intros Hr1. *)
(*       exists ((se, q3)%embed, mx). *)
(*       split. constructor. eauto. *)
(*       split. constructor. eauto. *)
(*       intros [crx mxx]. *)
(*       specialize (Hr (crx, mxx)) as [Hr|Hr]. *)
(*       + admit. *)
(*       + right. eauto. *)
(*     - admit. *)
(*   Admitted. *)

(* End ASSOC. *)

Lemma regular_conv_ref {E F} (R S: E <=> F)
  (HR: RegularConv R) (HS: RegularConv S):
  (forall m1 m2, Downset.has R (rcp_allow m1 m2) ->
            Downset.has S (rcp_allow m1 m2)) ->
  (forall m1 m2 n1 n2, Downset.has R (rcp_forbid m1 m2 n1 n2) ->
                  Downset.has S (rcp_forbid m1 m2 n1 n2)) ->
  R [= S.
Proof.
  intros Hm Hn s Hs. induction s; eauto.
  destruct (classic (Downset.has S (rcp_forbid m1 m2 n1 n2))) as [A|A].
  - eapply Downset.closed; eauto. constructor.
  - assert (Downset.has R (rcp_allow m1 m2)) as B.
    { eapply Downset.closed; eauto. constructor. }
    assert (~ Downset.has R (rcp_forbid m1 m2 n1 n2)) as C by eauto.
    assert (Downset.has (rcnext m1 m2 n1 n2 R) s) as D by easy.
    rewrite regular_conv in D; eauto.
    specialize (IHs D).
    erewrite <- regular_conv in IHs.
    + apply IHs.
    + eauto.
    + eauto.
Qed.

Lemma ϕ_rb_conv_ref1_helper:
  rb_m_erel ;; join_conv [= lift_emor ;; rb_cc ;; ClightP.pin ce.
Proof.
  apply regular_conv_ref; try typeclasses eauto.
  - intros. cbn in *. eprod_crush.
    inv H. inv H0. cbn in *. inv H2.
    eexists (_, Datatypes.pair _ _)%embed. split.
    rewrite lift_emor_operator. econstructor.
    inv H1. cbn in *. subst. inv HM.
    eexists (_, Datatypes.pair _ _)%embed. split.
    + inv HM0. econstructor. cbn. reflexivity.
      econstructor. eauto.
    + econstructor. instantiate (1 := (_, _)). split; reflexivity.
      inv HM0. econstructor; eauto.
  - intros * Hn.
    destruct m1 as [[se1 q1] rbm1].
    destruct m2 as [se2 q2].
    destruct n1 as [r1 rbn1].
    eexists (_, Datatypes.pair _ _)%embed. split.
    { cbn. rewrite lift_emor_operator. econstructor. }
    destruct Hn as (m2 & HA & HB & HC).
    destruct m2 as [[se3 q3] m].
    inv HA. cbn in HM. inv HM.
    destruct HB as ([se4 [qb mb]] & HB1 & HB2).
    inv HB1. cbn in H0. inv H0.
    inv HB2. cbn in HSE. subst.
    split.
    { eexists (_, Datatypes.pair _ _)%embed. split.
      - econstructor. reflexivity. cbn.
        constructor. eauto.
      - econstructor. instantiate (1 := (_, _)). split; eauto.
        inv HM. econstructor; eauto. }
    intros [r1' rbn1'].
    destruct (classic ((r1', rbn1') = (r1, rbn1))) as [Hrr|Hrr].
    2: { left. cbn. rewrite lift_emor_operator. econstructor. eauto. }
    right. inv Hrr.
    eexists (_, Datatypes.pair _ _)%embed. split. 2: split.
    + econstructor. reflexivity. cbn.
      constructor. eauto.
    + econstructor. instantiate (1 := (_, _)). split; eauto.
      inv HM. econstructor; eauto.
    + intros [cr1 pe1]. apply not_imply_or. intros Hx.
      assert (Hxx: LanguageInterface.match_reply rb_cc tt (r1, rbn1) (cr1, pe1)).
      { eapply rcp_forbid_mr; eauto.
        cbn. reflexivity.
        cbn. constructor. eauto. } clear Hx.
      cbn in Hxx. inv Hxx.
      cbn in *.
      econstructor. instantiate (1 := (_, _)). cbn. split; eauto.
      inv HM. econstructor; eauto.
      cbn. intros (mx & Hmx). 
      specialize (HC (cr1, mx)) as [Hc|Hc].
      * inv Hc. inv Hmx.
        apply HA. econstructor; cbn; eauto.
      * destruct Hc as (mc & Hc1 & Hc2 & Hc).
        specialize (Hc (cr1, mx)) as [Hc|Hc].
        -- inv Hc. destruct mc. destruct p. cbn in *. easy.
        -- inv Hc. cbn in *. subst. inv Hmx.
           apply HN. constructor. eauto.
           Unshelve. all: cbn; exact tt.
Qed.

Lemma ϕ_rb_conv_ref1: ϕ_bq_conv_1 [= ϕ_rb_conv.
Proof.
  unfold ϕ_bq_conv_1, ϕ_rb_conv, E_rb_rb0_conv, deencap.
  (* rewrite m_rb_ref. *)
  (* rewrite assoc1. *)
  (* rewrite vcomp_assoc. *)
  apply vcomp_ref. reflexivity.
  apply ϕ_rb_conv_ref1_helper.
Qed.
(*   rewrite <- pin_join_ref. *)
(*   rewrite <- !vcomp_assoc. *)
(*   rewrite !vcomp_assoc. *)
(*   apply vcomp_ref. reflexivity. *)
(*   apply vcomp_ref. reflexivity. *)
(*   intros c Hc. induction c. *)
(*   - cbn in *. eprod_crush. xinv H. xinv HM. xinv H0. *)
(*     cbn in H1. inv H1. rename s1 into s. rename c1 into c. *)
(*     exists (s, Datatypes.pair c r)%embed. split. repeat constructor. *)
(*     rewrite lift_emor_operator. constructor. *)
(*     exists (s, Datatypes.pair c pe)%embed. split. *)
(*     + econstructor; econstructor; eauto. *)
(*     + econstructor. instantiate (1 := (_, s)). cbn. easy. *)
(*       cbn. econstructor; eauto. *)
(*   - cbn in *. eprod_crush. xinv H. xinv HM. xinv H0. *)
(*     cbn in H2. symmetry in H2. inv H2.  *)
(*     exists (s, Datatypes.pair c1 r0)%embed. split. repeat constructor. *)
(*     rewrite lift_emor_operator. constructor. *)
(*     split. exists (s, Datatypes.pair c1 pe)%embed. split. *)
(*     { econstructor; econstructor; eauto. } *)
(*     { econstructor. instantiate (1 := (_, s)). cbn. easy. *)
(*       cbn. econstructor; eauto. } *)
(*     intros [cr rb1]. apply not_imply_or. intros Hr. *)
(*     exists (s, Datatypes.pair c1 pe)%embed. split. *)
(*     { econstructor; econstructor; eauto. } split. *)
(*     { econstructor. instantiate (1 := (_, s)). cbn. easy. *)
(*       cbn. econstructor; eauto. } *)
(*     intros [cr1 p1]. apply not_imply_or. intros Hr1. *)
(*     econstructor. instantiate (1 := (_, s)). cbn. easy. *)
(*     cbn. constructor. eauto. *)
(*     intros Hr2. cbn in *. destruct Hr2 as (mx & Hmx). inv Hmx. *)
(*     destruct (classic ((c0, r) = (cr, rb1))) as [Hrr|]. *)
(*     2: { apply Hr. rewrite lift_emor_operator. constructor. eauto. } *)
(*     eapply @rcp_forbid_mr with (w := tt) in Hr1. *)
(*     2: { cbn. easy. } 2: { constructor. eauto. } *)
(*     xinv Hrr. xinv Hr1. *)
(*     specialize (H1 (c, m)) as [H1 | H1]. *)
(*     + xinv H1. apply HA. econstructor; eauto. reflexivity. *)
(*     + xinv H1. cbn in *. easy. *)
(*   - cbn in *. eprod_crush. xinv H. xinv HM. xinv H0. *)
(*     cbn in H2. symmetry in H2. inv H2. *)
(*     exists (s, Datatypes.pair c2 r0)%embed. split. repeat constructor. *)
(*     rewrite lift_emor_operator. constructor. *)
(*     split. exists (s, Datatypes.pair c2 pe)%embed. split. *)
(*     { econstructor; econstructor; eauto. } *)
(*     { econstructor. instantiate (1 := (_, s)). cbn. easy. *)
(*       cbn. econstructor; eauto. } *)
(*     intros [cr rb1]. apply not_imply_or. intros Hr. *)
(*     destruct (classic ((c1, r) = (cr, rb1))) as [Hrr|]. *)
(*     2: { exfalso. apply Hr. rewrite lift_emor_operator. constructor. eauto. } *)
(*     xinv Hrr. apply not_imply_or. intros Hx. *)
(*     eapply not_ex_all_not with (n := (s, Datatypes.pair c2 pe)%embed) in Hx. *)
(*     apply not_and_or in Hx as [Hx | Hx]. *)
(*     { exfalso. apply Hx. econstructor. now cbn. *)
(*       cbn. econstructor; eauto. } *)
(*     apply not_and_or in Hx as [Hx | Hx]. *)
(*     { exfalso. apply Hx. econstructor. *)
(*       instantiate (1 := (_, s)). now cbn. *)
(*       cbn. econstructor; eauto. } *)
(*     apply not_all_ex_not in Hx as ((cr3 & p3) & Hx). *)
(*     apply not_or_and in Hx as [Hx1 Hx2]. *)
(*     eapply @rcp_forbid_mr with (w := tt) in Hx1. xinv Hx1. *)
(*     2: { now cbn. } 2: { constructor; eauto. } *)
(*     eapply @rcp_forbid_mr with (w := (_, s)) in Hx2. xinv Hx2. inv H. *)
(*     2: { now cbn. } 2: { constructor; eauto. } *)
(*     specialize (H1 (c0, m)) as [H1|[H1|H1]]. *)
(*     + exfalso. xinv H1. apply HA. *)
(*       econstructor; eauto. reflexivity. *)
(*     + exfalso. xinv H1. cbn in *. easy. *)
(*     + rewrite !regular_conv in H1. *)
(*       rewrite !regular_conv. eauto. *)
(*       * econstructor. split. econstructor. cbn. eauto. *)
(*         constructor. eauto. econstructor. *)
(*         instantiate (1 := (_, s)). now cbn. constructor. eauto. *)
(*       * intros HA. cbn in HA. *)
(*         eprod_crush. specialize (H2 (c0, p3)) as [A | B]. *)
(*         xinv A. apply HN. constructor. eauto. *)
(*         xinv B. apply HN. destruct w. econstructor. *)
(*         constructor. eauto. cbn in HSE. destruct HSE. subst. eauto. *)
(*       * rewrite lift_emor_operator. constructor. *)
(*       * intros HA. xinv HA. cbn in *. easy. *)
(*       * rewrite lift_emor_operator. constructor. *)
(*       * intros Hx. xinv Hx. cbn in *. easy. *)
(*       * constructor. econstructor; eauto. *)
(*       * intros HA. xinv HA. apply HA0. *)
(*         cbn. econstructor; eauto. reflexivity. *)
(*         Unshelve. all: cbn; exact tt. *)
(* Qed. *)

Import CategoricalComp.

Lemma ϕ_bq_rb:
  rsq E0_conv ϕ_bq_conv_2 Π_bq
    (comp_semantics' (Clight.semantics2 bqc) (Clight.semantics2 rbc) sk).
Proof.
  (* rewrite <- ϕ_bq_conv_ref1. *)
  unfold embed_lts_with_sk.
  setoid_rewrite <- cc_comp_ref. rewrite ϕ1'.
  eapply rsq_comp_when. constructor.
  - apply ϕ_bq_with_internals.
  - rewrite ϕ_rb_conv_ref1.
    apply ϕ_rb_with_internals.
Qed.

Global Instance asm_deterministic p: Deterministic (Asm.semantics p).
Proof. apply lts_strat_determ. apply Asm.semantics_determinate. Qed.

Section ASM.

  Context rb_asm (HA1: transf_clight_program rbc = Errors.OK rb_asm).
  Context bq_asm (HA2: transf_clight_program bqc = Errors.OK bq_asm).
  Context (HA0: CategoricalLinkable (Asm.semantics bq_asm) (Asm.semantics rb_asm)).
  Context bq_rb_asm (HA3: Linking.link bq_asm rb_asm = Some bq_rb_asm)
                    (HA4: sk = AST.erase_program bq_rb_asm).

  Definition cc := CAsm.cc_compcert.

  (* ϕ2_1 := ϕ_bq ;; ϕ^cc_bq *)
  Lemma ϕ2_1 : rsq (ϕ_bq_conv_1 ;; cc) (ϕ_bq_conv_2 ;; cc) M_bq (Asm.semantics bq_asm).
  Proof.
    eapply rsq_vcomp.
    3: apply ϕ_bq_with_internals.
    3: {
      eapply fsim_rsq_sk.
      - apply Asm.semantics_determinate.
      - apply clight2_semantic_preservation.
        apply Util.transf_clight_program_match. eauto.
      - eapply (Linking.link_linkorder _ _ _ Hsk).
    }
    all: eauto with typeclass_instances.
  Qed.

  (* ϕ2_2 := ϕ_rb ;; ϕ^cc_rb *)
  Lemma ϕ2_2 : rsq (E0_conv ;; cc) (ϕ_rb_conv ;; cc) Π_rb (Asm.semantics rb_asm).
  Proof.
    eapply rsq_vcomp.
    3: apply ϕ_rb_with_internals.
    3: {
      eapply fsim_rsq_sk.
      - apply Asm.semantics_determinate.
      - apply clight2_semantic_preservation.
        apply transf_clight_program_match. eauto.
      - eapply (Linking.link_linkorder _ _ _ Hsk). }
    all: eauto with typeclass_instances.
  Qed.

  Lemma absort : E0_conv ;; cc [= E0_conv.
  Proof. rewrite <- E0_conv_vcomp. reflexivity. Qed.

  (* ϕ2 := (ϕ_bq ;; ϕ^cc_bq) ⊙ (ϕ_rb ;; ϕ^cc_rb) ⊙ absort *)
  Lemma ϕ2: rsq E0_conv (ϕ_bq_conv_2 ;; cc)
              (M_bq ⊙ Π_rb) (Asm.semantics bq_asm ⊙ Asm.semantics rb_asm).
  Proof.
    rewrite <- absort.
    eapply rsq_comp. 1-2: eauto with typeclass_instances.
    - apply ϕ2_1.
    - rewrite ϕ_rb_conv_ref1. apply ϕ2_2.
  Qed.

  Import -(notations) CallconvAlgebra.

  Lemma asm_link_fsim:
    forward_simulation cc_id cc_id
      (comp_semantics' (Asm.semantics bq_asm) (Asm.semantics rb_asm) sk)
      (Asm.semantics bq_rb_asm).
  Proof.
    eapply open_fsim_ccref. apply cc_compose_id_left. apply cc_compose_id_left.
    eapply compose_forward_simulations.
    eapply categorical_compose_approximation; eauto with typeclass_instances.
    rewrite HA4.
    assert (Hx: (fun i: bool => Asm.semantics (if i then bq_asm else rb_asm)) =
             fun i : bool => if i then Asm.semantics bq_asm else Asm.semantics rb_asm).
    { apply Axioms.functional_extensionality. intros [|]; eauto. }
    rewrite <- Hx.
    eapply AsmLinking.asm_linking. apply HA3.
  Qed.

  Theorem ϕ_bq_rb_asm:
    rsq E0_conv (ϕ_bq_conv_2 ;; cc) Π_bq (Asm.semantics bq_rb_asm).
  Proof.
    rewrite ϕ1'.
    rewrite <- vcomp_vid_r at 1. setoid_rewrite <- vcomp_vid_r at 4.
    eapply rsq_vcomp.
    3: apply ϕ2.
    1-2: eauto with typeclass_instances.
    setoid_rewrite cc_comp_ref.
    rewrite <- cc_conv_id. eapply fsim_rsq_sk.
    apply Asm.semantics_determinate. 2: apply linkorder_refl.
    apply asm_link_fsim.
  Qed.

End ASM.
