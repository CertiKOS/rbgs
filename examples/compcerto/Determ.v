Require Import Relations RelationClasses.
Require Import List.
Require Import compcert.lib.Coqlib.
Require Import compcert.common.LanguageInterface.
Require Import compcert.common.Events.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Smallstep.

Unset Program Cases.
Local Obligation Tactic := cbn.

Ltac determ_solve' :=
  auto ||
       match goal with
       | [ |- False -> _ ] => inversion 1
       | [ |- _ = _ -> _ ] => intros <-
       | [ |- _ = _ /\ _ = _ -> _ ] => intros [<- <-]
       | [ |- _ = _ /\ _ = _ /\ _ = _ -> _ ] => intros [<- [<- <-]]
       | [ |- _ -> _ ] => intros
       end.

Ltac determ_solve determ :=
  match goal with
  | [ P : _ , Q : _ |- _ ] =>
    exploit determ;
    [ exact P | exact Q | determ_solve' ]
  | _ => fail
  end.


Ltac find_specialize :=
  match goal with
  | [ H : forall x, ?P x -> _, X : _, H1 : ?P ?X |- _ ] => specialize (H _ H1)
  | [ H : forall x y, ?P x y -> _, X : _, Y : _,  H1 : ?P ?X ?Y |- _ ] => specialize (H _ _ H1)
  | [ H : forall x y z, ?P x y z -> _, X : _, Y : _, Z : _, H1 : ?P ?X ?Y ?Z |- _ ] => specialize (H _ _ _ H1)
  | _ => idtac
  end.

Ltac expr_determ_solve :=
  repeat find_specialize; try split; f_equal; congruence || easy.

Require Clight.

Section EXPR_DETERM.
  Variable ge: Clight.genv.
  Variable e: Clight.env.
  Variable le: Clight.temp_env.
  Variable m: Memory.Mem.mem.

  Lemma load_bitfield_determ t sz sgn a b mem v v1 v2 :
    Cop.load_bitfield t sz sgn a b mem v v1 ->
    Cop.load_bitfield t sz sgn a b mem v v2 ->
    v1 = v2.
  Proof.
    destruct 1; inversion 1; subst; congruence.
  Qed.

  Lemma deref_loc_determ t mem loc ofs bf v1 v2:
    Clight.deref_loc t mem loc ofs bf v1 ->
    Clight.deref_loc t mem loc ofs bf v2 ->
    v1 = v2.
  Proof.
    induction 1; inversion 1; subst; try congruence.
    eapply load_bitfield_determ; eauto.
  Qed.

  Lemma expr_determ:
    (forall a v1,
        Clight.eval_expr ge e le m a v1 ->
        forall v2,
          Clight.eval_expr ge e le m a v2 ->
          v1 = v2)
    /\
    (forall a b1 ofs1 bf1,
        Clight.eval_lvalue ge e le m a b1 ofs1 bf1 ->
        forall b2 ofs2 bf2,
          Clight.eval_lvalue ge e le m a b2 ofs2 bf2 ->
          b1 = b2 /\ ofs1 = ofs2 /\ bf1 = bf2).
  Proof.
    apply Clight.eval_expr_lvalue_ind.
    - inversion 1; expr_determ_solve.
    - inversion 1; expr_determ_solve.
    - inversion 1; expr_determ_solve.
    - inversion 1; expr_determ_solve.
    - inversion 2; expr_determ_solve.
    - intros. inv H1; expr_determ_solve.
    - intros. inversion H2; expr_determ_solve.
    - intros. inversion H4; expr_determ_solve.
    - intros. inversion H2; expr_determ_solve.
    - inversion 1; expr_determ_solve.
    - inversion 1; expr_determ_solve.
    - intros. inv H2; inv H.
      + find_specialize. destruct H0 as [<- [<- <-]].
        determ_solve deref_loc_determ.
      + find_specialize. destruct H0 as [<- [<- <-]].
        determ_solve deref_loc_determ.
      + find_specialize. destruct H0 as [<- [<- <-]].
        determ_solve deref_loc_determ.
      + find_specialize. destruct H0 as [<- [<- <-]].
        determ_solve deref_loc_determ.
      + find_specialize. destruct H0 as [<- [<- <-]].
        determ_solve deref_loc_determ.
    - inversion 2; expr_determ_solve.
    - inversion 3; expr_determ_solve.
    - inversion 3; try expr_determ_solve.
      subst. specialize (H0 _ H7). inv H0. easy.
    - intros. inv H4.
      + find_specialize. inv H0. repeat apply conj; congruence.
      + find_specialize. inv H0. repeat apply conj; congruence.
    - intros. inv H4.
      + find_specialize. inv H0. repeat apply conj; congruence.
      + find_specialize. inv H0. repeat apply conj; congruence.
  Qed.

  Lemma eval_expr_determ:
    forall a v1,
      Clight.eval_expr ge e le m a v1 ->
        forall v2,
          Clight.eval_expr ge e le m a v2 ->
          v1 = v2.
  Proof.
    intros. eapply expr_determ; eauto.
  Qed.

  Lemma eval_lvalue_determ:
    forall a b1 ofs1 bf1,
      Clight.eval_lvalue ge e le m a b1 ofs1 bf1 ->
      forall b2 ofs2 bf2,
        Clight.eval_lvalue ge e le m a b2 ofs2 bf2 ->
        b1 = b2 /\ ofs1 = ofs2 /\ bf1 = bf2.
  Proof.
    intros. eapply expr_determ; eauto.
  Qed.

  Lemma eval_exprlist_determ es ty vs1 vs2:
    Clight.eval_exprlist ge e le m es ty vs1 ->
    Clight.eval_exprlist ge e le m es ty vs2 ->
    vs1 = vs2.
  Proof.
    intros eval1. revert vs2.
    induction eval1.
    - inversion 1. auto.
    - intros vs2 eval2.
      inversion eval2; subst.
      determ_solve eval_expr_determ.
      exploit IHeval1.
      exact H8. congruence.
  Qed.
End EXPR_DETERM.

Ltac Equalities :=
  match goal with
  | [ H1: ?a = ?b, H2: ?a = ?c |- _ ] =>
      rewrite H1 in H2; inv H2; Equalities
  | _ => idtac
  end.

Lemma store_bitfield_determ t sz sg pos width m addr v m1 m2 v1 v2:
  Cop.store_bitfield t sz sg pos width m addr v m1 v1 ->
  Cop.store_bitfield t sz sg pos width m addr v m2 v2 ->
  m1 = m2 /\ v1 = v2.
Proof. inversion 1; inversion 1. subst. Equalities. easy. Qed.

Lemma assign_loc_determ ge t m loc ofs v bf m1 m2:
    Clight.assign_loc ge t m loc ofs bf v m1 ->
    Clight.assign_loc ge t m loc ofs bf v m2 ->
    m1 = m2.
Proof.
  inversion 1; inversion 1; try congruence.
  subst. determ_solve store_bitfield_determ. easy.
Qed.

Lemma alloc_variables_determ ge e m vars e1 e2 m1 m2:
    Clight.alloc_variables ge e m vars e1 m1 ->
    Clight.alloc_variables ge e m vars e2 m2 ->
    e1 = e2 /\ m1 = m2.
Proof.
  intros alloc1. revert e2 m2.
  induction alloc1.
  - inversion 1. auto.
  - inversion 1; subst.
    rewrite H in H8. injection H8. intros <- <-.
    exploit IHalloc1. exact H9. auto.
Qed.

Lemma bind_parameters_determ ge e m params vargs m1 m2:
  Clight.bind_parameters ge e m params vargs m1 ->
  Clight.bind_parameters ge e m params vargs m2 ->
  m1 = m2.
Proof.
  intros bind1. revert m2.
  induction bind1.
  - inversion 1. auto.
  - inversion 1; subst.
    assert (b = b0) by congruence. subst.
    determ_solve assign_loc_determ.
    exploit IHbind1. exact H11. auto.
Qed.

Lemma func_entry2_determ ge f vargs m e1 le1 m1 e2 le2 m2:
  Clight.function_entry2 ge f vargs m e1 le1 m1 ->
  Clight.function_entry2 ge f vargs m e2 le2 m2 ->
  e1 = e2 /\ le1 = le2 /\ m1 = m2.
Proof.
  inversion 1. inversion 1.
  determ_solve alloc_variables_determ.
  firstorder. congruence.
Qed.

Ltac false_solve :=
  match goal with
  | [ H : _ \/ _ |- _ ] => inversion H; easy
  | _ => idtac
  end.

Local Hint Constructors match_traces : core.
Ltac autoc := auto || congruence || easy.

Lemma step_determ p se s t1 s1 t2 s2:
  Step ((Clight.semantics2 p) se) s t1 s1 ->
  Step ((Clight.semantics2 p) se) s t2 s2 ->
  match_traces se t1 t2 /\ (t1 = t2 -> s1 = s2).
Proof.
  intros step1 step2.
  inversion step1; subst;
    inversion step2; subst; false_solve;
      try (split; autoc).
  + determ_solve eval_expr_determ.
    determ_solve eval_lvalue_determ.
    Equalities.
    determ_solve assign_loc_determ.
    split; autoc.
  + determ_solve eval_expr_determ.
    split; auto.
  + determ_solve eval_expr_determ.
    assert (tyargs0 = tyargs) by congruence. subst.
    determ_solve eval_exprlist_determ.
    split; auto.
  + determ_solve eval_exprlist_determ.
    determ_solve external_call_determ.
    split. apply H1.
    intros. exploit (proj2 H1).
    auto. intros [<- <-]. auto.
  + determ_solve eval_expr_determ.
    split. auto.
    assert (b = b0) by congruence. subst; auto.
  + split; try autoc.
    determ_solve eval_expr_determ. autoc.
  + determ_solve eval_expr_determ. split; autoc.
  + assert (f = f0) by congruence. subst.
    determ_solve func_entry2_determ.
    split; autoc.
  + assert (ef = ef0) by congruence. subst.
    determ_solve external_call_determ.
    split. apply H0.
    intros. exploit (proj2 H0). auto.
    intros [<- <-]. auto.
Qed.

Lemma clight_single_event p se:
  single_events ((Clight.semantics2 p) se).
Proof.
  unfold single_events. intros.
  inversion H; auto; eapply external_call_trace_length; eauto.
Qed.

Local Hint Unfold globalenv Clight.globalenv : core.

Lemma clight_determinate p :
  determinate (Clight.semantics2 p).
Proof.
  split.
  - apply step_determ.
  - apply clight_single_event.
  - inversion 1; inversion 1; congruence.
  - inversion 1.
    replace (Clight.globalenv se p) with (globalenv ((Clight.semantics2 p) se)) in H0 by auto.
    inversion 1; subst; rewrite H0 in FIND; subst f.
    + easy.
    + injection FIND. intros <- <- <- <-.
      easy.
  - inversion 1; inversion 1; subst. f_equal.
    assert (f = f0) by congruence.
    subst f f0. congruence.
  - inversion 1; inversion 1; subst. auto.
  - inversion 1; inversion 1.
  - inversion 1; inversion 1.
  - inversion 1; inversion 1; subst. auto.
Qed.

(* ----------------- ClightP determinate ---------------------- *)

Require Import ClightP.

Section EXPR_DETERM.
  Variable ge: ClightP.genv.
  Variable e: Clight.env.
  Variable le: Clight.temp_env.
  Variable m: Memory.Mem.mem.
  Variable ce: Ctypes.composite_env.
  Variable pe: PEnv.penv.

  Lemma pread_val_determ pv l v1 v2 ty1 ty2:
    PEnv.pread_val ce pv l v1 ty1 ->
    PEnv.pread_val ce pv l v2 ty2 ->
    v1 = v2 /\ ty1 = ty2.
  Proof.
    intros H1 H2. revert v2 ty2 H2. induction H1; intros.
    - inv H2; easy.
    - inv H2; find_specialize. easy.
    - inv H3. clear H1. Equalities. find_specialize. easy.
  Qed.

  Lemma pread_determ id l v1 v2 ty1 ty2:
    PEnv.pread ce pe id l v1 ty1 ->
    PEnv.pread ce pe id l v2 ty2 ->
    v1 = v2 /\ ty1 = ty2.
  Proof.
    intros H1 H2. inv H1; inv H2. Equalities.
    eapply pread_val_determ; eauto.
  Qed.

  Lemma clightp_expr_determ:
    (forall a v1,
      ClightP.eval_expr ce ge e le pe m a v1 ->
      forall v2,
        ClightP.eval_expr ce ge e le pe m a v2 ->
        v1 = v2) /\
    (forall a b1 ofs1 bf1,
      ClightP.eval_lvalue ce ge e le pe m a b1 ofs1 bf1 ->
      forall b2 ofs2 bf2,
        ClightP.eval_lvalue ce ge e le pe m a b2 ofs2 bf2 ->
        b1 = b2 /\ ofs1 = ofs2 /\ bf1 = bf2) /\
    (forall a id1 l1,
      ClightP.eval_loc ce ge e le pe m a id1 l1 ->
      forall id2 l2,
        ClightP.eval_loc ce ge e le pe m a id2 l2 ->
        id1 = id2 /\ l1 = l2).
  Proof.
    apply ClightP.eval_expr_lvalue_loc_ind.
    - inversion 1; expr_determ_solve.
    - inversion 1; expr_determ_solve.
    - inversion 1; expr_determ_solve.
    - inversion 1; expr_determ_solve.
    - inversion 2; expr_determ_solve.
    - intros. inv H1; expr_determ_solve.
    - intros. inversion H2; expr_determ_solve.
    - intros. inversion H4; expr_determ_solve.
    - intros. inversion H2; expr_determ_solve.
    - inversion 1; expr_determ_solve.
    - inversion 1; expr_determ_solve.
    - intros. inv H2; inv H.
      6-10: inv H3.
      + find_specialize. destruct H0 as [<- [<- <-]].
        determ_solve deref_loc_determ.
      + find_specialize. destruct H0 as [<- [<- <-]].
        determ_solve deref_loc_determ.
      + find_specialize. destruct H0 as [<- [<- <-]].
        determ_solve deref_loc_determ.
      + find_specialize. destruct H0 as [<- [<- <-]].
        determ_solve deref_loc_determ.
      + find_specialize. destruct H0 as [<- [<- <-]].
        determ_solve deref_loc_determ.
    - intros. inv H; inv H3. 1,3,5: inv H.
      + find_specialize. destruct H0 as [<- <-].
        determ_solve pread_determ. easy.
      + find_specialize. destruct H0 as [<- <-].
        determ_solve pread_determ. easy.
      + find_specialize. destruct H0 as [<- <-].
        determ_solve pread_determ. easy.
    - inversion 2; expr_determ_solve.
    - inversion 3; expr_determ_solve.
    - inversion 3; try expr_determ_solve.
      subst. specialize (H0 _ H7). inv H0. easy.
    - intros. inv H4.
      + find_specialize. inv H0. repeat apply conj; congruence.
      + find_specialize. inv H0. repeat apply conj; congruence.
    - intros. inv H4.
      + find_specialize. inv H0. repeat apply conj; congruence.
      + find_specialize. inv H0. repeat apply conj; congruence.
    - intros. inv H1. split; congruence.
    - intros. inv H1. find_specialize. find_specialize.
      destruct H. split; congruence.
    - intros. inv H0. find_specialize.
      destruct H. split; congruence.
  Qed.

  Lemma clightp_eval_expr_determ:
    forall a v1,
      ClightP.eval_expr ce ge e le pe m a v1 ->
      forall v2,
        ClightP.eval_expr ce ge e le pe m a v2 ->
        v1 = v2.
  Proof. apply clightp_expr_determ. Qed.

  Lemma clightp_eval_lvalue_determ:
    forall a b1 ofs1 bf1,
      ClightP.eval_lvalue ce ge e le pe m a b1 ofs1 bf1 ->
      forall b2 ofs2 bf2,
        ClightP.eval_lvalue ce ge e le pe m a b2 ofs2 bf2 ->
        b1 = b2 /\ ofs1 = ofs2 /\ bf1 = bf2.
  Proof. apply clightp_expr_determ. Qed.

  Lemma clightp_eval_loc_determ:
    forall a id1 l1,
      ClightP.eval_loc ce ge e le pe m a id1 l1 ->
      forall id2 l2,
        ClightP.eval_loc ce ge e le pe m a id2 l2 ->
        id1 = id2 /\ l1 = l2.
  Proof. apply clightp_expr_determ. Qed.

  Lemma clightp_eval_exprlist_determ es ty vs1 vs2:
    ClightP.eval_exprlist ce ge e le pe m es ty vs1 ->
    ClightP.eval_exprlist ce ge e le pe m es ty vs2 ->
    vs1 = vs2.
  Proof.
    intros eval1. revert vs2.
    induction eval1.
    - inversion 1. auto.
    - intros vs2 eval2.
      inversion eval2; subst.
      determ_solve clightp_eval_expr_determ.
      exploit IHeval1.
      exact H8. congruence.
  Qed.

End EXPR_DETERM.

Lemma clightp_alloc_variables_determ ge e m vars e1 e2 m1 m2:
    ClightP.alloc_variables ge e m vars e1 m1 ->
    ClightP.alloc_variables ge e m vars e2 m2 ->
    e1 = e2 /\ m1 = m2.
Proof.
  intros alloc1. revert e2 m2.
  induction alloc1.
  - inversion 1. auto.
  - inversion 1; subst.
    rewrite H in H8. injection H8. intros <- <-.
    exploit IHalloc1. exact H9. auto.
Qed.

Lemma clightp_func_entry2_determ ge f vargs m e1 le1 m1 e2 le2 m2:
  ClightP.function_entry2 ge f vargs m e1 le1 m1 ->
  ClightP.function_entry2 ge f vargs m e2 le2 m2 ->
  e1 = e2 /\ le1 = le2 /\ m1 = m2.
Proof.
  inversion 1. inversion 1.
  determ_solve clightp_alloc_variables_determ.
  firstorder. congruence.
Qed.

Lemma pwrite_val_determ ce old_pv l v new_pv1 ty1 new_pv2 ty2:
  PEnv.pwrite_val ce old_pv l v new_pv1 ty1 ->
  PEnv.pwrite_val ce old_pv l v new_pv2 ty2 ->
  new_pv1 = new_pv2 /\ ty1 = ty2.
Proof.
  intros H1 H2. revert new_pv2 ty2 H2. induction H1; intros.
  - inv H2. easy.
  - inv H4. find_specialize. destruct IHpwrite_val. subst.
    split; eauto.
  - inv H5. Equalities. find_specialize.
    destruct IHpwrite_val. subst.
    Equalities. easy.
Qed.

Lemma pwrite_determ ce pe id l v pe1 pe2 ty1 ty2:
  PEnv.pwrite ce pe id l v pe1 ty1 ->
  PEnv.pwrite ce pe id l v pe2 ty2 ->
  pe1 = pe2 /\ ty1 = ty2.
Proof.
  intros H1 H2. inv H1. inv H2. Equalities.
  determ_solve pwrite_val_determ. easy.
Qed.

Lemma clightp_step_determ p se s t1 s1 t2 s2:
  Step ((ClightP.clightp2 p) se) s t1 s1 ->
  Step ((ClightP.clightp2 p) se) s t2 s2 ->
  match_traces se t1 t2 /\ (t1 = t2 -> s1 = s2).
Proof.
  intros step1 step2.
  inversion step1; subst;
    inversion step2; subst; false_solve;
      try (split; autoc).
  + determ_solve clightp_eval_expr_determ.
    determ_solve clightp_eval_lvalue_determ.
    Equalities.
    determ_solve assign_loc_determ.
    split; autoc.
  + determ_solve clightp_eval_expr_determ.
    split; auto.
  + determ_solve clightp_eval_expr_determ.
    determ_solve clightp_eval_loc_determ.
    determ_solve pwrite_determ. destruct H4.
    split; eauto. congruence.
  + determ_solve clightp_eval_expr_determ.
    assert (tyargs0 = tyargs) by congruence. subst.
    determ_solve clightp_eval_exprlist_determ.
    split; auto.
  + determ_solve clightp_eval_exprlist_determ.
    determ_solve external_call_determ.
    split. apply H1.
    intros. exploit (proj2 H1).
    auto. intros [<- <-]. auto.
  + determ_solve clightp_eval_expr_determ.
    split. auto.
    assert (b = b0) by congruence. subst; auto.
  + split; try autoc.
    determ_solve clightp_eval_expr_determ. autoc.
  + determ_solve clightp_eval_expr_determ. split; autoc.
  + assert (f = f0) by congruence. subst.
    determ_solve clightp_func_entry2_determ.
    split; autoc.
  + assert (ef = ef0) by congruence. subst.
    determ_solve external_call_determ.
    split. apply H0.
    intros. exploit (proj2 H0). auto.
    intros [<- <-]. auto.
Qed.

Lemma clightp_determinate p :
  determinate (ClightP.clightp2 p).
Proof.
  intros se. split.
  - intros * Hs1 Hs2. eapply clightp_step_determ; eauto.
  - intros s t s' H. inv H; cbn; try lia.
    eapply Events.external_call_trace_length; eauto.
    eapply Events.external_call_trace_length; eauto.
  - intros * Hq1 Hq2. inv Hq1; inv Hq2; easy.
  - intros * Hq s t Hs. inv Hq; inv Hs.
    + cbn in *. subst f. congruence.
    + cbn in *. subst f. rewrite H in FIND.
      inv FIND. easy.
  - intros * Ha1 Ha2. inv Ha1; inv Ha2.
    subst f. subst f0. rewrite H in H6. inv H6. reflexivity.
  - intros * Ha1 Ha2. inv Ha1; inv Ha2; easy.
  - intros * Ha1 s t Hs. inv Ha1; inv Hs.
  - intros * Hf He. inv Hf; inv He.
  - intros * Hf1 Hf2. inv Hf1; inv Hf2. easy.
Qed.

(* ----------------- Lifting determinate ---------------------- *)

Require Import Lifting Relators.

Ltac eprod_crush :=
  cbn in *;
  repeat
    (match goal with
     | [ H: ?a * ?b |- _ ] => destruct H;cbn [fst snd] in *; subst
     | [ H: (?a, ?b) = (?c, ?d) |- _ ] => inv H
     | [ H: (?x * ?y)%rel _ _ |- _] => destruct H; cbn [fst snd] in *; subst
     | [ H: ?x /\ ?y |- _] => destruct H
     | [ H: (exists _, _) |- _] => destruct H
     | [ H: unit |- _] => destruct H
     end).

Lemma lifting_determinate {liA liB K} (L: semantics liA liB):
  determinate L -> determinate (L@K).
Proof.
  intros HL se. specialize (HL se). split; intros; eprod_crush; subst.
  - exploit @sd_determ. apply HL. apply H. apply H0.
    intros [Hs1 Hs2]. split; eauto. intros; f_equal; eauto.
  - intros s * Hs. eprod_crush. subst. eapply sd_traces; eauto.
  - f_equal. eapply sd_initial_determ; eauto.
  - intros t x Hs. eprod_crush. subst. eapply sd_at_external_nostep; eauto.
  - f_equal. eapply sd_at_external_determ; eauto.
  - f_equal. eapply sd_after_external_determ; eauto.
  - intros t x Hs. eprod_crush. subst. eapply sd_final_nostep; eauto.
  - eapply sd_final_noext; eauto.
  - f_equal; eapply sd_final_determ; eauto.
Qed.
