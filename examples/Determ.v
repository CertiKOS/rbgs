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

  Ltac find_specialize :=
    match goal with
    | [ H : forall x, ?P x -> _, X : _, H1 : ?P ?X |- _ ] => specialize (H _ H1)
    | [ H : forall x y, ?P x y -> _, X : _, Y : _,  H1 : ?P ?X ?Y |- _ ] => specialize (H _ _ H1)
    | [ H : forall x y z, ?P x y z -> _, X : _, Y : _, Z : _, H1 : ?P ?X ?Y ?Z |- _ ] => specialize (H _ _ _ H1)
    | _ => idtac
    end.

  Ltac expr_determ_solve :=
    repeat find_specialize; try split; f_equal; congruence || easy.

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

Lemma clightp_determinate p :
  determinate (ClightP.clightp2 p).
Proof.
Admitted.


(* Lemma clight_determinate p: determinate (semantics2 p). *)
(* Proof. *)
(*   intros se. split. *)
(*   - intros * Hs1 Hs2. inv Hs1; inv Hs2. *)



(*     admit. *)
(*     (* inv Hs1; inv Hs2; split; eauto. *) *)
(*   - intros s t s' H. inv H; cbn; try lia. *)
(*     eapply Events.external_call_trace_length; eauto. *)
(*     eapply Events.external_call_trace_length; eauto. *)
(*   - intros * Hq1 Hq2. inv Hq1; inv Hq2; easy. *)
(*   - intros * Hq s t Hs. inv Hq; inv Hs.  *)
(*     + cbn in *. subst f. congruence. *)
(*     + cbn in *. subst f. rewrite H in FIND. *)
(*       inv FIND. easy. *)
(*   - intros * Ha1 Ha2. inv Ha1; inv Ha2. *)
(*     subst f. subst f0. rewrite H in H5. inv H5. reflexivity. *)
(*   - intros * Ha1 Ha2. inv Ha1; inv Ha2; easy. *)
(*   - intros * Ha1 s t Hs. inv Ha1; inv Hs. *)
(*   - intros * Hf He. inv Hf; inv He. *)
(*   - intros * Hf1 Hf2. inv Hf1; inv Hf2. easy. *)
(* Admitted. *)

(* Lemma clightp_determinate p: determinate (ClightP.ClightP.clightp2 p). *)
(* Admitted. *)
