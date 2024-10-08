Require Import Relations RelationClasses.
Require Import List.
Require Import compcert.lib.Coqlib.
Require Import compcert.common.LanguageInterface.
Require Import compcert.common.Events.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Smallstep.
Require Import models.Coherence.

Unset Program Cases.
Local Obligation Tactic := cbn.


(** * Coherence spaces for CompCertO semantics *)

(** ** Language interfaces *)

Coercion li_space (li : language_interface) : space :=
  input (query li) ;; output (reply li).

(** ** CompCert events *)

(*
Inductive ev_coh : relation event :=
  | Event_syscall_coh s1 s2 args1 args2 res1 res2 :
      (s1 = s2 -> args1 = args2 -> res1 = res2) ->
      ev_coh (Event_syscall s1 args1 res1) (Event_syscall s2 args2 res2)
  | Event_vload_coh ...

Program Definition Ev :=
  {|
    token := event;
    coh e1 e2 := 
*)


(** * CompCert semantics *)

(** Note that Reddy's object semantics have a rather coarse-grained
  handling of undefined behaviors, which is inherited by our CompCert
  semantics. Silent divergence and undefined behaviors are also
  conflated.

  The preliminary definition below loses information about the domains
  of component, which would make it impossible to define mutually
  recursive horizontal composition in a satisfactory way. However for
  now we don't need it so we don't care. Ultimately we could
  incoroporate it in the type of the semantics by using
  [input (query li) ;; (1 + output (reply li)] instead of [li_space]
  for the codomain.

  Finally, everything in CompCertO happens in the context of a global
  symbol table, so we need to specify one to get the component's
  semantics. Again this could be an [input Genv.symtbl ;; ...] component
  in the interaction but for now this is the simpler approach. *)

(** ** Semantics of transition systems *)

Section LTS.
  Context {liA liB S} (L : lts liA liB S).

  (** [lts_trace s t r] asserts that the transition system [L] reaches
    a final state with reply [r] from the state [s], with the sequence
    of external calls encoded by the trace [t]. *)

  Inductive lts_trace : S -> token !liA -> reply liB -> Prop :=
    | lts_trace_final (s : S) (r : reply liB) :
        final_state L s r ->
        lts_trace s nil r
    | lts_trace_step (s s' : S) (t : token !liA) (r : reply liB) :
        Step L s E0 s' ->
        lts_trace s' t r ->
        lts_trace s t r
    | lts_trace_external s qx rx s' t r :
        at_external L s qx ->
        after_external L s rx s' ->
        lts_trace s' t r ->
        lts_trace s ((qx, rx) :: t) r.

  Inductive lts_lmaps : token !liA -> token liB -> Prop :=
    | lts_lmaps_intro q s t r :
        valid_query L q = true ->
        initial_state L q s ->
        lts_trace s t r ->
        lts_lmaps t (q, r).

End LTS.

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

Section SEMANTICS.
  Context {liA liB} (L : semantics liA liB) (HL : determinate L).

  Lemma trace_determ se s es es' r r' :
    list_coh liA es es' ->
    lts_trace (L se) s es r ->
    lts_trace (L se) s es' r' ->
    es = es' /\ r = r'.
  Proof.
    intros coh h h'.
    revert es' coh h'.
    induction h; intros es' coh lts; inversion lts; subst.
    + determ_solve (sd_final_determ (HL se)).
    + determ_solve (sd_final_nostep (HL se)).
    + determ_solve (sd_final_noext (HL se)).
    + determ_solve (sd_final_nostep (HL se)).
    + determ_solve (sd_determ_2 (HL se)).
      eapply IHh. apply coh. apply H1.
    + determ_solve (sd_at_external_nostep (HL se)).
    + determ_solve (sd_final_noext (HL se)).
    + determ_solve (sd_at_external_nostep (HL se)).
    + specialize (IHh t0).
      determ_solve (sd_at_external_determ (HL se)).
      inversion coh as [ | | ? ? ? ? cohx cohxs]; subst.
      destruct cohx as [cohq cohr].
      exploit cohr. auto. intros <-.
      determ_solve (sd_after_external_determ (HL se)).
      split; f_equal; apply IHh; try apply cohxs; auto.
  Qed.

  Program Definition compcerto_lmap se : !liA --o liB :=
    {|
      has '(t, u) := lts_lmaps (L se) t u;
    |}.
  Next Obligation.
    intros se [eas [qb rb]] [eas' [qb' rb']] lmap lmap' coheas.
    split.
    - split; auto.
      intros <-.
      inversion lmap as [? ? ? ? valid_q init_q transition_q]. subst.
      inversion lmap' as [? ? ? ? valid_q' init_q' transition_q']. subst.
      determ_solve (sd_initial_determ (HL se)).
      exploit trace_determ.
      exact coheas. exact transition_q. exact transition_q'.
      intuition.
    - intros h. destruct h.
      inversion lmap as [? ? ? ? valid_q init_q transition_q]. subst.
      inversion lmap' as [? ? ? ? valid_q' init_q' transition_q']. subst.
      determ_solve (sd_initial_determ (HL se)).
      exploit trace_determ.
      exact coheas. exact transition_q. exact transition_q'.
      intuition.
  Qed.
End SEMANTICS.

(** ** Clight semantics *)

(** As an example, here is the semantics of Clight programs in terms
  of linear maps. *)

Require Clight.

(** *** Proof of determinism *)

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
    (forall a b1 ofs1 bf,
        Clight.eval_lvalue ge e le m a b1 ofs1 bf ->
        forall b2 ofs2,
          Clight.eval_lvalue ge e le m a b2 ofs2 bf ->
          b1 = b2 /\ ofs1 = ofs2).
  Proof.
    apply Clight.eval_expr_lvalue_ind.
    - inversion 1; expr_determ_solve.
    - inversion 1; expr_determ_solve.
    - inversion 1; expr_determ_solve.
    - inversion 1; expr_determ_solve.
    - inversion 2; expr_determ_solve.
    - admit.
    - intros. inversion H2; expr_determ_solve.
    - intros. inversion H4; expr_determ_solve.
    - intros. inversion H2; expr_determ_solve.
    - inversion 1; expr_determ_solve.
    - inversion 1; expr_determ_solve.
    - admit.
    - inversion 2; expr_determ_solve.
    - inversion 3; expr_determ_solve.
    - inversion 3; expr_determ_solve.
    - intros. inversion H4; expr_determ_solve.
    - intros. inversion H4; expr_determ_solve.
  Admitted.

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
    forall a b1 ofs1 bf,
      Clight.eval_lvalue ge e le m a b1 ofs1 bf ->
      forall b2 ofs2,
        Clight.eval_lvalue ge e le m a b2 ofs2 bf ->
        b1 = b2 /\ ofs1 = ofs2.
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

Lemma assign_loc_determ ge t m loc ofs v bf m1 m2:
    Clight.assign_loc ge t m loc ofs bf v m1 ->
    Clight.assign_loc ge t m loc ofs bf v m2 ->
    m1 = m2.
Proof.
  inversion 1; inversion 1; try congruence.
  subst. admit. (* store_bitfield *)
Admitted.

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

Lemma func_entry1_determ ge f vargs m e1 le1 m1 e2 le2 m2:
  Clight.function_entry1 ge f vargs m e1 le1 m1 ->
  Clight.function_entry1 ge f vargs m e2 le2 m2 ->
  e1 = e2 /\ le1 = le2 /\ m1 = m2.
Proof.
  inversion 1. inversion 1.
  determ_solve alloc_variables_determ.
  firstorder. congruence.
  determ_solve bind_parameters_determ.
Qed.

Ltac false_solve :=
  match goal with
  | [ H : _ \/ _ |- _ ] => inversion H; easy
  | _ => idtac
  end.

Hint Constructors match_traces.
Ltac autoc := auto || congruence || easy.

Lemma step_determ p se s t1 s1 t2 s2:
  Step ((Clight.semantics1 p) se) s t1 s1 ->
  Step ((Clight.semantics1 p) se) s t2 s2 ->
  match_traces se t1 t2 /\ (t1 = t2 -> s1 = s2).
Proof.
  intros step1 step2.
  inversion step1; subst;
    inversion step2; subst; false_solve;
      try (split; autoc).
  + determ_solve eval_expr_determ.
    admit. (*
    determ_solve eval_lvalue_determ.
    assert (v = v1) as <- by congruence.
    determ_solve assign_loc_determ.
    split; autoc.
            *)
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
    determ_solve func_entry1_determ.
    split; autoc.
  + assert (ef = ef0) by congruence. subst.
    determ_solve external_call_determ.
    split. apply H0.
    intros. exploit (proj2 H0). auto.
    intros [<- <-]. auto.
Admitted.

Lemma clight_single_event p se:
  single_events ((Clight.semantics1 p) se).
Proof.
  unfold single_events. intros.
  inversion H; auto; eapply external_call_trace_length; eauto.
Qed.

Hint Unfold globalenv.
Hint Unfold Clight.globalenv.

Lemma clight_determinate p :
  determinate (Clight.semantics1 p).
Proof.
  split.
  - apply step_determ.
  - apply clight_single_event.
  - inversion 1; inversion 1; congruence.
  - inversion 1.
    replace (Clight.globalenv se p) with (globalenv ((Clight.semantics1 p) se)) in H0 by auto.
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

(** *** Coherence space Clight semantics *)

Definition clight (p : Clight.program) se : !li_c --o li_c :=
  compcerto_lmap (Clight.semantics1 p) (clight_determinate p) se.

(** ** Soundness of forward simulations *)

(** Since for now, our model doesn't support abstraction, we can only
  consider simulations which use the [cc_id] simulation convention. *)

Section FSIM.
  Context {liA liB} (L1 L2 : semantics liA liB).
  Context (H1 : determinate L1).
  Context (H2 : determinate L2).
  Context (FSIM : forward_simulation 1 1 L1 L2).
  Context (se : Genv.symtbl) (Hse : Genv.valid_for (skel L1) se).

  (** XXX: we need a notion of refinement on linear maps themselves,
    or perhaps just define linear maps as cliques in the function
    space. *)

  Lemma fsim_sound :
    ref (compcerto_lmap L1 H1 se) (compcerto_lmap L2 H2 se).
  Proof.
    intros [t u] Ht. cbn in *.
    destruct FSIM as [[ind ord match_states _ H _]]. cbn in *.
    specialize (H se se tt eq_refl Hse).
    destruct Ht as [q s1 t1 r Hq1 Hs1 Ht1].
    edestruct @fsim_match_initial_states as (i & s2 & Hs2 & Hs);
      eauto; try reflexivity.
    econstructor.
    - erewrite fsim_match_valid_query; eauto. reflexivity.
    - eauto.
    - clear - H Hs Ht1. revert i s2 Hs.
      induction Ht1; cbn; intros.
      + (* final state *)
        edestruct @fsim_match_final_states as (xr & Hs2 & Hxr); eauto.
        destruct Hxr.
        constructor; auto.
      + (* step *)
        edestruct @simulation_star as (j & s2' & Hs2' & Hs'); eauto using star_one.
        revert Hs'. pattern s2, s2'.
        eapply star_E0_ind; eauto using lts_trace_step.
      + (* external interaction *)
        edestruct @fsim_match_external as (w & xq & Hq2 & Hxq & _ & Hrx); eauto.
        destruct Hxq.
        edestruct Hrx as (j & s2' & Hs2' & Hs'); cbn; eauto using lts_trace_external.
  Qed.
End FSIM.
