Require Import FMapPositive.
Require Import Relation_Operators Operators_Properties.
Require Import Program.
Require Import Classical.

Require Import coqrel.LogicalRelations.
Require Import interfaces.Category.
Require Import interfaces.Functor.
Require Import interfaces.MonoidalCategory.
Require Import models.EffectSignatures.


(** * Linearization-based Concurrent Certified Abstraction Layers *)

Module LinCCALBase <: Category.

  Module TMap := PositiveMap.
  Notation tid := TMap.key.
  Notation tmap := TMap.t.

  (** ** Concurrent object specifications *)

  Module Spec.

    (** *** Definition *)

    (** For simplicity, we use linearized atomic specifications and
      specify correctness directly in terms of that model. In their
      linearized form, the specifications are deterministic, however
      we allow both undefined and unimplementable behaviors.
      Undefined behaviors ([bot]) release the implementation of any
      obligation, and are usually a consequence of illegal actions
      by the client (for example, a thread acquiring a lock twice).
      Conversely, unimplementable behaviors ([top]) are simply
      impossible for an implementation to obey; this is usually
      meant to force a different linearization order. For example,
      in the atomic specification, acquiring a lock which is already
      held by a different thread will yield an unimplementable spec.
      However, a lock implementation can still obey the
      specification by delaying the linearization of [acquire] until
      the lock is released by the thread currently holding it. *)

    Variant outcome {E : Sig.t} {m : Sig.op E} {X : Type} :=
      | bot
      | top
      | ret (n : Sig.ar m) (x : X).

    Arguments outcome : clear implicits.

    (** Our specifications give an outcome of this kind
      for every possible thread and operation of [E]. *)

    CoInductive t {E} :=
      {
        next : tid -> forall m, outcome E m (@t E);
      }.

    Arguments t : clear implicits.

    (** *** State-based representations *)

    (** More generally, behaviors of this kind can be described by
      transition systems with the same shape as [next]. *)

    Notation lts E A := (A -> tid -> forall m, outcome E m A).

    (** In fact, [next] constitutes a final coalgebra over specifications,
      meaning that states in any transition system can be mapped to
      specifications with the same behavior. *)

    CoFixpoint gen {E A} (α : lts E A) x : t E :=
      {| next t m := match α x t m with
                     | bot => bot
                     | top => top
                     | ret n y => ret n (gen α y)
                     end |}.

    (** *** Tensor product *)

    Import (canonicals) Sig.Plus.

    Definition tens_lts {E1 E2} : lts (Sig.Plus.omap E1 E2) (t E1 * t E2) :=
      fun Σ t m =>
        match m with
        | inl m1 => match next (fst Σ) t m1 with
                    | bot => bot
                    | top => top
                    | ret n Σ1 => ret (m := inl m1) n (Σ1, snd Σ)
                    end
        | inr m2 => match next (snd Σ) t m2 with
                    | bot => bot
                    | top => top
                    | ret n Σ2 =>
                        ret (m := inr m2) n (fst Σ, Σ2)
                    end
        end.

    Definition tens {E1 E2} (Σ1 : t E1) (Σ2 : t E2) :=
      gen tens_lts (Σ1, Σ2).

  End Spec.

  Notation spec := Spec.t.

  Declare Scope spec_scope.
  Delimit Scope spec_scope with spec.
  Bind Scope spec_scope with Spec.t.
  Infix "*" := Spec.tens : spec_scope.

  (** ** Implementation states *)

  (** We use regular maps [Reg.m] to model implementations of a given
    overlay specification in terms of a given underlay specification.
    A regular map associates with each overlay operation a term of the
    underlay signature, interpreted as a strategy tree or a computation
    in the free monad, in the style of algebraic effect frameworks.

    To express correctness, we use the following execution model.
    When a method [ts_op] is invoked in a particular thread, we use
    the implementation to initialize a computation [ts_prog] for that
    thread.  Whenever the thread is scheduled, we use the (linearized,
    atomic) underlay specification to perform the next underlay call
    in the computation. Eventually, the computation will produce a
    result and return from the overlay call.

    It remains to compare this behavior to the one prescribed by the
    overlay specification. To prove that the implementation's behavior
    linearizes to the atomic overlay specification, we must show there
    is a way to pick a particular point in time, as a method is being
    executed, when its atomic call and return will be recoded as
    occuring from the point of view of the overlay client. We match
    the call against the overlay specification at that time and keep
    track of the result [ts_res] that we have committed to. As the
    method's execution proceeds and eventually terminates, we will
    have to show that the actual outcome matches the recorded result.

    Concretely, our state will consist of a finite map which will
    associate to each running thread a linearization state of the
    following type. *)

  Record threadstate {E F : Sig.t} :=
    mkts {
      ts_op : Sig.op F;
      ts_prog : Sig.term E (Sig.ar ts_op);
      ts_res : option (Sig.ar ts_op);
    }.

  Arguments threadstate : clear implicits.
  Arguments mkts {E F}.

  (** Then the global state consists of a thread state for every
    running thread, an overlay spec and an underlay spec. *)

  Record state {E F} :=
    mkst {
      st_spec : spec F;
      st_impl :> tmap (threadstate E F);
      st_base : spec E;
    }.

  Arguments state : clear implicits.
  Arguments mkst {E F}.

  (** *** Environment steps *)

  (** At any time, the environment may invoke a method on a ready thread,
    or schedule a running thread to execute. A linearization proof
    must be ready to deal with the corresponding effects on the state,
    enumerated below. *)

  Variant estep {E F} (M : Reg.Op.m E F) : relation (state E F) :=
    | einvoke t q Δ s s' Σ :
        TMap.find t s = None ->
        TMap.add t (mkts q (M q) None) s = s' ->
        estep M (mkst Δ s Σ) (mkst Δ s' Σ)
    | eaction t q m n k R Δ s Σ s' Σ' :
        TMap.find t s = Some (mkts q (Sig.cons m k) R) ->
        Spec.next Σ t m = Spec.ret n Σ' ->
        TMap.add t (mkts q (k n) R) s = s' ->
        estep M (mkst Δ s Σ) (mkst Δ s' Σ')
    | ereturn t q r Δ s s' Σ :
        TMap.find t s = Some (mkts q (Sig.var r) (Some r)) ->
        TMap.remove t s = s' ->
        estep M (mkst Δ s Σ) (mkst Δ s' Σ).

  (** *** Commit steps *)

  (** Our job is then to insert commit steps in such a way that by the
    time [ereturn] is in play, the invocation has been committed with
    the correct outcome. *)

  Variant lstep {E F} : relation (state E F) :=
    | lcommit t q r T Δ Δ' s s' Σ :
        TMap.find t s = Some (mkts q T None) ->
        Spec.next Δ t q = Spec.ret r Δ' ->
        TMap.add t (mkts q T (Some r)) s = s' ->
        lstep (mkst Δ s Σ) (mkst Δ' s' Σ).

  (** In addition, if it is possible for a commit to trigger an
    undefined behavior in the overlay specification, then any
    implementation behavior would be correct from this point on,
    so we need to relax any further correctness constraints.
    The following predicate identifies states for which
    that is not the case. *)

  Definition specified {E F} (s : state E F) :=
    forall t q T,
      TMap.find t s = Some (mkts q T None) ->
      Spec.next (st_spec s) t q <> Spec.bot.

  (** ** Correctness *)

  (** Based on the constructions above, our ultimate goal is to show
    that no matter what methods are called and how the threads are
    scheduled, there is a way to perform commits such that the
    following invariant is always preserved. That is, every thread
    will eventually produce the result that was matched against the
    overlay specification. *)

  Definition threadstate_valid {E F} (e : option (threadstate E F)) :=
    forall q r R, e = Some (mkts q (Sig.var r) R) -> R = Some r.

  (** Note that if [spec_top] appears in the underlay specification [Σ],
    there will be no corresponding [eaction] step to take. As a
    result the associated thread will not be scheduled and there are
    no correctness requirements against it at that time. Conversely,
    if [spec_top] appears in the overlay specification [Δ], there will
    be no way to commit a result at that point in time. *)

  (** *** Rechability predicate *)

  (** To formulate this criterion, we will use the following helpful
    definitions and properties. *)

  Notation star := (clos_refl_trans _).

  Definition reachable {A} (R : relation A) (P : A -> Prop) (x : A) :=
    exists y, star R x y /\ P y.

  Lemma reachable_base {A} (R : relation A) (P : A -> Prop) (x : A) :
    P x -> reachable R P x.
  Proof.
    firstorder auto using rt_refl.
  Qed.

  Lemma reachable_step {A} (R : relation A) P x y :
    reachable R P y ->
    R x y ->
    reachable R P x.
  Proof.
    firstorder eauto using rt_trans, rt_step.
  Defined.

  Lemma reachable_steps {A} (R : relation A) (P : A -> Prop) (x y : A) :
    reachable R P y ->
    star R x y ->
    reachable R P x.
  Proof.
    intros (z & Hyz & Hz) Hxy. red.
    eauto using rt_trans.
  Qed.

  Lemma lsteps_ind {E F} (P : spec F -> _ -> spec E -> Prop) (Q : state E F -> Prop) :
    (forall Δ v Σ,
        Q (mkst Δ v Σ) ->
        P Δ v Σ) ->
    (forall t q r T Δ Δ' s Σ,
        TMap.find t s = Some (mkts q T None) ->
        Spec.next Δ t q = Spec.ret r Δ' ->
        P Δ' (TMap.add t (mkts q T (Some r)) s) Σ ->
        P Δ s Σ) ->
    (forall Δ v Σ,
        reachable lstep Q (mkst Δ v Σ) ->
        P Δ v Σ).
  Proof.
    intros Hbase Hstep Δ s Σ.
    cut (forall U, reachable lstep Q U -> P (st_spec U) (st_impl U) (st_base U)).
    { intros H HU. apply H in HU. auto. }
    clear - Hbase Hstep.
    intros U (V & HUV & HV).
    pattern U. revert HUV. apply clos_refl_trans_ind_right.
    - destruct V; auto.
    - intros x y H Hy _. clear U V HV.
      destruct H; cbn in *; subst; eauto 10.
  Qed.

  (** *** Liveness *)

  (** Until now, we have considered [Spec.top] as a "magic" behavior,
    in the sense that threads which invoke primitives with this outcome
    are expected to wait and considered correct. This is sufficient to
    establish safety (the implementation will only produce outcomes
    which match the specification) but leaves open the possibility of
    deadlocks and fails to establish liveness (the implementation will
    eventually produce a result prescribed by the specification).

    In the setting of terminating programs, liveness is fairly
    straighforward: as long as the specification dictates that some
    result should be produced, or when a thread has committed a result
    against the specification but not produced it yet, it must be
    possible to make progress towards that goal. Note that we only
    consider threads with pending calls to underlay primitives,
    since threads which are ready to return have already committed a
    result and as such can no longer affect either specification. *)

  Variant progress_expected_by {E F} (Σ: spec F) t : option (threadstate E F) -> Prop :=
    progress_expected_intro q m k R r Σ' :
      (R = None -> Spec.next Σ t q = Spec.ret r Σ') ->
      progress_expected_by Σ t (Some (mkts q (Sig.cons m k) R)).

  Definition progress_expected {E F} (s : state E F) :=
    exists t, progress_expected_by (st_spec s) t (TMap.find t s).

  (** Progress means that some thread can invoke an underlay primitive
    without waiting. *)

  Variant progress_possible_in {E F} (Δ : spec E) t : option (threadstate E F) -> Prop :=
    progress_possible_intro q m k R n Δ' :
      Spec.next Δ t m = Spec.ret n Δ' ->
      progress_possible_in Δ t (Some (mkts q (Sig.cons m k) R)).

  Definition progress_possible {E F} (s : state E F) :=
    exists t, progress_possible_in (st_base s) t (TMap.find t s).

  (** Note that these are global property, and that the thread making
    progress may be different from the one where a result is expected,
    since it may be necessary for the former to act on the underlay
    (say, by releasing a lock) to allow the latter to proceed (now
    that the lock can be acquired again). The progressing thread may
    also resolve the situation by elimintating the expectation of
    further progress through its action on the overlay specification.
    For example, in a lock implementation, when two calls to [acq] are
    pending and the lock is available, the linearized specification
    dictates that either call would produce an immediate outcome,
    and consequently the situation in each of the threads is
    sufficient to create the expectation of progress. However,
    if the call to [acq] is carried out in either thread, this will
    update the specification and relieve the other thread from the
    expectation of producing a resultm as the lock is now being held
    by another thread. *)

  (** *** Coinductive property *)

  (** The overall correctness property can be given as follows. *)

  CoInductive correct {E F} (M : Reg.Op.m E F) (s : state E F) : Prop :=
    {
      correct_valid :
        specified s ->
        forall i, threadstate_valid (TMap.find i s);
      correct_safe :
        specified s ->
        forall i q m k R,
          TMap.find i s = Some (mkts q (Sig.cons m k) R) ->
          Spec.next (st_base s) i m <> Spec.bot;
      correct_live :
        specified s ->
        progress_expected s ->
        progress_possible s;
      correct_next :
        specified s ->
        forall s', estep M s s' -> reachable lstep (correct M) s';
    }.

  Definition cal {E F} Σ (M : Reg.Op.m E F) Δ :=
    correct M (mkst Δ (TMap.empty _) Σ).

  (** *** Proof method *)

  (** To establish correctness, it suffices to show that there is
    a correctness invariant with the following properties. *)

  Record correctness_invariant {E F} (M : Reg.Op.m E F) (P : state E F -> Prop) : Prop :=
    {
      ci_valid s :
        P s -> specified s ->
        forall i, threadstate_valid (TMap.find i s);
      ci_safe s :
        P s -> specified s ->
        forall i q m k R,
          TMap.find i s = Some (mkts q (Sig.cons m k) R) ->
          Spec.next (st_base s) i m <> Spec.bot;
      ci_live s :
        P s -> specified s ->
        progress_expected s ->
        progress_possible s;
      ci_next s :
        P s -> specified s ->
        forall s', estep M s s' -> reachable lstep P s';
    }.

  Lemma correct_ci {E F} (M : Reg.Op.m E F) :
    correctness_invariant M (correct M).
  Proof.
    constructor.
    - apply correct_valid.
    - apply correct_safe.
    - apply correct_live.
    - intros u Hu Hspec u' Hu'.
      apply correct_next in Hu'; auto.
  Qed.

  Lemma correctness_invariant_sound {E F} (M : Reg.Op.m E F) P :
    correctness_invariant M P ->
    forall s, P s -> correct M s.
  Proof.
    intros HP.
    cofix H.
    intros s Hs. constructor.
    - eapply ci_valid; eauto.
    - eapply ci_safe; eauto.
    - eapply ci_live; eauto.
    - intros Hspec s' Hs'. unfold reachable.
      edestruct @ci_next as (s'' & Hs'' & H''); eauto.
  Qed.

  (** ** Identity *)

  Variant id_linstate {E} : threadstate E E -> Prop :=
    | id_invoked q :
      id_linstate (mkts q (Sig.cons q Sig.var) None)
    | id_returned q r :
      id_linstate (mkts q (Sig.var r) (Some r)).

  Variant id_state {E} : state E E -> Prop :=
    id_state_intro Σ (u : tmap (threadstate E E)) :
      (forall t s, TMap.find t u = Some s -> id_linstate s) ->
      id_state (mkst Σ u Σ).

  Lemma id_state_ci E :
    correctness_invariant (Reg.id E) id_state.
  Proof.
    split.
    - intros _ [Σ u Hu] Hspec t q r R Hs. apply Hu in Hs.
      dependent destruction Hs; cbn in *; congruence.
    - intros _ [Σ u Hu] Hspec t q m k R Ht. cbn in *.
      specialize (Hu _ _ Ht).
      dependent destruction Hu.
      eauto.
    - intros _ [Σ u Hu] Hspec [t Ht]. red. cbn in *.
      pose proof (Hu t) as Hut. exists t. destruct Ht.
      specialize (Hut _ eq_refl). dependent destruction Hut.
      econstructor; eauto.
    - intros _ [Σ u Hu] Hspec u' Hu'.
      dependent destruction Hu'.
      + (* invocation *)
        apply reachable_base.
        constructor. intros i s Hs.
        destruct (classic (i = t)).
        * subst. rewrite TMap.gss in Hs.
          dependent destruction Hs.
          constructor.
        * rewrite TMap.gso in Hs; eauto.
      + (* execute action *)
        apply Hu in H.
        dependent destruction H.
        eexists (mkst Σ' _ Σ'). split.
        * apply rt_step.
          eapply (lcommit t m n); auto.
          rewrite TMap.gss. reflexivity.
        * constructor. intros t' s Hs.
          destruct (classic (t' = t)).
          -- subst. rewrite TMap.gss in Hs.
             dependent destruction Hs.
             constructor.
          -- rewrite !TMap.gso in Hs; eauto.
      + (* execute return *)
        eapply reachable_base.
        constructor. intros t' s Hs.
        destruct (classic (t' = t)).
        * subst. rewrite TMap.grs in Hs.
          dependent destruction Hs.
        * rewrite !TMap.gro in Hs; eauto.
  Qed.

  Theorem id_cal {E} (Σ : spec E) :
    cal Σ (Reg.id E) Σ.
  Proof.
    apply correctness_invariant_sound with id_state.
    - apply id_state_ci.
    - constructor.
      intros t s.
      rewrite TMap.gempty.
      discriminate.
  Qed.

  (** ** Vertical composition *)

  Notation "t >>= f" := (Sig.subst f t) (left associativity, at level 40).
  Notation "x <- t ; f" := (t >>= fun x => f) (right associativity, at level 60).

  Section COMPOSE.
    Context {E F G} (M : Reg.Op.m F G) (N : Reg.Op.m E F).

    (** *** Per-thread invariant *)

    (** When [M] invokes a method [m] of [N] with continuation [k],
      we distinguish between two phases:
         - before [N] commits a result, the action is still pending in [M]
         - afterwards, [M] progresses and is now waiting on the next action
           (or return), which will be carried out after [N] actually returns.
      In order to express this, we introduce the following auxiliary
      computation, which computes the current program of [M] based on
      the commit state [S] of the [N] component. *)

    Definition pending_program (q: Sig.op G) m k S : Sig.term F (Sig.ar q) :=
      match S with
        | None => Sig.cons m k
        | Some n => k n
      end.

    (** The predicate we use to formulate the composition invariant
      will also cover intermediate states where internal execution
      is ongoing. This is the case when a thread has a [Sig.cons]
      program in [M] while [N] is waiting for the next query,
      or when [N] has a [Sig.var] program. We will use the following
      constructions to manage this. *)

    Variant comp_phase :=
      | comp_ready
      | comp_running (i : tid) (q : Sig.op G) (T : Sig.term F (Sig.ar q)).

    Variant run_check_l i q : Sig.term F (Sig.ar q) -> comp_phase -> Prop :=
      | run_check_l_cons m mk :
        run_check_l i q (Sig.cons m mk) (comp_running i q (Sig.cons m mk))
      | run_check_l_var w r :
        run_check_l i q (Sig.var r) w.

    Variant run_check_r i q m mk : Sig.term E (Sig.ar m) -> _ -> Prop :=
      | run_check_r_cons u uk w :
        run_check_r i q m mk (Sig.cons u uk) w
      | run_check_r_var n :
        run_check_r i q m mk (Sig.var n) (comp_running i q (Sig.cons m mk)).

    (** The predicate [comp_threadstate i w s12 s1 s2] relates
      the composite state [s12] for thread [i] with the component
      states [s1] and [s2]. The parameter [w] optionally allows
      a thread to be running, so that unprocessed internal
      interactions could still be present if that thread matches [i]. *)

    Variant comp_threadstate i (w : comp_phase) : _ -> _ -> _ -> Prop :=
      (* The thread is currently waiting for the next query. *)
      | cts_ready :
        comp_threadstate i w
          None
          None
          None
      (* Query [q] is being executed by [M] with the remaning program [T].
         [N] is not running. *)
      | cts_left q T R :
        run_check_l i q T w ->
        comp_threadstate i w
          (Some (mkts q (Reg.transform N T) R))
          (Some (mkts q T R))
          None
      (* Query [q] is begin executed by [M], which has invoked [N]
         with the query [m]. Once the remaining program [U] in [N]
         returns a result [n], the execution of [M] is resumed
         according to [mk n]. *)
      | cts_right q m U Q mk R :
        run_check_r i q m mk U w ->
        comp_threadstate i w
          (Some (mkts q (n <- U; Reg.transform N (mk n)) R))
          (Some (mkts q (pending_program q m mk Q) R))
          (Some (mkts m U Q)).

    Lemma comp_threadstate_valid i e12 e1 e2 :
      comp_threadstate i comp_ready e12 e1 e2 ->
      threadstate_valid e1 ->
      threadstate_valid e2 ->
      threadstate_valid e12.
    Proof.
      intros He12 He1 He2.
      dependent destruction He12.
      - red. congruence.
      - intros xq r xR Hs.
        dependent destruction H.
        dependent destruction Hs; cbn in *.
        eauto.
      - intros xq r xR Hs.
        dependent destruction H; cbn in *.
        dependent destruction Hs.
    Qed.

    Lemma comp_threadstate_o i j q T w s12 s1 s2 :
      comp_threadstate i (comp_running j q T) s12 s1 s2 ->
      i <> j ->
      comp_threadstate i w s12 s1 s2.
    Proof.
      intros H Hij.
      dependent destruction H; constructor;
      dependent destruction H; (congruence || constructor).
    Qed.

    (** *** Global state invariant *)

    Definition comp_tmap w (s12 s1 s2 : tmap (threadstate _ _)) : Prop :=
      forall i,
        comp_threadstate i w (TMap.find i s12) (TMap.find i s1) (TMap.find i s2).

    (** Basic properties. *)

    Lemma comp_tmap_convert t q T w s12 s1 s2 :
      comp_tmap (comp_running t q T) s12 s1 s2 ->
      comp_threadstate t w (TMap.find t s12) (TMap.find t s1) (TMap.find t s2) ->
      comp_tmap w s12 s1 s2.
    Proof.
      intros H Ht i.
      destruct (classic (i = t)); subst; eauto using comp_threadstate_o.
    Qed.

    Lemma comp_tmap_specified_l w Δ s1 Γ s2 Σ s12 :
      comp_tmap w s12 s1 s2 ->
      specified (mkst Δ s12 Σ) ->
      specified (mkst Δ s1 Γ).
    Proof.
      intros Hs12 Hspec t q T Hs1t; cbn in *.
      specialize (Hs12 t).
      dependent destruction Hs12; try congruence.
      - rewrite Hs1t in x1. dependent destruction x1. eauto.
      - rewrite Hs1t in x1. dependent destruction x1. eauto.
    Qed.

    Lemma comp_tmap_specified_r w Δ s1 Γ s2 Σ s12 :
      comp_tmap w s12 s1 s2 ->
      correct M (mkst Δ s1 Γ) ->
      specified (mkst Δ s12 Σ) ->
      specified (mkst Γ s2 Σ).
    Proof.
      intros Hs12 Hs1 Hspec t q T Hs2t; cbn in *.
      pose proof (Hs12 t) as Hs12t.
      rewrite Hs2t in Hs12t.
      dependent destruction Hs12t.
      eapply correct_safe in Hs1; eauto.
      eapply comp_tmap_specified_l; eauto.
    Qed.

    (** The invariant is preserved by environment steps. *)

    Lemma comp_tmap_invoke_l s12 s1 s2 t q :
      TMap.find t s1 = None ->
      comp_tmap comp_ready s12 s1 s2 ->
      comp_tmap (comp_running t q (M q))
        (TMap.add t (mkts q (Reg.Op.compose M N q) None) s12)
        (TMap.add t (mkts q (M q) None) s1)
        s2.
    Proof.
      intros Hs1t Hs12 i.
      destruct (classic (i = t)); subst.
      - rewrite !TMap.gss.
        specialize (Hs12 t).
        rewrite Hs1t in Hs12.
        dependent destruction Hs12.
        rewrite <- x.
        constructor.
        destruct (M q); constructor.
      - rewrite !TMap.gso; auto.
        specialize (Hs12 i).
        inversion Hs12; constructor.
        + dependent destruction H3. constructor.
        + dependent destruction H3. constructor.
    Qed.

    Lemma comp_tmap_action_l w t q m n mk U R s12 s1 s2 :
      TMap.find t s1 = Some (mkts q (Sig.cons m mk) R) ->
      TMap.find t s2 = Some (mkts m U None) ->
      comp_tmap w s12 s1 s2 ->
      comp_tmap w s12 (TMap.add t (mkts q (mk n) R) s1)
                      (TMap.add t (mkts m U (Some n)) s2).
    Proof.
      intros Hs1t Hs2t Hs12 i.
      destruct (classic (i = t)); subst; rewrite ?TMap.gso by auto; auto.
      rewrite !TMap.gss.
      specialize (Hs12 t). rewrite Hs1t, Hs2t in Hs12. clear Hs1t Hs2t.
      dependent destruction Hs12. rewrite <- x0.
      apply (cts_right t w q m U (Some n)). auto.
    Qed.

    Lemma comp_tmap_return_l w t q r s12 s1 s2 :
      TMap.find t s1 = Some (mkts q (Sig.var r) (Some r)) ->
      TMap.find t s2 = None ->
      comp_tmap w s12 s1 s2 ->
      comp_tmap w (TMap.remove t s12) (TMap.remove t s1) s2.
    Proof.
      intros Hs1t Hs2t Hs12 i.
      destruct (classic (i = t)); subst.
      - rewrite !TMap.grs, Hs2t. constructor.
      - rewrite !TMap.gro; auto.
    Qed.

    Lemma comp_tmap_invoke_r s12 s1 s2 t q m mk R w :
      TMap.find t s1 = Some (mkts q (Sig.cons m mk) R) ->
      TMap.find t s2 = None ->
      comp_tmap w s12 s1 s2 ->
      comp_tmap w s12 s1 (TMap.add t (mkts m (N m) None) s2).
    Proof.
      intros Hs1t Hs2t Hs12 i.
      destruct (classic (i = t)); subst.
      - rewrite TMap.gss.
        specialize (Hs12 t).
        rewrite Hs1t, Hs2t in Hs12.
        dependent destruction Hs12.
        dependent destruction H.
        rewrite <- x, Hs1t. cbn.
        apply cts_right with (Q := None).
        destruct (N m); constructor.
      - rewrite TMap.gso; auto.
    Qed.

    Lemma comp_tmap_action_r s12 s1 s2 t q m mk u uk v R S :
      TMap.find t s1 = Some (mkts q (pending_program q m mk S) R) ->
      TMap.find t s2 = Some (mkts m (Sig.cons u uk) S) ->
      comp_tmap comp_ready s12 s1 s2 ->
      comp_tmap (comp_running t q (Sig.cons m mk))
                (TMap.add t (mkts q (n <- uk v; Reg.transform N (mk n)) R) s12)
                s1
                (TMap.add t (mkts m (uk v) S) s2).
    Proof.
      intros Hs1t Hs2t Hs12 i.
      destruct (classic (i = t)); subst.
      - rewrite !TMap.gss.
        rewrite Hs1t.
        econstructor.
        destruct (uk v); constructor.
      - rewrite !TMap.gso; auto.
        specialize (Hs12 i).
        inversion Hs12; constructor;
        dependent destruction H3; constructor.
    Qed.

    Lemma comp_tmap_return_r s12 s1 s2 t q m mk n :
      TMap.find t s2 = Some (mkts m (Sig.var n) (Some n)) ->
      comp_tmap (comp_running t q (Sig.cons m mk)) s12 s1 s2 ->
      comp_tmap (comp_running t q (mk n)) s12 s1 (TMap.remove t s2).
    Proof.
      intros Hs2t Hs12 i.
      destruct (classic (i = t)); subst.
      - rewrite TMap.grs.
        specialize (Hs12 t).
        rewrite Hs2t in Hs12.
        dependent destruction Hs12.
        rewrite <- x0, <- x. constructor.
        dependent destruction H. cbn.
        destruct (mk n); constructor.
      - rewrite TMap.gro; auto.
        eapply comp_threadstate_o; eauto.
    Qed.

    (** The commit steps triggered by the components likewise
      perserve the invariant, once equivalent commit steps have been
      applied to the composite layer as needed. *)

    Lemma comp_tmap_commit_l Δ s1 Γ s2 Σ s12 p :
      reachable lstep (correct M) (mkst Δ s1 Γ) ->
      comp_tmap p s12 s1 s2 ->
      exists Δ' s12' s1',
        star lstep (mkst Δ s12 Σ) (mkst Δ' s12' Σ) /\
        correct M (mkst Δ' s1' Γ) /\
        comp_tmap p s12' s1' s2.
    Proof.
      intros H.
      revert s12. pattern Δ, s1, Γ.
      revert Δ s1 Γ H. apply lsteps_ind.
      - intros Δ s1 Γ Hs1 s12 Hs12.
        eauto 10 using rt_refl.
      - intros i q r T Δ Δ' s1 Γ Hs1t HΔ IH s12 Hs12.
        pose proof (Hs12 i) as Hs12i.
        rewrite Hs1t in Hs12i.
        dependent destruction Hs12i.
        + edestruct IH
            with (TMap.add i (mkts q (Reg.transform N T) (Some r)) s12)
            as (Δ'' & s12'' & s1'' & Hstep & HM'' & Hs12'').
          {
            intros j. destruct (classic (j = i)); subst.
            * rewrite !TMap.gss, <- x. constructor. auto.
            * rewrite !TMap.gso; auto.
          }
          exists Δ'', s12'', s1''. split; auto.
          eapply rt_trans; eauto.
          apply rt_step.
          econstructor; eauto.
        + edestruct IH
            with (TMap.add i (mkts q (n <- U; Reg.transform N (mk n)) (Some r)) s12)
            as (Δ'' & s12'' & s1'' & Hstep & HM'' & Hs12'').
          {
            intros j. destruct (classic (j = i)); subst.
            * rewrite !TMap.gss, <- x. constructor. auto.
            * rewrite !TMap.gso; auto.
          }
          exists Δ'', s12'', s1''. split; auto.
          eapply rt_trans; eauto.
          apply rt_step.
          econstructor; eauto.
    Qed.

    Lemma comp_tmap_commit_r w Δ s1 Γ s2 Σ s12 :
      reachable lstep (correct N) (mkst Γ s2 Σ) ->
      correct M (mkst Δ s1 Γ) ->
      comp_tmap w s12 s1 s2 ->
      specified (mkst Δ s12 Σ) ->
      exists Δ' Γ' s12' s1' s2',
        star lstep (mkst Δ s12 Σ) (mkst Δ' s12' Σ) /\
        (specified (mkst Δ' s12' Σ) ->
         correct M (mkst Δ' s1' Γ') /\
         correct N (mkst Γ' s2' Σ) /\
         comp_tmap w s12' s1' s2' /\
         forall i, TMap.find i s2 <> None -> TMap.find i s2' <> None).
    Proof.
      intros Hs2. revert Δ s1 s12.
      pattern Γ, s2, Σ. revert Γ s2 Σ Hs2.
      apply lsteps_ind; eauto 20 using rt_refl.
      (*
       * When [N] commits the result [ri] in thread [i],
       * we perform the corresponding [eaction] step in [M].
       * Note that since [N] is still active, this will not
       * break the established invariant.
       *)
      intros i m n U Γ Γ' s2 Σ Hs2i HΓ IH Δ s1 s12 Hs1 Hs12 Hspec.
      pose proof (Hs12 i) as Hs12i. rewrite Hs2i in Hs12i.
      dependent destruction Hs12i.
      symmetry in x0. rename x0 into Hs12i.
      symmetry in x. rename x into Hs1i. cbn in Hs1i.
      assert (Hs1s: specified (mkst Δ s1 Γ)) by eauto using comp_tmap_specified_l.
      eapply comp_tmap_action_l with (n:=n) in Hs12; eauto.
      eapply correct_next in Hs1; eauto using (eaction M i q m n).
      clear Hs1i Hs1s.
      pose proof (TMap.gss i (mkts q (mk n) R) s1) as Hs1i.
      revert Hs12 Hs1 Hs1i.
      generalize (TMap.add i (mkts q (mk n) R) s1) as s1'. clear s1.
      intros s1. intros.
      (*
       * The execution of [M] will in turn trigger commits.
       *)
      eapply comp_tmap_commit_l in Hs12
        as (Δ' & s12' & s1' & Hsteps & Hs1' & Hs12');
        eauto.
      destruct (classic (specified (mkst Δ' s12' Σ))) as [Hspec' | Hspec'].
      2: {
        eexists Δ', Γ', s12', s1', s2. split; eauto. tauto.
      }
      edestruct IH
        as (Δ'' & Γ'' & s12'' & s1'' & s2' & Hsteps' & H'');
        eauto.
      destruct (classic (specified (mkst Δ'' s12'' Σ))) as [Hspec'' | Hspec''].
      2: {
        eexists Δ'', Γ'', s12'', s1'', s2'. split; eauto using rt_trans. tauto.
      }
      edestruct H'' as (Hs1'' & Hs2' & Hs12'' & ?); auto.
      assert (forall j, TMap.find j s2 <> None -> TMap.find j s2' <> None).
      { intros. apply H0.
        destruct (classic (j = i)); subst;
        rewrite ?TMap.gss, ?TMap.gso; congruence. }
      eauto 15 using rt_trans.
    Qed.

    (** *** Overall invariant *)

    (** The overall composition invariant is as follows.
      Essentially, there should be an intemediate specification
      and component states such that each thread satisfies
      [comp_threadstate], and such that the component are correct with
      respect to the relevant specifications. *)

    Variant comp_state_def w : state E G -> Prop :=
      | comp_state_intro Σ Γ Δ s12 s1 s2 :
        comp_tmap w s12 s1 s2 ->
        correct M (mkst Δ s1 Γ) ->
        correct N (mkst Γ s2 Σ) ->
        comp_state_def w (mkst Δ s12 Σ).

    Definition comp_state w s :=
      specified s -> comp_state_def w s.

    Lemma comp_specified_sufficient w s :
      (specified s -> reachable lstep (comp_state w) s) ->
      reachable lstep (comp_state w) s.
    Proof.
      intros H.
      destruct (classic (specified s)); auto.
      apply reachable_base. red. tauto.
    Qed.

    Lemma comp_run_r t q m mk s12 Δ s1 Γ s2 Σ :
      comp_tmap (comp_running t q (Sig.cons m mk)) s12 s1 s2 ->
      correct M (mkst Δ s1 Γ) ->
      correct N (mkst Γ s2 Σ) ->
      TMap.find t s2 <> None ->
      (forall n s,
          comp_state (comp_running t q (mk n)) s ->
          reachable lstep (comp_state comp_ready) s) ->
      reachable lstep (comp_state comp_ready) (mkst Δ s12 Σ).
    Proof.
      intros Hs12 Hs1 Hs2 Hs2t IHmk.
      pose proof (Hs12 t) as Hs12t.
      dependent destruction Hs12t; try congruence. clear Hs2t.
      symmetry in x0. rename x0 into Hs12t.
      symmetry in x1. rename x1 into Hs1t.
      symmetry in x. rename x into Hs2t.
      dependent destruction H.
      - (*
         * If the next instruction in [N] is an external call, we are done.
         *)
        apply reachable_base. econstructor; eauto. intro i.
        destruct (classic (i = t)); eauto using comp_threadstate_o. subst.
        rewrite Hs12t, Hs1t, Hs2t. constructor. constructor.
      - (*
         * If [N] is returning a value, we proceed accordingly.
         * The hypothesis on [mk] will eventually help us deal
         * with the remainder of [M]'s program.
         *)
        apply comp_specified_sufficient. intro Hspec.
        assert (specified (mkst Γ s2 Σ)) by eauto using comp_tmap_specified_r.
        assert (Q = Some n) by (eapply correct_valid; eauto). subst. cbn in *.
        (*
         * The first step is to trigger the [ereturn] step in [N].
         *)
        eapply comp_tmap_return_r in Hs12; eauto.
        eapply correct_next in Hs2; eauto using ereturn, comp_tmap_specified_r.
        (*
         * Now that we have returned to a state where [N] is inactive,
         * the induction hypothesis will be able to take care of the
         * remainder of the execution. However, the commit steps of
         * [N] triggered by the [ereturn] step must first be processed.
         *)
        edestruct comp_tmap_commit_r
          as (Δ' & Γ' & s12' & s1' & s2' & Hsteps & H'); eauto.
        eapply reachable_steps; eauto.
        apply comp_specified_sufficient. intro Hspec'.
        destruct H' as (Hs1' & Hs2' & Hs12' & _); eauto.
        eapply IHmk. econstructor; eauto.
    Qed.

    Lemma comp_run t q T s :
      comp_state (comp_running t q T) s ->
      reachable lstep (comp_state comp_ready) s.
    Proof.
      intros Hs.
      apply comp_specified_sufficient.
      revert s Hs.
      induction T as [m mk IHmk | r];
      intros s Hs Hspec;
      destruct Hs as [Σ Γ Δ s12 s1 s2 Hs12 Hs1 Hs2]; auto.
      (*
       * When [T] is [Sig.var] no internal interaction is possible,
       * so our job is already done.
       *)
      2: {
        apply reachable_base. econstructor; eauto.
        eapply comp_tmap_convert; eauto.
        specialize (Hs12 t). clear -Hs12.
        dependent destruction Hs12.
        - rewrite <- x0, <- x1, <- x. constructor.
        - rewrite <- x0, <- x1, <- x. constructor.
          dependent destruction H. constructor.
        - rewrite <- x0, <- x1, <- x. constructor.
          dependent destruction H. constructor.
      }
      (*
       * When [T] is [Sig.cons], we show that any internal interactions
       * that can be triggered preserve the composition invariant, and
       * that we eventually hit either a [comp_ready] state, or make
       * progress in executing [T] and use the induction hypothesis.
       *)
      pose proof (Hs12 t) as Hs12t.
      dependent destruction Hs12t.
      - (*
         * Inactive threads are already good.
         *)
        apply reachable_base. econstructor; eauto.
        eapply comp_tmap_convert; eauto.
        rewrite <- x0, <- x1, <- x. constructor.
      - (*
         * When only [M] is active, we need to execute the
         * corresponding program until it returns.
         *)
        symmetry in x0. rename x0 into Hs12t.
        symmetry in x1. rename x1 into Hs1t.
        symmetry in x. rename x into Hs2t.
        dependent destruction H.
        2: {
          apply reachable_base.
          econstructor; eauto.
          eapply comp_tmap_convert; eauto.
          rewrite Hs12t, Hs1t, Hs2t.
          constructor. constructor.
        }
        (*
         * To handle the next instruction, we invoke
         * its implementation in [N].
         *)
        eapply correct_next in Hs2;
          eauto using (einvoke N t m), comp_tmap_specified_r.
        eapply comp_tmap_invoke_r in Hs12; eauto.
        pose proof (TMap.gss t (mkts m (N m) None) s2) as Hs2t'.
        revert Hs12 Hs1 Hs2 Hs1t Hs2t'.
        generalize (TMap.add t (mkts m (N m) None) s2) as s2'. clear -IHmk.
        intros s2 Hs12 Hs1 Hs2 Hs1t Hs2t.
        apply comp_specified_sufficient. intro Hspec.
        edestruct comp_tmap_commit_r
          as (Δ' & Γ' & s12' & s1' & s2' & Hsteps & H');
          eauto.
        eapply reachable_steps; eauto.
        apply comp_specified_sufficient. intro Hspec'.
        destruct H' as (Hs1' & Hs2' & Hs12' & ?); auto.
        eapply comp_run_r; eauto using comp_specified_sufficient.
        apply H; congruence.
      - symmetry in x0. rename x0 into Hs12t.
        symmetry in x1. rename x1 into Hs1t.
        symmetry in x. rename x into Hs2t.
        dependent destruction H.
        + eapply reachable_base.
          econstructor; eauto.
          eapply comp_tmap_convert; eauto.
          rewrite Hs12t, Hs1t, Hs2t.
          constructor. constructor.
        + eapply comp_run_r; eauto using comp_specified_sufficient.
          congruence.
    Qed.

    Lemma comp_ci :
      correctness_invariant (Reg.Op.compose M N) (comp_state comp_ready).
    Proof.
      split.
      - intros s Hs Hspec i. destruct Hs; auto.
        eapply comp_threadstate_valid; eauto.
        + apply (correct_valid _ _ H0); eauto using comp_tmap_specified_l.
        + apply (correct_valid _ _ H1); eauto using comp_tmap_specified_r.
      - intros s Hs Hspec i q m k R Hsi.
        destruct Hs as [? ? ? s12 s1 s2 Hs12 Hs1 Hs2]; auto.
        cbn in *. pose proof (Hs12 i) as Hs12i. rewrite Hsi in Hs12i.
        dependent destruction Hs12i.
        + dependent destruction H. cbn in *. congruence.
        + dependent destruction H. cbn in *. dependent destruction x0.
          eapply (correct_safe N (mkst Γ s2 Σ)); cbn; eauto using comp_tmap_specified_r.
      - admit.
      - intros s Hs Hspec s12' H.
        destruct Hs as [? ? ? s12 s1 s2 Hs12 Hs1 Hs2]; auto.
        dependent destruction H.
        + (*
           * We mirror any invocation in [M].
           *) 
          assert (Hs1t: TMap.find t s1 = None).
          {
            specialize (Hs12 t). rewrite H in Hs12.
            dependent destruction Hs12; auto.
          }
          eapply correct_next in Hs1;
            eauto using (einvoke M t q), comp_tmap_specified_l.
          eapply comp_tmap_invoke_l in Hs12; eauto.
          eapply comp_tmap_commit_l in Hs1; eauto.
          destruct Hs1 as (Δ' & s12' & s1' & Hsteps & Hs1' & Hs12').
          eapply reachable_steps; eauto.
          eapply comp_run.
          econstructor; eauto.
        + (*
           * External actions are mirrored in [N].
           *)
          pose proof (Hs12 t) as Hs12t.
          rewrite H in Hs12t.
          dependent destruction Hs12t;
          dependent destruction H1; cbn in *; try congruence.
          dependent destruction x0. rename m into u, n into v, m0 into m.
          symmetry in x1. rename x1 into Hs1t.
          symmetry in x. rename x into Hs2t.
          eapply correct_next in Hs2;
            eauto using (eaction N t m u v), comp_tmap_specified_r.
          eapply comp_tmap_action_r in Hs12; eauto.
          apply comp_specified_sufficient. intro Hspec'.
          eapply comp_tmap_commit_r in Hs2; eauto.
          destruct Hs2
            as (Δ' & Γ' & s12' & s1' & s2' & Hsteps & H');
            eauto.
          eapply reachable_steps; eauto.
          apply comp_specified_sufficient. intro Hspec''.
          destruct H' as (Hs1' & Hs2' & Hs21' & _); auto.
          eapply comp_run.
          econstructor; eauto.
        + (*
           * Returns happen back in [M].
           *)
          pose proof (Hs12 t) as Hs12t.
          rewrite H in Hs12t.
          dependent destruction Hs12t;
            dependent destruction H0; cbn in *;
            dependent destruction x0.
          eapply correct_next in Hs1;
            eauto using (ereturn M t q r), comp_tmap_specified_l.
          eapply comp_tmap_return_l in Hs12; eauto.
          eapply comp_tmap_commit_l in Hs1; eauto.
          destruct Hs1 as (Δ' & s12' & s1' & Hsteps & Hs1' & Hs12').
          eapply reachable_steps; eauto.
          eapply reachable_base.
          econstructor; eauto.
    Admitted.

    Theorem comp_cal Σ Γ Δ :
      cal Γ M Δ ->
      cal Σ N Γ ->
      cal Σ (Reg.Op.compose M N) Δ.
    Proof.
      unfold cal. intros.
      eapply correctness_invariant_sound; eauto using comp_ci.
      econstructor; eauto.
      intro i. rewrite !TMap.gempty. constructor.
    Qed.
  End COMPOSE.

  (** ** Certified abstraction layers form a category *)

  Record layer_interface :=
    {
      li_sig : Sig.t;
      li_spec : spec li_sig;
    }.

  Record layer_implementation {L L' : layer_interface} :=
    {
      li_impl : Reg.Op.m (li_sig L) (li_sig L');
      li_correct : cal (li_spec L) li_impl (li_spec L');
    }.

  Arguments layer_implementation : clear implicits.

  Definition t : Type := layer_interface.
  Definition m : t -> t -> Type := layer_implementation.

  Program Definition id L : m L L :=
    {| li_impl := Reg.id (li_sig L) |}.
  Next Obligation.
    apply id_cal.
  Qed.

  Program Definition compose {L1 L2 L3} (M : m L2 L3) (N : m L1 L2) : m L1 L3 :=
    {| li_impl := Reg.Op.compose (li_impl M) (li_impl N) |}.
  Next Obligation.
    eapply comp_cal; eauto using li_correct.
  Qed.

  Lemma meq {L1 L2} (M N : m L1 L2) :
    li_impl M = li_impl N -> M = N.
  Proof.
    destruct M, N; cbn.
    intro. subst. f_equal.
    apply proof_irrelevance.
  Qed.

  Lemma compose_id_left {L1 L2} (M : m L1 L2) :
    compose (id L2) M = M.
  Proof.
    apply meq, Reg.Op.compose_id_left.
  Qed.

  Lemma compose_id_right {L1 L2} (M : m L1 L2) :
    compose M (id L1) = M.
  Proof.
    apply meq, Reg.Op.compose_id_right.
  Qed.

  Lemma compose_assoc {L1 L2 L3 L4} (M12: m L1 L2) (M23: m L2 L3) (M34: m L3 L4):
    compose (compose M34 M23) M12 = compose M34 (compose M23 M12).
  Proof.
    apply meq, Reg.Op.compose_assoc.
  Qed.

  Include CategoryTheory.
End LinCCALBase.

(** ** Horizontal composition *)

Module Type LinCCALTensSpec.
  Include LinCCALBase.
End LinCCALTensSpec.

Module LinCCALTens (B : LinCCALTensSpec) <: Monoidal B.
  Import (notations, canonicals) Reg.Plus.
  Import B.
  Obligation Tactic := intros.

  Module Tens <: SymmetricMonoidalStructure B.

    (** *** Tensor product of layer interfaces *)

    (** Two certified abstraction layers can be composed horizontally
      by taking method implementations as defined in [Reg.Plus]. Then
      the specification of the composite layer can be computed by
      independently interleaving the specifications from each side
      per [Spec.tens], as shown below. *)

    Definition omap (L1 L2 : t) : t :=
      {|
        li_sig := Reg.Plus.omap (li_sig L1) (li_sig L2);
        li_spec := li_spec L1 * li_spec L2;
      |}.

    Local Infix "*" := omap : obj_scope.

    (** *** Tensor product of layer implementations *)

    (** For some reason, [congruence] and other tactics are buggy when
      faced with those cases. *)

    Lemma inj_somets2 {E F} q T1 T2 R1 R2 :
      Some (@mkts E F q T1 R1) = Some (@mkts E F q T2 R2) ->
      T1 = T2 /\ R1 = R2.
    Proof.
      inversion 1.
      apply inj_pair2 in H1.
      apply inj_pair2 in H2.
      auto.
    Qed.

    (** Owing to proof irrelevance, the monoidal structure associated
      with the tensor product of layers can be pulled from [Reg.Plus].
      However, we first need to prove locality and show that
      horizontal composition preserves layer correctness.
      Fortunately, because the two layer act largely independently
      from each other, this is much simpler to establish than the
      vertical composition property used to define [compose] *)

    Section CORRECTNESS.
      Context {E1 E2 F1 F2 : Sig.t}.
      Context (M1 : Reg.Op.m E1 F1).
      Context (M2 : Reg.Op.m E2 F2).

      (** Per-thread invariant *)

      Variant fmap_threadstate : _ -> _ -> _ -> Prop :=
        | fmap_ts_none :
          fmap_threadstate
            None
            None
            None
        | fmap_ts_left (q : Sig.op F1) (T : Sig.term E1 (Sig.ar q)) R :
          fmap_threadstate
            (Some (mkts (inl q) (Reg.transform Reg.Plus.i1 T) R))
            (Some (mkts q T R))
            None
        | fmap_ts_right (q : Sig.op F2) (T : Sig.term E2 (Sig.ar q)) R :
          fmap_threadstate
            (Some (mkts (inr q) (Reg.transform Reg.Plus.i2 T) R))
            None
            (Some (mkts q T R)).

      (** Thread map invariant *)

      Definition fmap_tmap (s12 s1 s2 : tmap _) :=
        forall i,
          fmap_threadstate (TMap.find i s12) (TMap.find i s1) (TMap.find i s2).

      Lemma fmap_tmap_specified_l Σ1 Σ2 s12 s1 s2 Δ1 Δ2 :
        fmap_tmap s12 s1 s2 ->
        specified (mkst (Σ1 * Σ2) s12 (Δ1 * Δ2)) ->
        specified (mkst Σ1 s1 Δ1).
      Proof.
        intros H Hs12 i q T Hs1i. cbn in *.
        pose proof (H i) as Hs12i.
        rewrite Hs1i in Hs12i.
        dependent destruction Hs12i.
        symmetry in x0. rename x0 into Hs12i.
        apply Hs12 in Hs12i. cbn in *.
        destruct Spec.next; congruence.
      Qed.

      Lemma fmap_tmap_specified_r Σ1 Σ2 s12 s1 s2 Δ1 Δ2 :
        fmap_tmap s12 s1 s2 ->
        specified (mkst (Σ1 * Σ2) s12 (Δ1 * Δ2)) ->
        specified (mkst Σ2 s2 Δ2).
      Proof.
        intros H Hs12 i q T Hs1i. cbn in *.
        pose proof (H i) as Hs12i.
        rewrite Hs1i in Hs12i.
        dependent destruction Hs12i.
        symmetry in x0. rename x0 into Hs12i.
        apply Hs12 in Hs12i. cbn in *.
        destruct Spec.next; congruence.
      Qed.

      (** Global state invariant *)

      Variant fmap_state : state _ _ -> Prop :=
        fmap_state_intro s12 s1 s2 Δ1 Δ2 Σ1 Σ2 :
          fmap_tmap s12 s1 s2 ->
          correct M1 (mkst Δ1 s1 Σ1) ->
          correct M2 (mkst Δ2 s2 Σ2) ->
          fmap_state (mkst (Δ1 * Δ2) s12 (Σ1 * Σ2)).

      Lemma fmap_lsteps_l s12 s1 s2 Δ1 Δ2 Σ1 Σ2 :
        fmap_tmap s12 s1 s2 ->
        reachable lstep (correct M1) (mkst Δ1 s1 Σ1) ->
        correct M2 (mkst Δ2 s2 Σ2) ->
        reachable lstep fmap_state (mkst (Δ1 * Δ2) s12 (Σ1 * Σ2)).
      Proof.
        intros Hs12 Hs1 Hs2.
        revert Δ2 s2 Σ2 s12 Hs2 Hs12.
        pattern Δ1, s1, Σ1. revert Δ1 s1 Σ1 Hs1.
        apply lsteps_ind.
        - intros Δ1 s1 Σ1 H1; intros.
          apply reachable_base.
          econstructor; eauto.
        - intros t q r T Δ1 Δ1' s1 Σ1 Hs1t HΔ1' IH; intros.
          pose proof (Hs12 t) as Hs12t.
          rewrite Hs1t in Hs12t.
          dependent destruction Hs12t.
          symmetry in x0. rename x0 into Hs12t.
          symmetry in x. rename x into Hs2t.
          eapply reachable_step.
          2: {
            apply (lcommit t (inl q) r (Reg.transform Reg.Plus.i1 T)); auto.
            cbn. rewrite HΔ1'. fold (Δ1' * Δ2)%spec.
            reflexivity.
          }
          eapply IH; eauto.
          intros i. destruct (classic (i = t)); subst.
          + rewrite !TMap.gss, Hs2t. constructor.
          + rewrite !TMap.gso; auto.
      Qed.

      Lemma fmap_lsteps_r s12 s1 s2 Δ1 Δ2 Σ1 Σ2 :
        fmap_tmap s12 s1 s2 ->
        correct M1 (mkst Δ1 s1 Σ1) ->
        reachable lstep (correct M2) (mkst Δ2 s2 Σ2) ->
        reachable lstep fmap_state (mkst (Δ1 * Δ2) s12 (Σ1 * Σ2)).
      Proof.
        intros Hs12 Hs1 Hs2.
        revert Δ1 s1 Σ1 s12 Hs1 Hs12.
        pattern Δ2, s2, Σ2. revert Δ2 s2 Σ2 Hs2.
        apply lsteps_ind.
        - intros Δ2 s2 Σ2 H2; intros.
          apply reachable_base.
          econstructor; eauto.
        - intros t q r T Δ2 Δ2' s2 Σ2 Hs2t HΔ2' IH; intros.
          pose proof (Hs12 t) as Hs12t.
          rewrite Hs2t in Hs12t.
          dependent destruction Hs12t.
          symmetry in x0. rename x0 into Hs12t.
          symmetry in x. rename x into Hs1t.
          eapply reachable_step.
          2: {
            apply (lcommit t (inr q) r (Reg.transform Reg.Plus.i2 T)); auto.
            cbn. rewrite HΔ2'. fold (Δ1 * Δ2')%spec.
            reflexivity.
          }
          eapply IH; eauto.
          intros i. destruct (classic (i = t)); subst.
          + rewrite !TMap.gss, Hs1t. constructor.
          + rewrite !TMap.gso; auto.
      Qed.

      Lemma fmap_ci :
        correctness_invariant (Reg.Plus.fmap M1 M2) fmap_state.
      Proof.
        split.
        - (* validity of commit states *)
          intros _ [s12 s1 s2 Σ1 Σ2 Δ1 Δ2 Hs Hs1 Hs2] Hspec i q r R. cbn.
          intros Hs12i.
          pose proof (Hs i) as Hsi.
          inversion Hsi; subst; try congruence.
          + rewrite Hs12i in H0; clear Hs12i.
            assert (q = inl q0) by congruence; subst.
            apply inj_somets2 in H0 as [HT ?]; subst.
            destruct T; cbn in HT; try congruence. dependent destruction HT.
            eapply correct_valid in Hs1; eauto using fmap_tmap_specified_l.
          + rewrite Hs12i in H0; clear Hs12i.
            assert (q = inr q0) by congruence; subst.
            apply inj_somets2 in H0 as [HT ?]; subst.
            destruct T; cbn in HT; try congruence. dependent destruction HT.
            eapply correct_valid in Hs2; eauto using fmap_tmap_specified_r.
        - (* safety of outgoing calls *)
          intros _ [s12 s1 s2 Σ1 Σ2 Δ1 Δ2 Hs Hs1 Hs2] Hspec i q m k R. cbn.
          intro Hs12i.
          pose proof (Hs i) as Hsi.
          inversion Hsi; subst; try congruence.
          + rewrite Hs12i in H0. clear Hs12i.
            assert (q = inl q0) by congruence. subst.
            apply inj_somets2 in H0 as [HT ?]; subst.
            destruct T; cbn in HT; try congruence. dependent destruction HT.
            eapply correct_safe in Hs1; eauto using fmap_tmap_specified_l.
            cbn in *. destruct Spec.next; congruence.
          + rewrite Hs12i in H0. clear Hs12i.
            assert (q = inr q0) by congruence. subst.
            apply inj_somets2 in H0 as [HT ?]; subst.
            destruct T; cbn in HT; try congruence. dependent destruction HT.
            eapply correct_safe in Hs2; eauto using fmap_tmap_specified_r.
            cbn in *. destruct Spec.next; congruence.
        - (* liveness *)
          admit.
        - (* preservation by execution steps *)
          intros _ [s12 s1 s2 Σ1 Σ2 Δ1 Δ2 Hs Hs1 Hs2] Hspec s' Hs'.
          dependent destruction Hs'; rename t0 into t.
          + (* invocation *)
            pose proof (Hs t) as Hs12t. rewrite H in Hs12t.
            dependent destruction Hs12t.
            symmetry in x0; rename x0 into Hs1t.
            symmetry in x; rename x into Hs2t.
            destruct q as [q1|q2].
            * eapply correct_next in Hs1;
                eauto using (einvoke M1 t q1), fmap_tmap_specified_l.
              eapply fmap_lsteps_l; eauto.
              intros i. destruct (classic (i = t)); subst.
              -- rewrite !TMap.gss, Hs2t. constructor.
              -- rewrite !TMap.gso; auto.
            * eapply correct_next in Hs2;
                eauto using (einvoke M2 t q2), fmap_tmap_specified_r.
              eapply fmap_lsteps_r; eauto.
              intros i. destruct (classic (i = t)); subst.
              -- rewrite !TMap.gss, Hs1t. constructor.
              -- rewrite !TMap.gso; auto.
          + (* execution step *)
            pose proof (Hs t) as Hs12t.
            dependent destruction Hs12t; try congruence.
            * symmetry in x0; rename x0 into Hs12t.
              symmetry in x1; rename x1 into Hs1t.
              symmetry in x; rename x into Hs2t.
              rewrite Hs12t in H. clear Hs12t.
              assert (q = inl q0) by congruence. subst.
              apply inj_somets2 in H as [HT ?]; subst.
              destruct T; dependent destruction HT.
              cbn in H0. destruct Spec.next eqn:HΔ1'; dependent destruction H0.
              eapply correct_next in Hs1;
                eauto using (eaction M1 t), fmap_tmap_specified_l.
              eapply fmap_lsteps_l; eauto.
              intros i. destruct (classic (i = t)); subst.
              -- rewrite !TMap.gss, Hs2t. constructor.
              -- rewrite !TMap.gso; auto.
            * symmetry in x0; rename x0 into Hs12t.
              symmetry in x1; rename x1 into Hs1t.
              symmetry in x; rename x into Hs2t.
              rewrite Hs12t in H. clear Hs12t.
              assert (q = inr q0) by congruence. subst.
              apply inj_somets2 in H as [HT ?]; subst.
              destruct T; dependent destruction HT.
              cbn in H0. destruct Spec.next eqn:HΔ2'; dependent destruction H0.
              eapply correct_next in Hs2;
                eauto using (eaction M2 t), fmap_tmap_specified_r.
              eapply fmap_lsteps_r; eauto.
              intros i. destruct (classic (i = t)); subst.
              -- rewrite !TMap.gss, Hs1t. constructor.
              -- rewrite !TMap.gso; auto.
          + (* return *)
            pose proof (Hs t) as Hs12t.
            dependent destruction Hs12t; try congruence.
            * symmetry in x0; rename x0 into Hs12t.
              symmetry in x1; rename x1 into Hs1t.
              symmetry in x; rename x into Hs2t.
              rewrite Hs12t in H. clear Hs12t.
              assert (q = inl q0) by congruence. subst.
              apply inj_somets2 in H as [HT ?]; subst.
              destruct T; dependent destruction HT.
              eapply correct_next in Hs1;
                eauto using (ereturn M1 t _ r), fmap_tmap_specified_l.
              eapply fmap_lsteps_l; eauto.
              intros i. destruct (classic (i = t)); subst.
              -- rewrite !TMap.grs, Hs2t. constructor.
              -- rewrite !TMap.gro; auto.
            * symmetry in x0; rename x0 into Hs12t.
              symmetry in x1; rename x1 into Hs1t.
              symmetry in x; rename x into Hs2t.
              rewrite Hs12t in H. clear Hs12t.
              assert (q = inr q0) by congruence. subst.
              apply inj_somets2 in H as [HT ?]; subst.
              destruct T; dependent destruction HT.
              eapply correct_next in Hs2;
                eauto using (ereturn M2 t _ r), fmap_tmap_specified_r.
              eapply fmap_lsteps_r; eauto.
              intros i. destruct (classic (i = t)); subst.
              -- rewrite !TMap.grs, Hs1t. constructor.
              -- rewrite !TMap.gro; auto.
      Admitted.
    End CORRECTNESS.

    Program Definition fmap {L1 L2 L1' L2'} (M1: L1~~>L1') (M2: L2~~>L2') :
      L1 * L2 ~~> L1' * L2' :=
        {| li_impl := Reg.Plus.fmap (li_impl M1) (li_impl M2) |}.
    Next Obligation.
      eapply correctness_invariant_sound.
      - apply fmap_ci.
      - econstructor.
        + intro i. rewrite !TMap.gempty. constructor.
        + apply li_correct.
        + apply li_correct.
    Qed.

    Local Infix "*" := fmap : hom_scope.

    (** *** Functoriality *)

    Theorem fmap_id E1 E2 :
      fmap (id E1) (id E2) = id (omap E1 E2).
    Proof.
      apply meq, Reg.Plus.fmap_id.
    Qed.

    Theorem fmap_compose {E1 E2 F1 F2 G1 G2} :
      forall (g1: F1 ~~> G1) (g2: F2 ~~> G2) (f1: E1 ~~> F1) (f2: E2 ~~> F2),
        fmap (g1 @ f1) (g2 @ f2) = fmap g1 g2 @ fmap f1 f2.
    Proof.
      intros. apply meq, Reg.Plus.fmap_compose.
    Qed.

    (** *** Empty layer interface *)

    (** The empty spec is used to define the zero layer interface. *)

    Definition unit :=
      {|
        li_sig := Sig.Plus.unit;
        li_spec := Spec.gen (fun _ _ => Empty_set_rect _) tt;
      |}.

    (** *** Structural isomorphisms *)

    (** As with [fmap], we must show that the various structural
      isomorphisms constitute correct layer implementations.
      This is tedious but mostly straightforward. In order to
      streamline the process somewhat we define a generic correctness
      invariant induced by a [Sig.m]orphism, which generalizes the
      correctness invariant we used for [LinCCAL.id]. *)

    Section ISO_CORRECTNESS.
      Context {E F} (ϕ : Sig.Op.m E F).
      Import (notations) Sig.

      Variant iso_threadstate : threadstate E F -> Prop :=
        | iso_invoked q :
          iso_threadstate (mkts q (Sig.operator (ϕ q) >= n =>
                                   Sig.var (Sig.operand (ϕ q) n)) None)
        | iso_returned q n :
          iso_threadstate (mkts q (Sig.var (Sig.operand (ϕ q) n))
                                     (Some (Sig.operand (ϕ q) n))).

      Definition iso_tmap (s : tmap (threadstate E F)) :=
        forall t st, TMap.find t s = Some st -> iso_threadstate st.

    End ISO_CORRECTNESS.

    (** Unfortunately the overall invariant still must be defined on a
      case-by-case basis, because the way the spec components of the
      parameters are involved varies from one to the next. *)

    Local Infix "+" := Sig.Plus.omap.

    Variant assoc_fw_state {E F G}: state _ _ -> Prop :=
      | assoc_fw_state_intro Σ Φ Γ s :
        iso_tmap (Sig.bw (Sig.Plus.assoc E F G)) s ->
        assoc_fw_state (mkst ((Σ * Φ) * Γ) s (Σ * (Φ * Γ))).

    Variant assoc_bw_state {E F G}: state _ _ -> Prop :=
      | assoc_bw_state_intro Σ Φ Γ s :
        iso_tmap (Sig.fw (Sig.Plus.assoc E F G)) s ->
        assoc_bw_state (mkst (Σ * (Φ * Γ)) s ((Σ * Φ) * Γ)).

    Program Definition assoc L1 L2 L3 : iso (L1 * (L2 * L3)) ((L1 * L2) * L3) :=
      {|
        fw := {| li_impl := Reg.bw (Reg.Plus.assoc _ _ _) |};
        bw := {| li_impl := Reg.fw (Reg.Plus.assoc _ _ _) |};
      |}.
    Next Obligation.
      set (ϕ := Sig.bw (Sig.Plus.assoc (li_sig L1) (li_sig L2) (li_sig L3))).
      apply correctness_invariant_sound with assoc_fw_state.
      - constructor.
        + destruct 1. intros Hspec t q r R Ht.
          apply H in Ht. dependent destruction Ht. auto.
        + destruct 1. intros Hspec t q m k R Ht.
          specialize (H t _ Ht). dependent destruction H.
          cbn in *. apply Hspec in Ht. cbn in *.
          destruct q as [[|]|]; cbn in *;
          destruct Spec.next; congruence.
        + destruct 1. intros Hspec [t Ht].
          specialize (H t). exists t. cbn in *. destruct Ht.
          specialize (H _ eq_refl). dependent destruction H.
          specialize (H0 eq_refl).
          destruct q as [[|]|]; cbn in *;
          destruct Spec.next eqn:Hnext; cbn in *; dependent destruction H0.
          * eapply (progress_possible_intro _ _ (inl (inl o))); cbn; rewrite Hnext; auto.
          * eapply (progress_possible_intro _ _ (inl (inr o))); cbn; rewrite Hnext; auto.
          * eapply (progress_possible_intro _ _ (inr o)); cbn; rewrite Hnext; auto.
        + destruct 1. intros Hspec s' Hs'.
          dependent destruction Hs'.
          * apply reachable_base. constructor.
            intros i x Hi. destruct (classic (i = t0)); subst.
            -- rewrite !TMap.gss in Hi. dependent destruction Hi.
               destruct q as [[|]|]; apply (iso_invoked ϕ).
            -- rewrite !TMap.gso in *; eauto.
          * apply H in H0. dependent destruction H0. cbn in *.
            destruct q as [[|]|]; cbn in *;
            destruct Spec.next eqn:Hnext; dependent destruction H1.
            -- eapply reachable_step with (mkst ((x * Φ) * Γ) _ (x * (Φ * Γ))).
               2: { apply (lcommit t0 (inl (inl o)) n (Sig.var n)); eauto.
                    ++ rewrite TMap.gss. reflexivity. 
                    ++ cbn. rewrite Hnext. reflexivity. }
               apply reachable_base. constructor.
               intros i si Hi. destruct (classic (i = t0)); subst.
               ++ rewrite !TMap.gss in Hi. dependent destruction Hi.
                  apply (iso_returned ϕ (inl (inl o)) n).
               ++ rewrite !TMap.gso in Hi; eauto.
            -- eapply reachable_step with (mkst ((Σ * x) * Γ) _ (Σ * (x * Γ))).
               2: { apply (lcommit t0 (inl (inr o)) n (Sig.var n)); eauto.
                    ++ rewrite TMap.gss. reflexivity. 
                    ++ cbn. rewrite Hnext. reflexivity. }
               apply reachable_base. constructor.
               intros i si Hi. destruct (classic (i = t0)); subst.
               ++ rewrite !TMap.gss in Hi. dependent destruction Hi.
                  apply (iso_returned ϕ (inl (inr o)) n).
               ++ rewrite !TMap.gso in Hi; eauto.
            -- eapply reachable_step with (mkst ((Σ * Φ) * x) _ (Σ * (Φ * x))).
               2: { apply (lcommit t0 (inr o) n (Sig.var n)); eauto.
                    ++ rewrite TMap.gss. reflexivity. 
                    ++ cbn. rewrite Hnext. reflexivity. }
               apply reachable_base. constructor.
               intros i si Hi. destruct (classic (i = t0)); subst.
               ++ rewrite !TMap.gss in Hi. dependent destruction Hi.
                  apply (iso_returned ϕ (inr o) n).
               ++ rewrite !TMap.gso in Hi; eauto.
          * apply reachable_base. constructor.
            intros i si Hi. destruct (classic (i = t0)); subst.
            -- rewrite TMap.grs in Hi. congruence.
            -- rewrite TMap.gro in Hi; eauto.
      - constructor. intros i si Hi.
        rewrite TMap.gempty in Hi. congruence.
    Qed.
    Next Obligation.
      set (ϕ := Sig.fw (Sig.Plus.assoc (li_sig L1) (li_sig L2) (li_sig L3))).
      apply correctness_invariant_sound with assoc_bw_state.
      - constructor.
        + destruct 1. intros Hspec t q r R Ht.
          apply H in Ht. dependent destruction Ht. auto.
        + destruct 1. intros Hspec t q m k R Ht.
          specialize (H t _ Ht). dependent destruction H.
          cbn in *. apply Hspec in Ht. cbn in *.
          destruct q as [|[|]]; cbn in *;
          destruct Spec.next; congruence.
        + destruct 1. intros Hspec [t Ht].
          specialize (H t). exists t. cbn in *. destruct Ht.
          specialize (H _ eq_refl). dependent destruction H.
          specialize (H0 eq_refl).
          destruct q as [|[|]]; cbn in *;
          destruct Spec.next eqn:Hnext; cbn in *; dependent destruction H0.
          * eapply (progress_possible_intro _ _ (inl o)); cbn; rewrite Hnext; auto.
          * eapply (progress_possible_intro _ _ (inr (inl o))); cbn; rewrite Hnext; auto.
          * eapply (progress_possible_intro _ _ (inr (inr o))); cbn; rewrite Hnext; auto.
        + destruct 1. intros Hspec s' Hs'.
          dependent destruction Hs'.
          * apply reachable_base. constructor.
            intros i x Hi. destruct (classic (i = t0)); subst.
            -- rewrite !TMap.gss in Hi. dependent destruction Hi.
               destruct q as [|[|]]; apply (iso_invoked ϕ).
            -- rewrite !TMap.gso in *; eauto.
          * apply H in H0. dependent destruction H0. cbn in *.
            destruct q as [|[|]]; cbn in *;
            destruct Spec.next eqn:Hnext; dependent destruction H1.
            -- eapply reachable_step with (mkst (x * (Φ * Γ)) _ ((x * Φ) * Γ)).
               2: { apply (lcommit t0 (inl o) n (Sig.var n)); eauto.
                    ++ rewrite TMap.gss. reflexivity. 
                    ++ cbn. rewrite Hnext. reflexivity. }
               apply reachable_base. constructor.
               intros i si Hi. destruct (classic (i = t0)); subst.
               ++ rewrite !TMap.gss in Hi. dependent destruction Hi.
                  apply (iso_returned ϕ (inl o) n).
               ++ rewrite !TMap.gso in Hi; eauto.
            -- eapply reachable_step with (mkst (Σ * (x * Γ)) _ ((Σ * x) * Γ)).
               2: { apply (lcommit t0 (inr (inl o)) n (Sig.var n)); eauto.
                    ++ rewrite TMap.gss. reflexivity. 
                    ++ cbn. rewrite Hnext. reflexivity. }
               apply reachable_base. constructor.
               intros i si Hi. destruct (classic (i = t0)); subst.
               ++ rewrite !TMap.gss in Hi. dependent destruction Hi.
                  apply (iso_returned ϕ (inr (inl o)) n).
               ++ rewrite !TMap.gso in Hi; eauto.
            -- eapply reachable_step with (mkst (Σ * (Φ * x)) _ ((Σ * Φ) * x)).
               2: { apply (lcommit t0 (inr (inr o)) n (Sig.var n)); eauto.
                    ++ rewrite TMap.gss. reflexivity. 
                    ++ cbn. rewrite Hnext. reflexivity. }
               apply reachable_base. constructor.
               intros i si Hi. destruct (classic (i = t0)); subst.
               ++ rewrite !TMap.gss in Hi. dependent destruction Hi.
                  apply (iso_returned ϕ (inr (inr o)) n).
               ++ rewrite !TMap.gso in Hi; eauto.
          * apply reachable_base. constructor.
            intros i si Hi. destruct (classic (i = t0)); subst.
            -- rewrite TMap.grs in Hi. congruence.
            -- rewrite TMap.gro in Hi; eauto.
      - constructor. intros i si Hi.
        rewrite TMap.gempty in Hi. congruence.
    Qed.
    Next Obligation.
      apply meq, Reg.bw_fw.
    Qed.
    Next Obligation.
      apply meq, Reg.fw_bw.
    Qed.

    Variant lunit_fw_state {E}: state _ _ -> Prop :=
      | lunit_fw_state_intro Σ s :
        iso_tmap (Sig.bw (Sig.Plus.lunit E)) s ->
        lunit_fw_state (mkst Σ s (li_spec unit * Σ)).

    Variant lunit_bw_state {E}: state _ _ -> Prop :=
      | lunit_bw_state_intro Σ s :
        iso_tmap (Sig.fw (Sig.Plus.lunit E)) s ->
        lunit_bw_state (mkst (li_spec unit * Σ) s Σ).

    Program Definition lunit L : iso (unit * L) L :=
      {|
        fw := {| li_impl := Reg.bw (Reg.Plus.lunit _) |};
        bw := {| li_impl := Reg.fw (Reg.Plus.lunit _) |};
      |}.
    Next Obligation.
      set (ϕ := Sig.bw (Sig.Plus.lunit (li_sig L))).
      apply correctness_invariant_sound with lunit_fw_state.
      - constructor.
        + destruct 1. intros Hspec t q r R Ht.
          apply H in Ht. dependent destruction Ht. auto.
        + destruct 1. intros Hspec t q m k R Ht.
          specialize (H t _ Ht). dependent destruction H.
          cbn in *. apply Hspec in Ht. cbn in *.
          destruct Spec.next; congruence.
        + destruct 1. intros Hspec [t Ht].
          specialize (H t). exists t. cbn in *. destruct Ht.
          specialize (H _ eq_refl). dependent destruction H.
          specialize (H0 eq_refl).
          econstructor. cbn.
          rewrite H0. reflexivity.
        + destruct 1. intros Hspec s' Hs'.
          dependent destruction Hs'.
          * apply reachable_base. constructor.
            intros i x Hi. destruct (classic (i = t0)); subst.
            -- rewrite !TMap.gss in Hi. dependent destruction Hi.
               apply (iso_invoked ϕ).
            -- rewrite !TMap.gso in *; eauto.
          * apply H in H0. dependent destruction H0. cbn in *.
            destruct Spec.next eqn:Hnext; dependent destruction H1.
            eapply reachable_step with (mkst x _ (_ * x)).
            2: { apply (lcommit t0 q n (Sig.var n)); eauto.
                 rewrite TMap.gss. reflexivity. }
            apply reachable_base. constructor.
            intros i si Hi. destruct (classic (i = t0)); subst.
            -- rewrite !TMap.gss in Hi. dependent destruction Hi.
               apply (iso_returned ϕ q n).
            -- rewrite !TMap.gso in Hi; eauto.
          * apply reachable_base. constructor.
            intros i si Hi. destruct (classic (i = t0)); subst.
            -- rewrite TMap.grs in Hi. congruence.
            -- rewrite TMap.gro in Hi; eauto.
      - constructor. intros i si Hi.
        rewrite TMap.gempty in Hi. congruence.
    Qed.
    Next Obligation.
      set (ϕ := Sig.fw (Sig.Plus.lunit (li_sig L))).
      apply correctness_invariant_sound with lunit_bw_state.
      - constructor.
        + destruct 1. intros Hspec t q r R Ht.
          apply H in Ht. dependent destruction Ht. auto.
        + destruct 1. intros Hspec t [[]|q] m k R Ht.
          specialize (H t _ Ht). dependent destruction H.
          cbn in *. apply Hspec in Ht. cbn in *.
          destruct Spec.next; congruence.
        + destruct 1. intros Hspec [t Ht].
          specialize (H t). exists t. cbn in *. destruct Ht.
          specialize (H _ eq_refl). dependent destruction H.
          specialize (H0 eq_refl).
          destruct q as [[]|]; cbn in *.
          destruct Spec.next eqn:Hnext; cbn in *; dependent destruction H0.
          eapply (progress_possible_intro _ _ (inr o)); eauto.
        + destruct 1. intros Hspec s' Hs'.
          dependent destruction Hs'.
          * destruct q as [[]|q].
            apply reachable_base. constructor.
            intros i x Hi. destruct (classic (i = t0)); subst.
            -- rewrite !TMap.gss in Hi. dependent destruction Hi.
               apply (iso_invoked ϕ).
            -- rewrite !TMap.gso in *; eauto.
          * destruct q as [[]|q].
            apply H in H0. dependent destruction H0. cbn in *.
            eapply reachable_step with (mkst (_ * Σ') _ Σ').
            2: { apply (lcommit t0 (inr q) n (Sig.var n)); eauto.
                 -- rewrite TMap.gss. reflexivity.
                 -- cbn. rewrite H1. reflexivity. }
            apply reachable_base. constructor.
            intros i si Hi. destruct (classic (i = t0)); subst.
            -- rewrite !TMap.gss in Hi. dependent destruction Hi.
               apply (iso_returned ϕ (inr q) n).
            -- rewrite !TMap.gso in Hi; eauto.
          * apply reachable_base. constructor.
            intros i si Hi. destruct (classic (i = t0)); subst.
            -- rewrite TMap.grs in Hi. congruence.
            -- rewrite TMap.gro in Hi; eauto.
      - constructor. intros i si Hi.
        rewrite TMap.gempty in Hi. congruence.
    Qed.
    Next Obligation.
      apply meq, Reg.bw_fw.
    Qed.
    Next Obligation.
      apply meq, Reg.fw_bw.
    Qed.

    Variant runit_fw_state {E}: state _ _ -> Prop :=
      | runit_fw_state_intro Σ s :
        iso_tmap (Sig.bw (Sig.Plus.runit E)) s ->
        runit_fw_state (mkst Σ s (Σ * li_spec unit)).

    Variant runit_bw_state {E}: state _ _ -> Prop :=
      | runit_bw_state_intro Σ s :
        iso_tmap (Sig.fw (Sig.Plus.runit E)) s ->
        runit_bw_state (mkst (Σ * li_spec unit) s Σ).

    Program Definition runit L : iso (L * unit) L :=
      {|
        fw := {| li_impl := Reg.bw (Reg.Plus.runit _) |};
        bw := {| li_impl := Reg.fw (Reg.Plus.runit _) |};
      |}.
    Next Obligation.
      set (ϕ := Sig.bw (Sig.Plus.runit (li_sig L))).
      apply correctness_invariant_sound with runit_fw_state.
      - constructor.
        + destruct 1. intros Hspec t q r R Ht.
          apply H in Ht. dependent destruction Ht. auto.
        + destruct 1. intros Hspec t q m k R Ht.
          specialize (H t _ Ht). dependent destruction H.
          cbn in *. apply Hspec in Ht. cbn in *.
          destruct Spec.next; congruence.
        + destruct 1. intros Hspec [t Ht].
          specialize (H t). exists t. cbn in *. destruct Ht.
          specialize (H _ eq_refl). dependent destruction H.
          specialize (H0 eq_refl).
          econstructor. cbn.
          rewrite H0. reflexivity.
        + destruct 1. intros Hspec s' Hs'.
          dependent destruction Hs'.
          * apply reachable_base. constructor.
            intros i x Hi. destruct (classic (i = t0)); subst.
            -- rewrite !TMap.gss in Hi. dependent destruction Hi.
               apply (iso_invoked ϕ).
            -- rewrite !TMap.gso in *; eauto.
          * apply H in H0. dependent destruction H0. cbn in *.
            destruct Spec.next eqn:Hnext; dependent destruction H1.
            eapply reachable_step with (mkst x _ (x * _)).
            2: { apply (lcommit t0 q n (Sig.var n)); eauto.
                 rewrite TMap.gss. reflexivity. }
            apply reachable_base. constructor.
            intros i si Hi. destruct (classic (i = t0)); subst.
            -- rewrite !TMap.gss in Hi. dependent destruction Hi.
               apply (iso_returned ϕ q n).
            -- rewrite !TMap.gso in Hi; eauto.
          * apply reachable_base. constructor.
            intros i si Hi. destruct (classic (i = t0)); subst.
            -- rewrite TMap.grs in Hi. congruence.
            -- rewrite TMap.gro in Hi; eauto.
      - constructor. intros i si Hi.
        rewrite TMap.gempty in Hi. congruence.
    Qed.
    Next Obligation.
      set (ϕ := Sig.fw (Sig.Plus.runit (li_sig L))).
      apply correctness_invariant_sound with runit_bw_state.
      - constructor.
        + destruct 1. intros Hspec t q r R Ht.
          apply H in Ht. dependent destruction Ht. auto.
        + destruct 1. intros Hspec t [q|[]] m k R Ht.
          specialize (H t _ Ht). dependent destruction H.
          cbn in *. apply Hspec in Ht. cbn in *.
          destruct Spec.next; congruence.
        + destruct 1. intros Hspec [t Ht].
          specialize (H t). exists t. cbn in *. destruct Ht.
          specialize (H _ eq_refl). dependent destruction H.
          specialize (H0 eq_refl).
          destruct q as [|[]]; cbn in *.
          destruct Spec.next eqn:Hnext; cbn in *; dependent destruction H0.
          eapply (progress_possible_intro _ _ (inl o)); eauto.
        + destruct 1. intros Hspec s' Hs'.
          dependent destruction Hs'.
          * destruct q as [q|[]].
            apply reachable_base. constructor.
            intros i x Hi. destruct (classic (i = t0)); subst.
            -- rewrite !TMap.gss in Hi. dependent destruction Hi.
               apply (iso_invoked ϕ).
            -- rewrite !TMap.gso in *; eauto.
          * destruct q as [q|[]].
            apply H in H0. dependent destruction H0. cbn in *.
            eapply reachable_step with (mkst (Σ' * _) _ Σ').
            2: { apply (lcommit t0 (inl q) n (Sig.var n)); eauto.
                 -- rewrite TMap.gss. reflexivity.
                 -- cbn. rewrite H1. reflexivity. }
            apply reachable_base. constructor.
            intros i si Hi. destruct (classic (i = t0)); subst.
            -- rewrite !TMap.gss in Hi. dependent destruction Hi.
               apply (iso_returned ϕ (inl q) n).
            -- rewrite !TMap.gso in Hi; eauto.
          * apply reachable_base. constructor.
            intros i si Hi. destruct (classic (i = t0)); subst.
            -- rewrite TMap.grs in Hi. congruence.
            -- rewrite TMap.gro in Hi; eauto.
      - constructor. intros i si Hi.
        rewrite TMap.gempty in Hi. congruence.
    Qed.
    Next Obligation.
      apply meq, Reg.bw_fw.
    Qed.
    Next Obligation.
      apply meq, Reg.fw_bw.
    Qed.

    Variant swap_state {E F}: state _ _ -> Prop :=
      | swap_state_intro Σ Φ s :
        iso_tmap (Sig.bw (Sig.Plus.swap_iso E F)) s ->
        swap_state (mkst (Φ * Σ) s (Σ * Φ)).

    Program Definition swap L1 L2 : L1 * L2 ~~> L2 * L1 :=
      {| li_impl := Reg.Plus.swap _ _ |}.
    Next Obligation.
      set (ϕ := Sig.bw (Sig.Plus.swap_iso (li_sig L1) (li_sig L2))).
      apply correctness_invariant_sound with swap_state.
      - constructor.
        + destruct 1. intros Hspec t q r R Ht.
          apply H in Ht. dependent destruction Ht. auto.
        + destruct 1. intros Hspec t q m k R Ht.
          specialize (H t _ Ht). dependent destruction H.
          cbn in *. apply Hspec in Ht. cbn in *.
          destruct q as [|]; cbn in *;
          destruct Spec.next; congruence.
        + destruct 1. intros Hspec [t Ht].
          specialize (H t). exists t. cbn in *. destruct Ht.
          specialize (H _ eq_refl). dependent destruction H.
          specialize (H0 eq_refl).
          destruct q as [|]; cbn in *;
          destruct Spec.next eqn:Hnext; cbn in *; dependent destruction H0.
          * eapply (progress_possible_intro _ _ (inl o)); cbn; rewrite Hnext; auto.
          * eapply (progress_possible_intro _ _ (inr o)); cbn; rewrite Hnext; auto.
        + destruct 1. intros Hspec s' Hs'.
          dependent destruction Hs'.
          * apply reachable_base. constructor.
            intros i x Hi. destruct (classic (i = t0)); subst.
            -- rewrite !TMap.gss in Hi. dependent destruction Hi.
               destruct q as [|]; apply (iso_invoked ϕ).
            -- rewrite !TMap.gso in *; eauto.
          * apply H in H0. dependent destruction H0. cbn in *.
            destruct q as [|]; cbn in *;
            destruct Spec.next eqn:Hnext; dependent destruction H1.
            -- eapply reachable_step with (mkst (x * Σ) _ (Σ * x)).
               2: { apply (lcommit t0 (inl o) n (Sig.var n)); eauto.
                    ++ rewrite TMap.gss. reflexivity. 
                    ++ cbn. rewrite Hnext. reflexivity. }
               apply reachable_base. constructor.
               intros i si Hi. destruct (classic (i = t0)); subst.
               ++ rewrite !TMap.gss in Hi. dependent destruction Hi.
                  apply (iso_returned ϕ (inl o) n).
               ++ rewrite !TMap.gso in Hi; eauto.
            -- eapply reachable_step with (mkst (Φ * x) _ (x * Φ)).
               2: { apply (lcommit t0 (inr o) n (Sig.var n)); eauto.
                    ++ rewrite TMap.gss. reflexivity. 
                    ++ cbn. rewrite Hnext. reflexivity. }
               apply reachable_base. constructor.
               intros i si Hi. destruct (classic (i = t0)); subst.
               ++ rewrite !TMap.gss in Hi. dependent destruction Hi.
                  apply (iso_returned ϕ (inr o) n).
               ++ rewrite !TMap.gso in Hi; eauto.
          * apply reachable_base. constructor.
            intros i si Hi. destruct (classic (i = t0)); subst.
            -- rewrite TMap.grs in Hi. congruence.
            -- rewrite TMap.gro in Hi; eauto.
      - constructor. intros i si Hi.
        rewrite TMap.gempty in Hi. congruence.
    Qed.

    (** *** Naturality properties *)

    Theorem assoc_nat {A1 B1 C1 A2 B2 C2} f g h :
      fmap (fmap f g) h @ assoc A1 B1 C1 = assoc A2 B2 C2 @ fmap f (fmap g h).
    Proof.
      apply meq, Reg.Plus.assoc_nat_bw.
    Qed.

    Theorem lunit_nat {A1 A2} f :
      f @ lunit A1 = lunit A2 @ fmap (id unit) f.
    Proof.
      apply meq, Reg.Plus.lunit_nat_bw.
    Qed.

    Theorem runit_nat {A1 A2} f :
      f @ runit A1 = runit A2 @ fmap f (id unit).
    Proof.
      apply meq, Reg.Plus.runit_nat_bw.
    Qed.

    Proposition swap_nat {A1 A2 B1 B2} f g :
      fmap g f @ swap A1 B1 = swap A2 B2 @ fmap f g.
    Proof.
      apply meq. symmetry. apply Reg.Plus.swap_nat.
    Qed.

    (** *** Coherence diagrams *)

    Theorem assoc_coh A B C D :
      fmap (assoc A B C) (id D) @
        assoc A (omap B C) D @
        fmap (id A) (assoc B C D) =
      assoc (omap A B) C D @
        assoc A B (omap C D).
    Proof.
      apply meq. cbn -[Reg.Plus.assoc]. unfold Reg.Op.compose.
      rewrite !Reg.compose_assoc. apply Reg.Plus.assoc_coh_bw.
    Qed.

    Theorem unit_coh A B :
      fmap (runit A) (id B) @ assoc A unit B = fmap (id A) (lunit B).
    Proof.
      apply meq, Reg.Plus.unit_coh_bw.
    Qed.

    Proposition swap_assoc A B C :
      fmap (swap A C) (id B) @ assoc A C B @ fmap (id A) (swap B C) =
      assoc C A B @ swap (omap A B) C @ assoc A B C.
    Proof.
      apply meq. cbn -[Reg.Plus.assoc Reg.Plus.swap]. unfold Reg.Op.compose.
      rewrite !Reg.compose_assoc. apply Reg.Plus.swap_assoc_bw.
    Qed.

    Proposition runit_swap A :
      runit A @ swap unit A = lunit A.
    Proof.
      apply meq. cbn -[Reg.Plus.lunit Reg.Plus.swap]. unfold Reg.Op.compose.
      apply Reg.Plus.runit_swap_bw.
    Qed.

    Proposition swap_swap A B :
      swap B A @ swap A B = id (omap A B).
    Proof.
      apply meq, Reg.Plus.swap_swap.
    Qed.

    Include BifunctorTheory B B B.
    Include SymmetricMonoidalStructureTheory B.
  End Tens.

  Include SymmetricMonoidalTheory B.
End LinCCALTens.

(** ** Putting everything together *)

Module LinCCAL <: MonoidalCategory :=
  LinCCALBase <+
  LinCCALTens.


(** * Example *)

(** As an example we will show a concurrent counter can be implemented
  in terms of a lock and register. *)

Module LinCCALExample.
  Import (coercions, canonicals, notations) Sig.
  Open Scope term_scope.
  Unset Program Cases.

  (** ** Counter specification *)

  Variant Ecounter_op :=
    | fai.

  Canonical Structure Ecounter :=
    {|
      Sig.op := Ecounter_op;
      Sig.ar _ := nat;
    |}.

  Definition Σcounter : LinCCAL.Spec.lts Ecounter nat := 
    fun c t 'fai => LinCCAL.Spec.ret (m:=fai) c (S c).

  Definition Lcounter : LinCCAL.t :=
    {| LinCCAL.li_spec := LinCCAL.Spec.gen Σcounter 0%nat; |}.

  (** ** Lock specification *)

  Variant Elock_op :=
    | acq
    | rel.

  Canonical Structure Elock :=
    {|
      Sig.op := Elock_op;
      Sig.ar _ := unit;
    |}.

  Definition Σlock : LinCCAL.Spec.lts Elock (option LinCCAL.tid) :=
    fun s t m =>
      match s, m with
      | None, acq => LinCCAL.Spec.ret (m:=acq) tt (Some t)
      | None, rel => LinCCAL.Spec.bot
      | Some i, acq =>
          if LinCCAL.TMap.E.eq_dec i t then LinCCAL.Spec.bot
                                       else LinCCAL.Spec.top
      | Some i, rel =>
          if LinCCAL.TMap.E.eq_dec i t then LinCCAL.Spec.ret (m:=rel) tt None
                                       else LinCCAL.Spec.bot
      end.

  Definition Llock : LinCCAL.t :=
    {| LinCCAL.li_spec := LinCCAL.Spec.gen Σlock None |}.

  (** ** Register specification *)

  Variant Ereg_op {S} :=
    | get
    | set (s : S).

  Arguments Ereg_op : clear implicits.

  Definition Ereg_ar {S} (m : Ereg_op S) :=
    match m with
      | get => S
      | set _ => unit
    end.

  Canonical Structure Ereg S :=
    {|
      Sig.op := Ereg_op S;
      Sig.ar := Ereg_ar;
    |}.

  Definition Σreg S : LinCCAL.Spec.lts (Ereg S) S :=
    fun s t m =>
      match m with
        | get => LinCCAL.Spec.ret (m:=get) s s
        | set s' => LinCCAL.Spec.ret (m:=set _) tt s'
      end.

  Definition Lreg {S} (s0 : S) :=
    {| LinCCAL.li_spec := LinCCAL.Spec.gen (Σreg S) s0 |}.

  (** ** Implementation *)

  Import (notations) LinCCAL.
  Import (canonicals) Sig.Plus.

  Definition fai_impl : Sig.term (LinCCAL.li_sig (Llock * Lreg 0%nat)%obj) nat :=
    inl acq >= _ =>
    inr get >= c =>
    inr (set (S c)) >= _ =>
    inl rel >= _ =>
    Sig.var c.

  Variant fai_threadstate (i : LinCCAL.tid) h : _ -> _ -> Prop :=
    | fai_rdy c :
      h <> Some i ->
      fai_threadstate i h c None
    | fai_acq c :
      h <> Some i ->
      fai_threadstate i h c (Some (LinCCAL.mkts fai fai_impl None))
    | fai_get c :
      h = Some i ->
      fai_threadstate i h c
        (Some (LinCCAL.mkts fai (inr get >= c =>
                                 inr (set (S c)) >= _ =>
                                 inl rel >= _ =>
                                 Sig.var c) None))
    | fai_set c :
      h = Some i ->
      fai_threadstate i h c
        (Some (LinCCAL.mkts fai (inr (set (S c)) >= _ =>
                                 inl rel >= _ =>
                                 Sig.var c) None))
    | fai_rel c :
      h = Some i ->
      fai_threadstate i h (S c)
        (Some (LinCCAL.mkts fai (inl rel >= _ =>
                                 Sig.var c) (Some c)))
    | fai_ret c c' :
      h <> Some i ->
      fai_threadstate i h c'
        (Some (LinCCAL.mkts fai (Sig.var c) (Some c))).

  Variant fai_state : _ -> Prop :=
    fai_state_intro h c s :
      (forall i, fai_threadstate i h c (LinCCAL.TMap.find i s)) ->
      fai_state (LinCCAL.mkst (LinCCAL.Spec.gen Σcounter c)
                              s
                              (LinCCAL.Spec.gen Σlock h *
                               LinCCAL.Spec.gen (Σreg _) c)).

  Lemma fai_threadstate_convert i h h' c c' s :
    fai_threadstate i h c s ->
    h <> Some i ->
    h' <> Some i ->
    fai_threadstate i h' c' s.
  Proof.
    destruct 1; intros; try congruence; try constructor; auto.
  Qed.

  Program Definition Mcounter : LinCCAL.m (Llock * Lreg 0%nat) Lcounter :=
    {| LinCCAL.li_impl 'fai := fai_impl |}.
  Next Obligation.
    eapply LinCCAL.correctness_invariant_sound with (P := fai_state).
    - split.
      + intros _ [h c s Hs] _ i q r R Hsi. cbn in *.
        specialize (Hs i).
        dependent destruction Hs; unfold fai_impl in *; try congruence.
        rewrite Hsi in x. dependent destruction x. reflexivity.
      + intros _ [h c s Hs] _ i q m k R Hsi. cbn in Hsi |- *.
        specialize (Hs i). cbn in Hs. rewrite Hsi in Hs.
        dependent destruction Hs; cbn; try congruence.
        * (* acquire *)
          destruct h; cbn; try congruence.
          destruct LinCCAL.TMap.E.eq_dec; congruence.
        * (* release *)
          destruct LinCCAL.TMap.E.eq_dec; congruence.
      + (* liveness *)
        intros _ [h c s Hs] _ [t Ht]. cbn in *.
        destruct h as [i | ].
        * (* a thread holding the lock is expected to progress. *)
          exists i; cbn. specialize (Hs i). clear Ht.
          dependent destruction Hs; try congruence; destruct x;
            eapply (LinCCAL.progress_possible_intro _ _ fai); cbn; try reflexivity.
          destruct LinCCAL.TMap.E.eq_dec; try congruence.
          reflexivity.
        * (* otherwise, any running thread would do *)
          exists t; cbn. specialize (Hs t). destruct Ht.
          dependent destruction Hs.
          econstructor. cbn. reflexivity.
      + intros _ [h c s Hs] _ s' Hs'.
        dependent destruction Hs'.
        * (* incoming call *)
          destruct q.
          pose proof (Hs t) as Hst. rewrite H in Hst. dependent destruction Hst.
          apply LinCCAL.reachable_base. constructor.
          intro i. destruct (classic (i = t)); subst.
          -- rewrite LinCCAL.TMap.gss. constructor; auto.
          -- rewrite LinCCAL.TMap.gso; auto.
        * (* execution step *)
          destruct q.
          pose proof (Hs t) as Hst. dependent destruction Hst; try congruence.
          -- (* acq *)
             rewrite H in x. dependent destruction x.
             cbn in H0.
             destruct h; try discriminate. cbn in H0.
             destruct LinCCAL.TMap.E.eq_dec; try discriminate. cbn in H0.
             dependent destruction H0.
             apply LinCCAL.reachable_base. constructor.
             intros i. destruct (classic (i = t)); subst.
             ++ rewrite LinCCAL.TMap.gss. constructor. auto.
             ++ rewrite LinCCAL.TMap.gso; auto.
                eapply fai_threadstate_convert; eauto; congruence.
          -- (* get *)
             rewrite H in x. dependent destruction x.
             apply LinCCAL.reachable_base. constructor.
             intros i. destruct (classic (i = t)); subst.
             ++ rewrite LinCCAL.TMap.gss. constructor. auto.
             ++ rewrite LinCCAL.TMap.gso; auto.
          -- (* set *)
             rewrite H in x. dependent destruction x.
             eapply LinCCAL.reachable_step.
             2: {
               eapply (LinCCAL.lcommit t fai c); eauto.
               ** rewrite LinCCAL.TMap.gss. reflexivity.
               ** cbn. reflexivity.
             }
             apply LinCCAL.reachable_base. constructor.
             intros i. destruct (classic (i = t)); subst.
             ++ rewrite LinCCAL.TMap.gss. constructor. auto.
             ++ rewrite !LinCCAL.TMap.gso; auto.
                eapply fai_threadstate_convert; eauto; congruence.
          -- (* rel *)
             rewrite H in x. dependent destruction x.
             cbn in H0.
             destruct LinCCAL.TMap.E.eq_dec; cbn in H0; try congruence.
             dependent destruction H0.
             apply LinCCAL.reachable_base. constructor.
             intros i. destruct (classic (i = t)); subst.
             ++ rewrite LinCCAL.TMap.gss. constructor. congruence.
             ++ rewrite !LinCCAL.TMap.gso; auto.
                eapply fai_threadstate_convert; eauto; congruence.
        * (* return *)
          destruct q.
          pose proof (Hs t) as Hst. rewrite H in Hst. dependent destruction Hst.
          apply LinCCAL.reachable_base. constructor.
          intro i. destruct (classic (i = t)); subst.
          -- rewrite LinCCAL.TMap.grs. constructor; auto.
          -- rewrite LinCCAL.TMap.gro; auto.
    - (* initial state *)
      constructor.
      intro i.
      rewrite LinCCAL.TMap.gempty.
      constructor.
      congruence.
  Qed.

  (** ** Liveness issue *)

  (** Unfortunately, our formulation of correctness only ensures safety.
    Although our programs all terminate, the underlay specification
    can still introduce the possibility of deadlocks. In this case,
    threads will wait on [LinCCAL.Spec.top] and will be considered
    correct. While we would usually hope that other schedules will
    allow the underlay to progress, so that the pending underlay calls
    would eventually have non-[top] results, this is not currently
    enforced by our correctness property.

    To illustrate this, we show that any overlay can be implemented in
    terms of the following "deadlock" underlay. *)

  Variant Edeadlock_op :=
    | deadlock.

  Canonical Structure Edeadlock :=
    {|
      Sig.op := Edeadlock_op;
      Sig.ar _ := Empty_set;
    |}.

  Definition Σdeadlock : LinCCAL.Spec.t Edeadlock := 
    {| LinCCAL.Spec.next _ _ := LinCCAL.Spec.top |}.

  Definition Ldeadlock : LinCCAL.t :=
    {| LinCCAL.li_spec := Σdeadlock |}.

  Definition dead_impl {X} : Sig.term Edeadlock X :=
    deadlock >= e => match e with end.

  Variant dead_thread {E} : option (LinCCAL.threadstate Edeadlock E) -> Prop :=
    | dead_ready :
      dead_thread None
    | dead_locked q :
      dead_thread (Some (LinCCAL.mkts (F:=E) q dead_impl None)).

  Variant dead_state {E} {Σ : LinCCAL.spec E} : _ -> Prop :=
    dead_state_intro s :
      (forall i, dead_thread (LinCCAL.TMap.find i s)) ->
      dead_state (LinCCAL.mkst Σ s Σdeadlock).

  Proposition dead_correct E (Σ : LinCCAL.spec E) :
    LinCCAL.cal Σdeadlock (fun q => dead_impl) Σ.
  Proof.
    intros.
    eapply LinCCAL.correctness_invariant_sound with (P := dead_state).
    - split.
      + intros _ [s Hs] _ i q r R Hsi. cbn in *.
        specialize (Hs i).
        dependent destruction Hs; unfold dead_impl in *; try congruence.
        rewrite Hsi in x. dependent destruction x.
      + intros _ [s Hs] _ i q m k R Hsi. cbn in Hsi |- *.
        specialize (Hs i). cbn in Hs. rewrite Hsi in Hs.
        dependent destruction Hs; cbn; try congruence.
      + (* liveness cannot be proven *)
        admit.
      + intros _ [s Hs] _ s' Hs'.
        dependent destruction Hs'.
        * (* incoming call *)
          apply LinCCAL.reachable_base. constructor.
          intro i. destruct (classic (i = t)); subst.
          -- rewrite LinCCAL.TMap.gss. constructor; auto.
          -- rewrite LinCCAL.TMap.gso; auto.
        * (* return *)
          specialize (Hs t). setoid_rewrite H in Hs.
          dependent destruction Hs.
    - (* initial state *)
      constructor.
      intro i.
      rewrite LinCCAL.TMap.gempty.
      constructor.
  Abort.

End LinCCALExample.
