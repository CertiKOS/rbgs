Require Import FMapPositive.
Require Import Relation_Operators Operators_Properties.
Require Import Program.
Require Import Classical.

Require Import coqrel.LogicalRelations.
Require Import interfaces.Category.
Require Import models.EffectSignatures.


(** * Linearization-based Concurrent Certified Abstraction Layers *)

Module LinCCAL <: Category.

  Module TMap := PositiveMap.
  Notation tid := TMap.key.
  Notation tmap := TMap.t.

  (** ** Concurrent object specifications *)

  (** For simplicity, we use linearized atomic specifications and
    specify correctness directly in terms of this model. In their
    linearized form, the specifications are deterministic, however
    we allow both undefined and unimplementable behaviors.
    Undefined behaviors ([spec_bot]) release the implementation of
    any obligation, and are usually a consequence of illegal actions
    by the client (for example, a thread acquiring a lock twice).
    Conversely, unimplementable behaviors ([spec_top]) are simply
    impossible for an implementation to obey; this is usually meant
    to force a different linearization order. For example, in the
    atomic specification, acquiring a lock which is already held
    by a different thread will yield an unimplementable spec.
    However, a lock implementation can still obey the specification
    by delaying the linearization of [acquire] until the lock is
    released by the thread currently holding it. *)

  CoInductive spec_after {E : Sig.t} {m : Sig.op E} :=
    (*
    | spec_bot
     *)
    | spec_top
    | spec_cons (n : Sig.ar m) (k : tid -> forall m, @spec_after E m).

  Arguments spec_after : clear implicits.

  Notation spec E := (tid -> forall m, spec_after E m).

  (** To formalize this interpretation, we can describe the possible
    outcomes of performing the next invocation in a specification,
    namely the admissible return values and specification next states. *)

  (*
  Variant spec_query {E m} (n: Sig.ar m) (k: spec E) : spec_after E m -> Prop :=
    | spec_query_bot : spec_query n k spec_bot
    | spec_query_cons : spec_query n k (spec_cons n k).

  Definition spec_next {E} (Σ : spec E) t m n k : Prop :=
    spec_query n k (Σ t m).
   *)

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
        Σ t m = spec_cons n Σ' ->
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
        Δ t q = spec_cons r Δ' ->
        TMap.add t (mkts q T (Some r)) s = s' ->
        lstep (mkst Δ s Σ) (mkst Δ' s' Σ).

  (** ** Correctness *)

  (** Based on the constructions above, our ultimate goal is to show
    that no matter what methods are called and how the threads are
    scheduled, there is a way to perform commits such that the
    following invariant is always preserved. That is, every thread
    will eventually produce the result that was matched against the
    overlay specification. *)

  Definition threadstate_valid {E F} (e : option (threadstate E F)) :=
    forall x, e = Some x -> forall r, ts_prog x = Sig.var r -> ts_res x = Some r.

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
        Δ t q = spec_cons r Δ' ->
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

  (** *** Coinductive property *)

  (** The overall correctness property can be given as follows. *)

  CoInductive correct {E F} (M : Reg.Op.m E F) (s : state E F) : Prop :=
    {
      correct_valid :
        forall i, threadstate_valid (TMap.find i s);
      correct_next :
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
        P s -> forall i, threadstate_valid (TMap.find i s);
      ci_next s :
        P s -> forall s', estep M s s' -> reachable lstep P s';
    }.

  Lemma correct_ci {E F} (M : Reg.Op.m E F) :
    correctness_invariant M (correct M).
  Proof.
    constructor.
    - apply correct_valid.
    - intros u Hu u' Hu'.
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
    - intros s' Hs'. unfold reachable.
      edestruct @ci_next as (s'' & Hs'' & H''); eauto.
  Qed.

  (** *** Other properties *)

  Lemma correct_commit {E F} (M : Reg.Op.m E F) t s {q} r R Δ Σ :
    TMap.find t s = Some (mkts q (Sig.var r) R) ->
    correct M (mkst Δ s Σ) ->
    R = Some r.
  Proof.
    intros Ht Hs.
    eapply correct_valid in Hs. cbn in Hs.
    specialize (Hs _ Ht _ eq_refl).
    exact Hs.
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
    - intros _ [Σ u Hu] t s Hs r Hr. cbn in *. apply Hu in Hs.
      dependent destruction Hs; cbn in *; congruence.
    - intros _ [Σ u Hu] u' Hu'.
      dependent destruction Hu'.
      + (* invocation *)
        eexists. split. { apply rt_refl. }
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
        eexists. split. { apply rt_refl. }
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

  (** ** Composition *)

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
      - intros s Hs r Hr.
        dependent destruction H.
        dependent destruction Hs; cbn in *.
        specialize (He1 _ eq_refl _ eq_refl). cbn in *.
        congruence.
      - intros s Hs xr Hr.
        dependent destruction H; cbn in *.
        dependent destruction Hs; cbn in *.
        congruence.
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

    Lemma comp_tmap_convert t q T w s12 s1 s2 :
      comp_tmap (comp_running t q T) s12 s1 s2 ->
      comp_threadstate t w (TMap.find t s12) (TMap.find t s1) (TMap.find t s2) ->
      comp_tmap w s12 s1 s2.
    Proof.
      intros H Ht i.
      destruct (classic (i = t)); subst; eauto using comp_threadstate_o.
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
      exists Δ' Γ' s12' s1' s2',
        star lstep (mkst Δ s12 Σ) (mkst Δ' s12' Σ) /\
        correct M (mkst Δ' s1' Γ') /\
        correct N (mkst Γ' s2' Σ) /\
        comp_tmap w s12' s1' s2' /\
        forall i, TMap.find i s2 <> None -> TMap.find i s2' <> None.
    Proof.
      intros Hs2. revert Δ s1 s12.
      pattern Γ, s2, Σ. revert Γ s2 Σ Hs2.
      apply lsteps_ind; eauto 10 using rt_refl.
      (*
       * When [N] commits the result [ri] in thread [i],
       * we perform the corresponding [eaction] step in [M].
       * Note that since [N] is still active, this will not
       * break the established invariant.
       *)
      intros i m n U Γ Γ' s2 Σ Hs2i HΓ IH Δ s1 s12 Hs1 Hs12.
      pose proof (Hs12 i) as Hs12i. rewrite Hs2i in Hs12i.
      dependent destruction Hs12i.
      symmetry in x0. rename x0 into Hs12i.
      symmetry in x. rename x into Hs1i.
      cbn in *.
      eapply comp_tmap_action_l with (n:=n) in Hs12; eauto.
      eapply correct_next in Hs1; eauto using (eaction M i q m n). clear Hs1i.
      pose proof (TMap.gss i (mkts q (mk n) R) s1) as Hs1i.
      revert Hs12 Hs1 Hs1i.
      generalize (TMap.add i (mkts q (mk n) R) s1) as s1'. clear s1.
      intros s1. intros.
      (*
       * This will in turn trigger commits in [M]
       *)
      eapply comp_tmap_commit_l in Hs12
        as (Δ' & s12' & s1' & Hsteps & Hs1' & Hs12');
        eauto.
      edestruct IH
        as (Δ'' & Γ'' & s12'' & s1'' & s2' & Hsteps' & Hs1'' & Hs2' & Hs12'' & ?);
        eauto.
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

    Variant comp_state w : state E G -> Prop :=
      comp_state_intro Σ Γ Δ s12 s1 s2 :
        comp_tmap w s12 s1 s2 ->
        correct M (mkst Δ s1 Γ) ->
        correct N (mkst Γ s2 Σ) ->
        comp_state w (mkst Δ s12 Σ).

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
        assert (Q = Some n) by eauto using correct_commit. subst. cbn in *.
        (*
         * The first step is to trigger the [ereturn] step in [N].
         *)
        eapply comp_tmap_return_r in Hs12; eauto.
        eapply correct_next in Hs2; eauto using ereturn.
        (*
         * Now that we have returned to a state where [N] is inactive,
         * the induction hypothesis will be able to take care of the
         * remainder of the execution. However, the commit steps of
         * [N] triggered by the [ereturn] step must first be processed.
         *)
        edestruct comp_tmap_commit_r
          as (Δ' & Γ' & s12' & s1' & s2' & Hsteps & Hs1' & Hs2' & Hs12' & _);
          eauto.
        eapply reachable_steps; eauto.
        eapply IHmk. econstructor; eauto.
    Qed.

    Lemma comp_run t q T s :
      comp_state (comp_running t q T) s ->
      reachable lstep (comp_state comp_ready) s.
    Proof.
      revert s.
      induction T as [m mk IHmk | r];
      intros _ [Σ Γ Δ s12 s1 s2 Hs12 Hs1 Hs2].
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
        eapply correct_next in Hs2; eauto using (einvoke N t m).
        eapply comp_tmap_invoke_r in Hs12; eauto.
        pose proof (TMap.gss t (mkts m (N m) None) s2) as Hs2t'.
        revert Hs12 Hs1 Hs2 Hs1t Hs2t'.
        generalize (TMap.add t (mkts m (N m) None) s2) as s2'. clear -IHmk.
        intros s2 Hs12 Hs1 Hs2 Hs1t Hs2t.
        edestruct comp_tmap_commit_r
          as (Δ' & Γ' & s12' & s1' & s2' & Hsteps & Hs1' & Hs2' & Hs12' & ?);
          eauto.
        eapply reachable_steps; eauto.
        eapply comp_run_r; eauto.
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
        + eapply comp_run_r; eauto.
          congruence.
    Qed.

    Lemma comp_ci :
      correctness_invariant (Reg.Op.compose M N) (comp_state comp_ready).
    Proof.
      split.
      - intros _ [ ] i.
        eapply comp_threadstate_valid; eauto.
        + apply (correct_valid _ _ H0).
        + apply (correct_valid _ _ H1).
      - intros _ [? ? ? s12 s1 s2 Hs12 Hs1 Hs2] s12' H.
        dependent destruction H.
        + (*
           * We mirror any invocation in [M].
           *) 
          assert (Hs1t: TMap.find t s1 = None).
          {
            specialize (Hs12 t). rewrite H in Hs12.
            dependent destruction Hs12; auto.
          }
          eapply correct_next in Hs1; eauto using (einvoke M t q).
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
          eapply correct_next in Hs2; eauto using (eaction N t m u v).
          eapply comp_tmap_action_r in Hs12; eauto.
          eapply comp_tmap_commit_r in Hs2; eauto.
          destruct Hs2
            as (Δ' & Γ' & s12' & s1' & s2' & Hsteps & Hs1' & Hs2' & Hs21' & _);
            eauto.
          eapply reachable_steps; eauto.
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
          eapply correct_next in Hs1; eauto using (ereturn M t q r).
          eapply comp_tmap_return_l in Hs12; eauto.
          eapply comp_tmap_commit_l in Hs1; eauto.
          destruct Hs1 as (Δ' & s12' & s1' & Hsteps & Hs1' & Hs12').
          eapply reachable_steps; eauto.
          eapply reachable_base.
          econstructor; eauto.
    Qed.

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

  Program Definition compose {L1 L2 L3} (M : m L2 L3) (N : m L1 L2) :=
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
End LinCCAL.
