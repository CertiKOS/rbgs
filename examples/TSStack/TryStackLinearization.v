Require Import FMapPositive.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Arith.
Require Import Coq.PArith.PArith.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Relations.Relation_Operators.
Require Import Lia.

Require Import models.EffectSignatures.
Require Import LinCCAL.
Require Import LTS.
Require Import Semantics.
Require Import TPSimulationSet.

Require Import examples.Common.Heap.
Require Import examples.Common.ThreadDomain.
Require Import examples.TSStack.ListPoolSpec.
Require Import examples.TSStack.TryStackAuxSpec.
Require Import examples.TSStack.TryStackAuxGhost.
Require Import examples.TSStack.TryStackSpec.


(** Trace-level theory of the TryStack layer.

    An abstract history [h] places the TryStack linearisation points of the
    operations recorded in a ghost-timed TryStackAux state: the abstract
    push-inv of each vertex (possibly lagging behind the concrete push-inv),
    and the atomic pop of each removed or speculatively popped vertex.  The
    abstract push-ret is fixed at the concrete push response.  Positions are
    pairs [(gap, rank)]: the abstract events of gap [g] happen right after
    the concrete event with clock value [g], ordered by rank.

    [Real] collects the abstract configurations of all consistent
    histories; it is the invariant of the layer proof. *)
Module TryStackLinearization.
  Import LTSSpec.
  Import LinCCALBase.
  Import Semantics.
  Import TPSimulationSet.TPSimulation.
  Import ListPoolSpec.
  Import TryStackAuxSpec.
  Import TryStackAuxGhost.
  Import TryStackSpec.

  (** * Positions *)

  Definition Pos : Type := (nat * nat)%type.

  Definition pos_lt (p q : Pos) : Prop :=
    fst p < fst q \/ (fst p = fst q /\ snd p < snd q).

  Definition pos_le (p q : Pos) : Prop := pos_lt p q \/ p = q.

  (** Ranks of gap [g] are bounded, and the rank [2g+2] is reserved for
      the abstract push response of the concrete event at [g]. *)
  Definition pos_ok (p : Pos) : Prop := snd p < 2 * fst p + 2.

  Definition ret_pos (r : nat) : Pos := pair r (2 * r + 2).

  Lemma pos_lt_trans p q r : pos_lt p q -> pos_lt q r -> pos_lt p r.
  Proof. unfold pos_lt. destruct p, q, r; simpl. lia. Qed.

  Lemma pos_lt_irrefl p : ~ pos_lt p p.
  Proof. unfold pos_lt. destruct p; simpl. lia. Qed.

  Lemma pos_lt_dec p q : {pos_lt p q} + {~ pos_lt p q}.
  Proof.
    unfold pos_lt. destruct p as [g1 k1], q as [g2 k2]; simpl.
    destruct (lt_dec g1 g2); [left; lia|].
    destruct (Nat.eq_dec g1 g2); [|right; lia].
    destruct (lt_dec k1 k2); [left; lia|right; lia].
  Qed.

  Lemma pos_trichotomy p q : pos_lt p q \/ p = q \/ pos_lt q p.
  Proof.
    unfold pos_lt. destruct p as [g1 k1], q as [g2 k2]; simpl.
    destruct (lt_eq_lt_dec g1 g2) as [[H|H]|H]; [left; lia| |right; right; lia].
    subst. destruct (lt_eq_lt_dec k1 k2) as [[H|H]|H];
      [left; lia|subst; right; left; reflexivity|right; right; lia].
  Qed.

  Lemma pos_ok_lt_ret_pos p r : pos_ok p -> fst p <= r -> pos_lt p (ret_pos r).
  Proof. unfold pos_ok, pos_lt, ret_pos. destruct p; simpl. lia. Qed.

  Lemma ret_pos_lt_gap r g : r < g -> pos_lt (ret_pos r) (pair g 0).
  Proof. unfold pos_lt, ret_pos; simpl. lia. Qed.

  (** * Phases

      What the layer proof knows about each active thread beyond the
      concrete state: the operation it invoked and, once the concrete
      response happened, its result. *)
  Section Phases.
    Context {A : Type}.

    Variant Phase : Type :=
    | PhPushInvoked (v : A)
    | PhPushPending (v : A) (loc : Addr)
    | PhPushDone (v : A)
    | PhPopInvoked
    | PhPopSnapshot
    | PhPopEmptyPending
    | PhPopDone (r : @TResult A).

    Definition PhaseMap : Type := tid -> option Phase.
  End Phases.

  Section Histories.
    Context {A : Type}.

    (** * Histories *)

    Record History : Type := {
      h_inv : LPNodeId -> option Pos;
      h_pop : LPNodeId -> option (Pos * tid)
    }.

    Definition abs_ret (s : @TryStackAuxState A) (n : LPNodeId) (q : Pos) : Prop :=
      exists r, tsa_node_ret s n = Some r /\ q = ret_pos r.

    (** Abstract edge from [x] to [y]: at the abstract push-inv of [x], the
        vertex [y] was already completed. *)
    Definition abs_edge (s : @TryStackAuxState A) (h : History)
        (x y : LPNodeId) : Prop :=
      exists p q, h_inv h x = Some p /\ abs_ret s y q /\ pos_lt q p.

    (** * Consistency of a history with a ghost-timed state *)

    Record consistent (s : @TryStackAuxState A) (h : History) : Prop := {
      (** Abstract push-inv: not before the concrete push-inv, not after
          the concrete push response, in the past. *)
      c_inv_placed : forall n p,
        h_inv h n = Some p ->
        pos_ok p /\ fst p < tsa_now s /\
        (exists i, tsa_node_inv s n = Some i /\ i <= fst p) /\
        (forall r, tsa_node_ret s n = Some r -> fst p <= r);
      (** A completed push has taken its abstract push-inv. *)
      c_ret_forces_inv : forall n r,
        tsa_node_ret s n = Some r -> exists p, h_inv h n = Some p;
      (** An abstract pop: after the vertex exists, within the popper's
          interval; a completed removal pops the recorded node, a
          speculative pop belongs to a pending snapshot containing the
          node. *)
      c_pop_placed : forall n p a,
        h_pop h n = Some (pair p a) ->
        pos_ok p /\ fst p < tsa_now s /\
        (exists q, h_inv h n = Some q /\ pos_lt q p) /\
        ((exists st rt, tsa_removals s n = Some (pair (pair a st) rt) /\
            st <= fst p /\ fst p <= rt) \/
         (tsa_removals s n = None /\
          exists st, TMap.find a (tsa_snap_time s) = Some st /\
            st <= fst p /\
            exists i, tsa_node_inv s n = Some i /\ i < st));
      (** Every completed removal is linearised. *)
      c_removal_popped : forall n a st rt,
        tsa_removals s n = Some (pair (pair a st) rt) ->
        exists p, h_pop h n = Some (pair p a);
      (** A pending snapshot speculates on at most one vertex. *)
      c_spec_unique : forall n m p q a,
        h_pop h n = Some (pair p a) -> h_pop h m = Some (pair q a) ->
        tsa_removals s n = None -> tsa_removals s m = None -> n = m;
      (** The popped vertex is a top of the live abstract graph. *)
      c_pop_top : forall n p a x q,
        h_pop h n = Some (pair p a) ->
        h_inv h x = Some q -> pos_lt q p -> abs_edge s h x n ->
        exists p' a', h_pop h x = Some (pair p' a') /\ pos_lt p' p;
      (** Positions are distinct. *)
      c_inv_unique : forall n m p,
        h_inv h n = Some p -> h_inv h m = Some p -> n = m;
      c_pop_unique : forall n m p a b,
        h_pop h n = Some (pair p a) -> h_pop h m = Some (pair p b) -> n = m;
      c_inv_pop_distinct : forall n m p a,
        h_inv h n = Some p -> h_pop h m = Some (pair p a) -> False
    }.

    (** * Phase consistency *)

    Definition latest_node (s : @TryStackAuxState A) (t : tid) (loc : Addr) : Prop :=
      exists i, tsa_node_inv s (pair t loc) = Some i /\
        forall loc' i', tsa_node_inv s (pair t loc') = Some i' -> i' <= i.


    Definition phase_consistent
        (c : @TryStackAuxControl A) (phi : @PhaseMap A) : Prop :=
      let s := match c with TSAReady s => s | TSAAtomicPending s _ _ => s end in
      (forall t loc,
        TMap.find t (tsa_pending_pushes s) = Some loc <->
        exists v, phi t = Some (PhPushPending v loc)) /\
      (forall t,
        (exists N, TMap.find t (tsa_snapshots s) = Some N) <->
        phi t = Some PhPopSnapshot) /\
      (forall t,
        phi t = Some PhPopEmptyPending <->
        exists op, c = TSAAtomicPending s t op) /\
      (forall t v loc, phi t = Some (PhPushPending v loc) ->
        tsa_vertices s (pair t loc) = Some v) /\
      (forall t v, phi t = Some (PhPushDone v) ->
        exists loc r, tsa_node_ret s (pair t loc) = Some r /\
          tsa_vertices s (pair t loc) = Some v /\
          latest_node s t loc) /\
      (forall t v owner loc, phi t = Some (PhPopDone (TSuccNode v owner loc)) ->
        tsa_vertices s (pair owner loc) = Some v /\
        exists st rt, tsa_removals s (pair owner loc) = Some (pair (pair t st) rt)) /\
      (** The empty branch is taken only when every vertex is garbage; the
          control state then blocks all other concrete steps. *)
      (forall t, phi t = Some PhPopEmptyPending -> tsa_all_vertices_garbage s).

    (** * Representation of an abstract configuration at a cut

        [represents_at s phi h P pending_done rho pi]: [rho] and the
        tokens [pi] are the abstract configuration obtained by executing
        the abstract events of [h] whose position is below [P].  The
        result tokens of failed/empty pops are already in place except for
        the thread [pending_done] (used while replaying its response). *)

    Definition placed_before (h : History) (P : Pos) (n : LPNodeId) : Prop :=
      exists q, h_inv h n = Some q /\ pos_lt q P.

    Definition popped_before (h : History) (P : Pos) (n : LPNodeId) : Prop :=
      exists q a, h_pop h n = Some (pair q a) /\ pos_lt q P.

    Definition popped_before_by (h : History) (P : Pos) (a : tid) (n : LPNodeId) : Prop :=
      exists q, h_pop h n = Some (pair q a) /\ pos_lt q P.

    Definition ret_before (s : @TryStackAuxState A) (P : Pos) (n : LPNodeId) : Prop :=
      exists r, tsa_node_ret s n = Some r /\ pos_lt (ret_pos r) P.

    Definition token_at (s : @TryStackAuxState A) (phi : @PhaseMap A)
        (h : History) (P : Pos) (pending_done : option tid)
        (t : tid) (tok : option (@LinState ETryStack)) : Prop :=
      match phi t with
      | None => tok = None
      | Some (PhPushInvoked v) => tok = Some (ls_inv (ts_push v))
      | Some (PhPushPending v loc) =>
          (placed_before h P (pair t loc) /\ tok = Some (ls_lini (ts_push v))) \/
          (~ placed_before h P (pair t loc) /\ tok = Some (ls_inv (ts_push v)))
      | Some (PhPushDone v) =>
          exists loc, latest_node s t loc /\
          ((ret_before s P (pair t loc) /\ tok = Some (ls_linr (ts_push v) tt)) \/
           (~ ret_before s P (pair t loc) /\ placed_before h P (pair t loc) /\
            tok = Some (ls_lini (ts_push v))) \/
           (~ placed_before h P (pair t loc) /\ tok = Some (ls_inv (ts_push v))))
      | Some PhPopInvoked => tok = Some (ls_inv ts_trypop)
      | Some PhPopEmptyPending => tok = Some (ls_inv ts_trypop)
      | Some PhPopSnapshot =>
          (exists n v, popped_before_by h P t n /\ tsa_removals s n = None /\
             tsa_vertices s n = Some v /\
             tok = Some (ls_linr ts_trypop (TSuccNode v (fst n) (snd n)))) \/
          ((forall n, popped_before_by h P t n -> tsa_removals s n <> None) /\
           tok = Some (ls_inv ts_trypop))
      | Some (PhPopDone (TSuccNode v owner loc)) =>
          (popped_before_by h P t (pair owner loc) /\
           tok = Some (ls_linr ts_trypop (TSuccNode v owner loc))) \/
          (~ popped_before_by h P t (pair owner loc) /\ tok = Some (ls_inv ts_trypop))
      | Some (PhPopDone r) =>
          (pending_done = Some t /\ tok = Some (ls_inv ts_trypop)) \/
          (pending_done <> Some t /\ tok = Some (ls_linr ts_trypop r))
      end.

    Definition represents_at (s : @TryStackAuxState A) (phi : @PhaseMap A)
        (h : History) (P : Pos) (pending_done : option tid)
        (rho : @TryStackControl A) (pi : tmap (@LinState ETryStack)) : Prop :=
      exists st, rho = TSReady st /\
      (forall n, placed_before h P n -> ts_vertices st n = tsa_vertices s n) /\
      (forall n, ~ placed_before h P n -> ts_vertices st n = None) /\
      (forall x y, ts_edges st x y <->
        (placed_before h P x /\ abs_edge s h x y)) /\
      (forall t loc, TMap.find t (ts_pending_pushes st) = Some loc <->
        (placed_before h P (pair t loc) /\ ~ ret_before s P (pair t loc))) /\
      (forall n, ts_garbage st n <-> popped_before h P n) /\
      (forall t, token_at s phi h P pending_done t (TMap.find t pi)).

    Definition final_cut (s : @TryStackAuxState A) : Pos := pair (tsa_now s) 0.

    Definition payload (c : @TryStackAuxControl A) : @TryStackAuxState A :=
      match c with TSAReady s => s | TSAAtomicPending s _ _ => s end.

    (** The abstract configurations realisable from the current state. *)
    Definition Real (c : @TryStackAuxControl A) (phi : @PhaseMap A)
        (rho : @TryStackControl A) (pi : tmap (@LinState ETryStack)) : Prop :=
      exists h, consistent (payload c) h /\
        represents_at (payload c) phi h (final_cut (payload c)) None rho pi.

    (** * Basic facts about cuts *)

    Lemma placed_before_mono h P Q n :
      pos_le P Q -> placed_before h P n -> placed_before h Q n.
    Proof.
      intros HPQ (q & Hq & Hlt). exists q. split; [exact Hq|].
      destruct HPQ as [HPQ| ->]; [eapply pos_lt_trans; eauto|exact Hlt].
    Qed.

    Lemma popped_before_mono h P Q n :
      pos_le P Q -> popped_before h P n -> popped_before h Q n.
    Proof.
      intros HPQ (q & a & Hq & Hlt). exists q, a. split; [exact Hq|].
      destruct HPQ as [HPQ| ->]; [eapply pos_lt_trans; eauto|exact Hlt].
    Qed.

    Definition next_pos (P : Pos) : Pos := pair (fst P) (S (snd P)).

    Lemma pos_lt_next P : pos_lt P (next_pos P).
    Proof. unfold pos_lt, next_pos; simpl. lia. Qed.

    (** [q < next P] iff [q < P] or [q = P]. *)
    Lemma pos_lt_next_iff q P :
      pos_lt q (next_pos P) <-> pos_lt q P \/ q = P.
    Proof.
      unfold pos_lt, next_pos. destruct q as [g1 k1], P as [g2 k2]; simpl.
      split.
      - intros [H|[H1 H2]]; [left; left; exact H|].
        subst. destruct (Nat.eq_dec k1 k2) as [->|Hne].
        + right. reflexivity.
        + left. right. split; [reflexivity|lia].
      - intros [[H|[H1 H2]]|H]; [left; exact H|right; split; lia|].
        inversion H; subst. right. split; lia.
    Qed.

    (** No event of [h] sits exactly at [P]. *)
    Definition no_event_at (s : @TryStackAuxState A) (h : History) (P : Pos) : Prop :=
      (forall n, h_inv h n <> Some P) /\
      (forall n a, h_pop h n <> Some (pair P a)) /\
      (forall n, ~ abs_ret s n P).

    Lemma placed_before_next_none h P n s :
      no_event_at s h P ->
      placed_before h (next_pos P) n <-> placed_before h P n.
    Proof.
      intros [Hinv _]. unfold placed_before. split.
      - intros (q & Hq & Hlt). apply pos_lt_next_iff in Hlt.
        destruct Hlt as [Hlt| ->]; [eauto|]. exfalso. eapply Hinv; eauto.
      - intros (q & Hq & Hlt). exists q. split; [exact Hq|].
        apply pos_lt_next_iff. now left.
    Qed.

    Lemma popped_before_next_none h P n s :
      no_event_at s h P ->
      popped_before h (next_pos P) n <-> popped_before h P n.
    Proof.
      intros [_ [Hpop _]]. unfold popped_before. split.
      - intros (q & a & Hq & Hlt). apply pos_lt_next_iff in Hlt.
        destruct Hlt as [Hlt| ->]; [eauto|]. exfalso. eapply Hpop; eauto.
      - intros (q & a & Hq & Hlt). exists q, a. split; [exact Hq|].
        apply pos_lt_next_iff. now left.
    Qed.

    Lemma popped_before_by_next_none h P a n s :
      no_event_at s h P ->
      popped_before_by h (next_pos P) a n <-> popped_before_by h P a n.
    Proof.
      intros [_ [Hpop _]]. unfold popped_before_by. split.
      - intros (q & Hq & Hlt). apply pos_lt_next_iff in Hlt.
        destruct Hlt as [Hlt| ->]; [eauto|]. exfalso. eapply Hpop; eauto.
      - intros (q & Hq & Hlt). exists q. split; [exact Hq|].
        apply pos_lt_next_iff. now left.
    Qed.

    Lemma ret_before_next_none h P n s :
      no_event_at s h P ->
      ret_before s (next_pos P) n <-> ret_before s P n.
    Proof.
      intros [_ [_ Hret]]. unfold ret_before. split.
      - intros (r & Hr & Hlt). apply pos_lt_next_iff in Hlt.
        destruct Hlt as [Hlt| Heq]; [eauto|]. exfalso. apply (Hret n).
        exists r. auto.
      - intros (r & Hr & Hlt). exists r. split; [exact Hr|].
        apply pos_lt_next_iff. now left.
    Qed.

    Lemma token_at_next_none s phi h P pd t tok :
      no_event_at s h P ->
      token_at s phi h P pd t tok -> token_at s phi h (next_pos P) pd t tok.
    Proof.
      intros Hno. unfold token_at. destruct (phi t) as [ph|]; [|tauto].
      destruct ph; try tauto.
      - rewrite (placed_before_next_none _ _ _ _ Hno). tauto.
      - intros (loc & Hlat & Hcase). exists loc. split; [exact Hlat|].
        rewrite (placed_before_next_none _ _ _ _ Hno),
          (ret_before_next_none _ _ _ _ Hno). exact Hcase.
      - intros H. destruct H as [H|H];
          [destruct H as (n & v & Hpop & Hrest)|destruct H as [Hnone Htok]].
        + left. exists n, v. rewrite (popped_before_by_next_none _ _ _ _ _ Hno).
          auto.
        + right. split; [|exact Htok]. intros n Hpop.
          apply Hnone. rewrite <- (popped_before_by_next_none _ _ _ _ _ Hno).
          exact Hpop.
      - destruct r as [v owner loc| |].
        + rewrite (popped_before_by_next_none _ _ _ _ _ Hno). tauto.
        + tauto.
        + tauto.
    Qed.

    Lemma represents_at_next_none s phi h P pd rho pi :
      no_event_at s h P ->
      represents_at s phi h P pd rho pi ->
      represents_at s phi h (next_pos P) pd rho pi.
    Proof.
      intros Hno (st & -> & HV & HVn & HE & HP & HG & Htok).
      exists st. split; [reflexivity|].
      refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
      - intros n Hn. apply HV. now rewrite <- (placed_before_next_none _ _ _ _ Hno).
      - intros n Hn. apply HVn. now rewrite <- (placed_before_next_none _ _ _ _ Hno).
      - intros x y. rewrite (HE x y). now rewrite (placed_before_next_none _ _ _ _ Hno).
      - intros t loc. rewrite (HP t loc).
        now rewrite (placed_before_next_none _ _ _ _ Hno),
          (ret_before_next_none _ _ _ _ Hno).
      - intros n. rewrite (HG n). now rewrite (popped_before_next_none _ _ _ _ Hno).
      - intros t. apply token_at_next_none; auto.
    Qed.

    (** * Position facts derived from consistency *)

    Lemma ret_pos_not_ok r : ~ pos_ok (ret_pos r).
    Proof. unfold pos_ok, ret_pos; simpl. lia. Qed.

    Lemma no_ret_at_ok s n P : pos_ok P -> ~ abs_ret s n P.
    Proof.
      intros Hok (r & Hr & ->). apply (ret_pos_not_ok r). exact Hok.
    Qed.

    Lemma ret_pos_not_lt_next P r :
      pos_ok P -> fst P <= r -> ~ pos_lt (ret_pos r) (next_pos P).
    Proof. unfold pos_ok, pos_lt, ret_pos, next_pos. destruct P; simpl. lia. Qed.

    Lemma inv_before_ret s h n p q :
      consistent s h -> h_inv h n = Some p -> abs_ret s n q -> pos_lt p q.
    Proof.
      intros Hc Hp (r & Hr & ->).
      destruct (c_inv_placed _ _ Hc _ _ Hp) as (Hok & _ & _ & Hret).
      apply pos_ok_lt_ret_pos; auto.
    Qed.

    Lemma inv_not_ret_before_next s h n P :
      consistent s h -> h_inv h n = Some P -> ~ ret_before s (next_pos P) n.
    Proof.
      intros Hc Hp (r & Hr & Hlt).
      destruct (c_inv_placed _ _ Hc _ _ Hp) as (Hok & _ & _ & Hret).
      exact (ret_pos_not_lt_next P r Hok (Hret r Hr) Hlt).
    Qed.

    Lemma pop_after_inv s h n q a p :
      consistent s h -> h_pop h n = Some (pair q a) -> h_inv h n = Some p ->
      pos_lt p q.
    Proof.
      intros Hc Hq Hp.
      destruct (c_pop_placed _ _ Hc _ _ _ Hq) as (_ & _ & (p' & Hp' & Hlt) & _).
      rewrite Hp in Hp'. inversion Hp'; subst. exact Hlt.
    Qed.

    Lemma placed_before_self s h n P :
      consistent s h -> h_inv h n = Some P -> ~ placed_before h P n.
    Proof.
      intros Hc Hp (q & Hq & Hlt). rewrite Hp in Hq. inversion Hq; subst.
      eapply pos_lt_irrefl; eauto.
    Qed.

    Lemma placed_before_next_inv s h n P m :
      consistent s h -> h_inv h n = Some P ->
      placed_before h (next_pos P) m <-> (m = n \/ placed_before h P m).
    Proof.
      intros Hc Hp. unfold placed_before. split.
      - intros (q & Hq & Hlt). apply pos_lt_next_iff in Hlt.
        destruct Hlt as [Hlt| ->]; [right; eauto|].
        left. eapply c_inv_unique; eauto.
      - intros [->|[q [Hq Hlt]]].
        + exists P. split; [exact Hp|apply pos_lt_next].
        + exists q. split; [exact Hq|]. apply pos_lt_next_iff. now left.
    Qed.

    Lemma popped_before_next_pop s h n P a m :
      consistent s h -> h_pop h n = Some (pair P a) ->
      popped_before h (next_pos P) m <-> (m = n \/ popped_before h P m).
    Proof.
      intros Hc Hp. unfold popped_before. split.
      - intros (q & b & Hq & Hlt). apply pos_lt_next_iff in Hlt.
        destruct Hlt as [Hlt| ->]; [right; eauto|].
        left. eapply c_pop_unique; eauto.
      - intros [->|[q [b [Hq Hlt]]]].
        + exists P, a. split; [exact Hp|apply pos_lt_next].
        + exists q, b. split; [exact Hq|]. apply pos_lt_next_iff. now left.
    Qed.

    Lemma popped_before_by_next_pop s h n P a b m :
      consistent s h -> h_pop h n = Some (pair P a) ->
      popped_before_by h (next_pos P) b m <->
      ((m = n /\ b = a) \/ popped_before_by h P b m).
    Proof.
      intros Hc Hp. unfold popped_before_by. split.
      - intros (q & Hq & Hlt). apply pos_lt_next_iff in Hlt.
        destruct Hlt as [Hlt| ->]; [right; eauto|].
        left. pose proof (c_pop_unique _ _ Hc _ _ _ _ _ Hq Hp). subst m.
        rewrite Hp in Hq. inversion Hq. auto.
      - intros [[-> ->]|[q [Hq Hlt]]].
        + exists P. split; [exact Hp|apply pos_lt_next].
        + exists q. split; [exact Hq|]. apply pos_lt_next_iff. now left.
    Qed.

    (** No pop happens at an inv position and vice versa. *)
    Lemma no_pop_at_inv s h n P :
      consistent s h -> h_inv h n = Some P ->
      forall m a, h_pop h m <> Some (pair P a).
    Proof. intros Hc Hp m a Hq. eapply c_inv_pop_distinct; eauto. Qed.

    Lemma no_inv_at_pop s h n P a :
      consistent s h -> h_pop h n = Some (pair P a) ->
      forall m, h_inv h m <> Some P.
    Proof. intros Hc Hp m Hq. eapply c_inv_pop_distinct; eauto. Qed.

    Lemma pop_pos_ok s h n P a :
      consistent s h -> h_pop h n = Some (pair P a) -> pos_ok P.
    Proof. intros Hc Hp. eapply c_pop_placed; eauto. Qed.

    Lemma inv_pos_ok s h n P :
      consistent s h -> h_inv h n = Some P -> pos_ok P.
    Proof. intros Hc Hp. eapply c_inv_placed; eauto. Qed.


    Lemma popped_before_by_next_nopop h P b m :
      (forall n a, h_pop h n <> Some (pair P a)) ->
      popped_before_by h (next_pos P) b m <-> popped_before_by h P b m.
    Proof.
      intros Hno. unfold popped_before_by. split.
      - intros (q & Hq & Hlt). apply pos_lt_next_iff in Hlt.
        destruct Hlt as [Hlt| ->]; [eauto|]. exfalso. eapply Hno; eauto.
      - intros (q & Hq & Hlt). exists q. split; [exact Hq|].
        apply pos_lt_next_iff. now left.
    Qed.

    Lemma popped_before_next_nopop h P m :
      (forall n a, h_pop h n <> Some (pair P a)) ->
      popped_before h (next_pos P) m <-> popped_before h P m.
    Proof.
      intros Hno. unfold popped_before. split.
      - intros (q & a & Hq & Hlt). apply pos_lt_next_iff in Hlt.
        destruct Hlt as [Hlt| ->]; [eauto|]. exfalso. eapply Hno; eauto.
      - intros (q & a & Hq & Hlt). exists q, a. split; [exact Hq|].
        apply pos_lt_next_iff. now left.
    Qed.

    Lemma ret_before_next_noret s P m :
      ~ abs_ret s m P ->
      ret_before s (next_pos P) m <-> ret_before s P m.
    Proof.
      intros Hno. unfold ret_before. split.
      - intros (r & Hr & Hlt). apply pos_lt_next_iff in Hlt.
        destruct Hlt as [Hlt| Heq]; [eauto|]. exfalso. apply Hno.
        exists r. auto.
      - intros (r & Hr & Hlt). exists r. split; [exact Hr|].
        apply pos_lt_next_iff. now left.
    Qed.

    Lemma placed_before_next_noinv h P m :
      (forall n, h_inv h n <> Some P) ->
      placed_before h (next_pos P) m <-> placed_before h P m.
    Proof.
      intros Hno. unfold placed_before. split.
      - intros (q & Hq & Hlt). apply pos_lt_next_iff in Hlt.
        destruct Hlt as [Hlt| ->]; [eauto|]. exfalso. eapply Hno; eauto.
      - intros (q & Hq & Hlt). exists q. split; [exact Hq|].
        apply pos_lt_next_iff. now left.
    Qed.

    (** Tokens of threads other than the pusher are unchanged across a
        push-inv position. *)
    Lemma token_at_next_inv_other s phi h P pd n t tok :
      consistent s h -> h_inv h n = Some P -> t <> fst n ->
      token_at s phi h P pd t tok -> token_at s phi h (next_pos P) pd t tok.
    Proof.
      intros Hc Hp Hneq.
      assert (Hok : pos_ok P) by (eapply inv_pos_ok; eauto).
      assert (Hnopop : forall m a, h_pop h m <> Some (pair P a))
        by (eapply no_pop_at_inv; eauto).
      assert (Hplaced : forall loc,
        placed_before h (next_pos P) (pair t loc) <-> placed_before h P (pair t loc)).
      { intro loc. rewrite (placed_before_next_inv _ _ _ _ _ Hc Hp). split.
        - intros [Heq|H]; [|exact H]. exfalso. apply Hneq. rewrite <- Heq. reflexivity.
        - intro H. now right. }
      unfold token_at. destruct (phi t) as [ph|]; [|tauto].
      destruct ph; try tauto.
      - rewrite Hplaced. tauto.
      - intros (loc & Hlat & Hcase). exists loc. split; [exact Hlat|].
        rewrite Hplaced, (ret_before_next_noret _ _ _ (no_ret_at_ok s _ P Hok)).
        exact Hcase.
      - intros H. destruct H as [H|H];
          [destruct H as (m & v & Hpop & Hrest)|destruct H as [Hnone Htok]].
        + left. exists m, v. rewrite (popped_before_by_next_nopop _ _ _ _ Hnopop). auto.
        + right. split; [|exact Htok]. intros m Hpop. apply Hnone.
          rewrite <- (popped_before_by_next_nopop _ _ _ _ Hnopop). exact Hpop.
      - destruct r as [v owner loc| |]; try tauto.
        rewrite (popped_before_by_next_nopop _ _ _ _ Hnopop). tauto.
    Qed.

    Lemma latest_node_unique s t loc1 loc2 :
      tsa_ghost_wf s -> latest_node s t loc1 -> latest_node s t loc2 -> loc1 = loc2.
    Proof.
      intros Hwf (i1 & H1 & Hmax1) (i2 & H2 & Hmax2).
      assert (i1 = i2) by (pose proof (Hmax1 _ _ H2); pose proof (Hmax2 _ _ H1); lia).
      subst i2.
      pose proof (wf_inv_unique _ _ _ _ Hwf H1 H2) as Heq. inversion Heq. reflexivity.
    Qed.

    (** Tokens of other threads are unchanged across a pop position. *)
    Lemma token_at_next_pop_other s phi h P pd n a t tok :
      consistent s h -> h_pop h n = Some (pair P a) -> t <> a ->
      token_at s phi h P pd t tok -> token_at s phi h (next_pos P) pd t tok.
    Proof.
      intros Hc Hp Hneq.
      assert (Hok : pos_ok P) by (eapply pop_pos_ok; eauto).
      assert (Hnoinv : forall m, h_inv h m <> Some P)
        by (eapply no_inv_at_pop; eauto).
      assert (Hpops : forall m,
        popped_before_by h (next_pos P) t m <-> popped_before_by h P t m).
      { intro m. rewrite (popped_before_by_next_pop _ _ _ _ _ _ _ Hc Hp). split.
        - intros [[_ Heq]|H]; [congruence|exact H].
        - intro H. now right. }
      unfold token_at. destruct (phi t) as [ph|]; [|tauto].
      destruct ph; try tauto.
      - rewrite (placed_before_next_noinv _ _ _ Hnoinv). tauto.
      - intros (loc & Hlat & Hcase). exists loc. split; [exact Hlat|].
        rewrite (placed_before_next_noinv _ _ _ Hnoinv),
          (ret_before_next_noret _ _ _ (no_ret_at_ok s _ P Hok)).
        exact Hcase.
      - intros H. destruct H as [H|H];
          [destruct H as (m & v & Hpop & Hrest)|destruct H as [Hnone Htok]].
        + left. exists m, v. rewrite Hpops. auto.
        + right. split; [|exact Htok]. intros m Hpop. apply Hnone.
          rewrite <- Hpops. exact Hpop.
      - destruct r as [v owner loc| |]; try tauto.
        rewrite Hpops. tauto.
    Qed.

    (** Tokens of other threads are unchanged across a push-ret position. *)
    Lemma token_at_next_ret_other s phi h pd t loc r t' tok :
      tsa_ghost_wf s -> consistent s h ->
      tsa_node_ret s (pair t loc) = Some r -> t' <> t ->
      token_at s phi h (ret_pos r) pd t' tok ->
      token_at s phi h (next_pos (ret_pos r)) pd t' tok.
    Proof.
      intros Hwf Hc Hr Hneq.
      assert (Hnoinv : forall m, h_inv h m <> Some (ret_pos r)).
      { intros m Hm. apply (ret_pos_not_ok r). eapply inv_pos_ok; eauto. }
      assert (Hnopop : forall m a, h_pop h m <> Some (pair (ret_pos r) a)).
      { intros m a Hm. apply (ret_pos_not_ok r). eapply pop_pos_ok; eauto. }
      assert (Hnoret : forall loc', ~ abs_ret s (pair t' loc') (ret_pos r)).
      { intros loc' (r' & Hr' & Heq). unfold ret_pos in Heq.
        inversion Heq; subst r'.
        pose proof (wf_ret_unique _ _ _ _ Hwf Hr' Hr) as Heq'.
        inversion Heq'. congruence. }
      unfold token_at. destruct (phi t') as [ph|]; [|tauto].
      destruct ph; try tauto.
      - rewrite (placed_before_next_noinv _ _ _ Hnoinv). tauto.
      - intros (loc' & Hlat & Hcase). exists loc'. split; [exact Hlat|].
        rewrite (placed_before_next_noinv _ _ _ Hnoinv),
          (ret_before_next_noret _ _ _ (Hnoret loc')).
        exact Hcase.
      - intros H. destruct H as [H|H];
          [destruct H as (m & v & Hpop & Hrest)|destruct H as [Hnone Htok]].
        + left. exists m, v. rewrite (popped_before_by_next_nopop _ _ _ _ Hnopop). auto.
        + right. split; [|exact Htok]. intros m Hpop. apply Hnone.
          rewrite <- (popped_before_by_next_nopop _ _ _ _ Hnopop). exact Hpop.
      - destruct r0 as [v owner loc'| |]; try tauto.
        rewrite (popped_before_by_next_nopop _ _ _ _ Hnopop). tauto.
    Qed.

    (** * Cut equivalence *)

    Definition cut_equiv (s : @TryStackAuxState A) (h : History) (P Q : Pos) : Prop :=
      (forall n, placed_before h P n <-> placed_before h Q n) /\
      (forall n, popped_before h P n <-> popped_before h Q n) /\
      (forall a n, popped_before_by h P a n <-> popped_before_by h Q a n) /\
      (forall n, ret_before s P n <-> ret_before s Q n).

    Lemma token_at_cut_equiv s phi h P Q pd t tok :
      cut_equiv s h P Q ->
      token_at s phi h P pd t tok -> token_at s phi h Q pd t tok.
    Proof.
      intros (Hpl & Hpo & Hpb & Hrt). unfold token_at.
      destruct (phi t) as [ph|]; [|tauto].
      destruct ph as [v|v loc|v| | | |r].
      - tauto.
      - rewrite Hpl. tauto.
      - intros (loc & Hlat & Hcase). exists loc. split; [exact Hlat|].
        rewrite Hpl, Hrt in Hcase. exact Hcase.
      - tauto.
      - intros H. destruct H as [H|H];
          [destruct H as (m & v & Hpop & Hrest)|destruct H as [Hnone Htok]].
        + left. exists m, v. rewrite <- Hpb. auto.
        + right. split; [|exact Htok]. intros m Hpop. apply Hnone.
          rewrite Hpb. exact Hpop.
      - tauto.
      - destruct r as [v owner loc| |]; [rewrite Hpb; tauto|tauto|tauto].
    Qed.

    Lemma represents_at_cut_equiv s phi h P Q pd rho pi :
      cut_equiv s h P Q ->
      represents_at s phi h P pd rho pi -> represents_at s phi h Q pd rho pi.
    Proof.
      intros Hcut (st & -> & HV & HVn & HE & HP & HG & Htok).
      pose proof Hcut as (Hpl & Hpo & Hpb & Hrt).
      exists st. split; [reflexivity|].
      refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
      - intros n Hn. apply HV. now rewrite Hpl.
      - intros n Hn. apply HVn. now rewrite Hpl.
      - intros x y. rewrite (HE x y). now rewrite Hpl.
      - intros t loc. rewrite (HP t loc). now rewrite Hpl, Hrt.
      - intros n. rewrite (HG n). now rewrite Hpo.
      - intros t. eapply token_at_cut_equiv; eauto.
    Qed.

    (** Moving the cut forward over a region without events. *)
    Lemma cut_equiv_shift s h P Q :
      pos_le P Q ->
      (forall n q, h_inv h n = Some q -> pos_lt q Q -> pos_lt q P) ->
      (forall n q a, h_pop h n = Some (pair q a) -> pos_lt q Q -> pos_lt q P) ->
      (forall n q, abs_ret s n q -> pos_lt q Q -> pos_lt q P) ->
      cut_equiv s h P Q.
    Proof.
      intros HPQ Hinv Hpop Hret.
      assert (Hle : forall q, pos_lt q P -> pos_lt q Q).
      { intros q Hq. destruct HPQ as [HPQ| ->]; [eapply pos_lt_trans; eauto|exact Hq]. }
      repeat split.
      - intros (q & Hq & Hlt). exists q. auto.
      - intros (q & Hq & Hlt). exists q. eauto.
      - intros (q & a & Hq & Hlt). exists q, a. auto.
      - intros (q & a & Hq & Hlt). exists q, a. eauto.
      - intros (q & Hq & Hlt). exists q. auto.
      - intros (q & Hq & Hlt). exists q. eauto.
      - intros (r & Hr & Hlt). exists r. auto.
      - intros (r & Hr & Hlt). exists r. split; [exact Hr|].
        apply (Hret n (ret_pos r)); [exists r; auto|exact Hlt].
    Qed.

    (** The cut [(g, 2g+3)] sees exactly the events below [(g+1, 0)]. *)
    Lemma cut_equiv_gap_end s h g :
      consistent s h ->
      cut_equiv s h (pair g (2 * g + 3)) (pair (S g) 0).
    Proof.
      intros Hc. apply cut_equiv_shift.
      - left. unfold pos_lt; simpl. lia.
      - intros n q Hq Hlt.
        destruct (c_inv_placed _ _ Hc _ _ Hq) as (Hok & _).
        unfold pos_ok in Hok. unfold pos_lt in *. destruct q; simpl in *. lia.
      - intros n q a Hq Hlt.
        destruct (c_pop_placed _ _ Hc _ _ _ Hq) as (Hok & _).
        unfold pos_ok in Hok. unfold pos_lt in *. destruct q; simpl in *. lia.
      - intros n q (r & Hr & ->) Hlt. unfold pos_lt, ret_pos in *. simpl in *. lia.
    Qed.

    (** Phase requirements for the abstract events of the last gap: the
        threads whose events are replayed are in the phase corresponding to
        the concrete event just recorded. *)
    Definition gap_phases (s : @TryStackAuxState A) (phi : @PhaseMap A)
        (h : History) (g : nat) : Prop :=
      (forall n k, h_inv h n = Some (pair g k) ->
        exists v, tsa_vertices s n = Some v /\
          (phi (fst n) = Some (PhPushPending v (snd n)) \/
           (phi (fst n) = Some (PhPushDone v) /\ latest_node s (fst n) (snd n)))) /\
      (forall n k a, h_pop h n = Some (pair (pair g k) a) ->
        exists v, tsa_vertices s n = Some v /\
          ((phi a = Some PhPopSnapshot /\ tsa_removals s n = None) \/
           phi a = Some (PhPopDone (TSuccNode v (fst n) (snd n))))) /\
      (forall t loc, tsa_node_ret s (pair t loc) = Some g ->
        exists v, phi t = Some (PhPushDone v) /\ latest_node s t loc).

    Lemma token_at_done_other s phi h P t t' tok :
      t' <> t ->
      token_at s phi h P (Some t) t' tok -> token_at s phi h P None t' tok.
    Proof.
      intros Hneq. unfold token_at. destruct (phi t') as [ph|]; [|tauto].
      destruct ph; try tauto.
      destruct r as [v owner loc| |]; try tauto.
      - intros [[Heq _]|[_ Htok]]; [inversion Heq; congruence|].
        right. split; [discriminate|exact Htok].
      - intros [[Heq _]|[_ Htok]]; [inversion Heq; congruence|].
        right. split; [discriminate|exact Htok].
    Qed.

    (** * Restriction of a history to the events below a cut *)

    Definition restrict (h : History) (C : Pos) : History :=
      {| h_inv := fun n => match h_inv h n with
                           | Some q => if pos_lt_dec q C then Some q else None
                           | None => None
                           end;
         h_pop := fun n => match h_pop h n with
                           | Some qa => if pos_lt_dec (fst qa) C then Some qa else None
                           | None => None
                           end |}.

    Lemma restrict_inv_some h C n q :
      h_inv (restrict h C) n = Some q <-> (h_inv h n = Some q /\ pos_lt q C).
    Proof.
      simpl. destruct (h_inv h n) as [q'|] eqn:Hq.
      - destruct (pos_lt_dec q' C) as [Hlt|Hnlt]; split.
        + intro H. inversion H; subst. auto.
        + intros [H _]. exact H.
        + discriminate.
        + intros [H Hlt]. inversion H; subst. contradiction.
      - split; [discriminate|]. intros [H _]. discriminate.
    Qed.

    Lemma restrict_pop_some h C n q a :
      h_pop (restrict h C) n = Some (pair q a) <->
      (h_pop h n = Some (pair q a) /\ pos_lt q C).
    Proof.
      simpl. destruct (h_pop h n) as [[q' a']|] eqn:Hq.
      - simpl. destruct (pos_lt_dec q' C) as [Hlt|Hnlt]; split.
        + intro H. inversion H; subst. auto.
        + intros [H _]. exact H.
        + discriminate.
        + intros [H Hlt]. inversion H; subst. contradiction.
      - split; [discriminate|]. intros [H _]. discriminate.
    Qed.

    Lemma restrict_placed_before h C Q n :
      pos_le Q C ->
      placed_before (restrict h C) Q n <-> placed_before h Q n.
    Proof.
      intros HQC. unfold placed_before. split.
      - intros (q & Hq & Hlt). apply restrict_inv_some in Hq. destruct Hq. eauto.
      - intros (q & Hq & Hlt). exists q. split; [|exact Hlt].
        apply restrict_inv_some. split; [exact Hq|].
        destruct HQC as [HQC| ->]; [eapply pos_lt_trans; eauto|exact Hlt].
    Qed.

    Lemma restrict_popped_before h C Q n :
      pos_le Q C ->
      popped_before (restrict h C) Q n <-> popped_before h Q n.
    Proof.
      intros HQC. unfold popped_before. split.
      - intros (q & a & Hq & Hlt). apply restrict_pop_some in Hq. destruct Hq. eauto.
      - intros (q & a & Hq & Hlt). exists q, a. split; [|exact Hlt].
        apply restrict_pop_some. split; [exact Hq|].
        destruct HQC as [HQC| ->]; [eapply pos_lt_trans; eauto|exact Hlt].
    Qed.

    Lemma restrict_popped_before_by h C Q a n :
      pos_le Q C ->
      popped_before_by (restrict h C) Q a n <-> popped_before_by h Q a n.
    Proof.
      intros HQC. unfold popped_before_by. split.
      - intros (q & Hq & Hlt). apply restrict_pop_some in Hq. destruct Hq. eauto.
      - intros (q & Hq & Hlt). exists q. split; [|exact Hlt].
        apply restrict_pop_some. split; [exact Hq|].
        destruct HQC as [HQC| ->]; [eapply pos_lt_trans; eauto|exact Hlt].
    Qed.

    Lemma restrict_abs_edge s h C x y :
      abs_edge s (restrict h C) x y <-> (abs_edge s h x y /\ placed_before h C x).
    Proof.
      unfold abs_edge, placed_before. split.
      - intros (p & q & Hp & Hq & Hlt). apply restrict_inv_some in Hp.
        destruct Hp as [Hp HpC]. split; eauto.
      - intros [H1 H2]. destruct H1 as (p & q & Hp & Hq & Hlt).
        destruct H2 as (p' & Hp' & HpC).
        rewrite Hp in Hp'. inversion Hp'; subst p'.
        exists p, q. repeat split; auto. apply restrict_inv_some. auto.
    Qed.

    (** Representation is insensitive to events at or beyond the cut. *)
    Lemma represents_at_restrict s phi h C pd rho pi :
      represents_at s phi (restrict h C) C pd rho pi <->
      represents_at s phi h C pd rho pi.
    Proof.
      assert (Hle : pos_le C C) by (right; reflexivity).
      assert (Hcut : forall h1 h2,
        (forall n, placed_before h1 C n <-> placed_before h2 C n) ->
        (forall n, popped_before h1 C n <-> popped_before h2 C n) ->
        (forall a n, popped_before_by h1 C a n <-> popped_before_by h2 C a n) ->
        (forall x y, placed_before h1 C x /\ abs_edge s h1 x y <->
                     placed_before h2 C x /\ abs_edge s h2 x y) ->
        represents_at s phi h1 C pd rho pi -> represents_at s phi h2 C pd rho pi).
      { intros h1 h2 Hpl Hpo Hpb Hedge (st & -> & HV & HVn & HE & HP & HG & Htok).
        exists st. split; [reflexivity|].
        refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
        - intros n Hn. apply HV. now rewrite Hpl.
        - intros n Hn. apply HVn. now rewrite Hpl.
        - intros x y. rewrite (HE x y). apply Hedge.
        - intros t loc. rewrite (HP t loc). now rewrite Hpl.
        - intros n. rewrite (HG n). now rewrite Hpo.
        - intros t. specialize (Htok t). unfold token_at in *.
          destruct (phi t) as [ph|]; [|exact Htok].
          destruct ph as [v|v loc|v| | | |r]; try exact Htok.
          + rewrite Hpl in Htok. exact Htok.
          + destruct Htok as (loc & Hlat & Hcase). exists loc. split; [exact Hlat|].
            rewrite Hpl in Hcase. exact Hcase.
          + destruct Htok as [H|H];
              [destruct H as (m & v & Hpop & Hrest)|destruct H as [Hnone Htok]].
            * left. exists m, v. rewrite <- Hpb. auto.
            * right. split; [|exact Htok]. intros m Hpop. apply Hnone.
              rewrite Hpb. exact Hpop.
          + destruct r as [v owner loc| |]; try exact Htok.
            rewrite Hpb in Htok. exact Htok. }
      split; apply Hcut; intros;
        try (apply restrict_placed_before; exact Hle);
        try (apply restrict_popped_before; exact Hle);
        try (apply restrict_popped_before_by; exact Hle);
        try (symmetry; apply restrict_placed_before; exact Hle);
        try (symmetry; apply restrict_popped_before; exact Hle);
        try (symmetry; apply restrict_popped_before_by; exact Hle).
      - rewrite restrict_abs_edge, restrict_placed_before by exact Hle. tauto.
      - rewrite restrict_abs_edge, restrict_placed_before by exact Hle. tauto.
    Qed.

    (** Tokens of a thread whose phase is unchanged transfer from the old
        state to the new one, provided the facts the token depends on
        agree at the cut. *)
    Lemma token_at_transfer_other s s' phi phi' h C pd t tok :
      phi' t = phi t -> pd <> Some t ->
      (forall n, ret_before s' C n <-> ret_before s C n) ->
      (forall loc, latest_node s' t loc <-> latest_node s t loc) ->
      (forall m, popped_before_by h C t m ->
        (tsa_removals s' m = None <-> tsa_removals s m = None)) ->
      (forall m, popped_before_by h C t m ->
        tsa_vertices s' m = tsa_vertices s m) ->
      token_at s phi h C None t tok -> token_at s' phi' h C pd t tok.
    Proof.
      intros Hphi Hpd Hret Hlat Hrem HV. unfold token_at. rewrite Hphi.
      destruct (phi t) as [ph|]; [|tauto].
      destruct ph as [v|v loc|v| | | |r]; try tauto.
      - intros (loc & Hl & Hcase). exists loc. split; [now apply Hlat|].
        rewrite Hret. exact Hcase.
      - intros H. destruct H as [H|H];
          [destruct H as (m & v & Hpop & Hrest)|destruct H as [Hnone Htok]].
        + left. exists m, v. rewrite Hrem, HV; auto.
        + right. split; [|exact Htok]. intros m Hpop. rewrite Hrem; auto.
      - destruct r as [v owner loc| |]; try tauto.
        + intros [[Hne _]|[_ Htok]]; [discriminate|]. right. auto.
        + intros [[Hne _]|[_ Htok]]; [discriminate|]. right. auto.
    Qed.

    (** * Generic step lemmas

        The facts relating the ghost state before ([s]) and after ([s'])
        a concrete event, as far as the events below the cut
        [C = final_cut s] are concerned. *)
    Record ghost_extends (s s' : @TryStackAuxState A) : Prop := {
      ge_now : tsa_now s <= tsa_now s';
      ge_inv_back : forall m i, tsa_node_inv s' m = Some i -> i < tsa_now s ->
        tsa_node_inv s m = Some i;
      ge_inv_fwd : forall m i, tsa_node_inv s m = Some i -> tsa_node_inv s' m = Some i;
      ge_ret_back : forall m r, tsa_node_ret s' m = Some r -> r < tsa_now s ->
        tsa_node_ret s m = Some r;
      ge_ret_fwd : forall m r, tsa_node_ret s m = Some r ->
        tsa_node_ret s' m = Some r /\ r < tsa_now s;
      ge_rem_fwd : forall m rec, tsa_removals s m = Some rec -> tsa_removals s' m = Some rec;
      ge_rem_back : forall m a st rt, tsa_removals s' m = Some (pair (pair a st) rt) ->
        (rt < tsa_now s -> tsa_removals s m = Some (pair (pair a st) rt)) /\
        (~ rt < tsa_now s -> tsa_removals s m = None /\
          TMap.find a (tsa_snap_time s) = Some st);
      ge_rem_none : forall m, tsa_removals s' m = None -> tsa_removals s m = None;
      ge_snap_back : forall a st, TMap.find a (tsa_snap_time s') = Some st ->
        st < tsa_now s -> TMap.find a (tsa_snap_time s) = Some st
    }.

    Lemma ge_abs_ret_below s s' n q C :
      ghost_extends s s' -> C = final_cut s -> pos_lt q C ->
      (abs_ret s' n q <-> abs_ret s n q).
    Proof.
      intros Hge -> Hlt. unfold abs_ret. split.
      - intros (r & Hr & ->). exists r. split; [|reflexivity].
        apply (ge_ret_back _ _ Hge); [exact Hr|].
        unfold pos_lt, ret_pos, final_cut in Hlt. simpl in Hlt. lia.
      - intros (r & Hr & ->). exists r. split; [|reflexivity].
        apply (ge_ret_fwd _ _ Hge). exact Hr.
    Qed.

    Lemma ge_ret_before s s' n C :
      ghost_extends s s' -> C = final_cut s ->
      (ret_before s' C n <-> ret_before s C n).
    Proof.
      intros Hge HC. unfold ret_before. split.
      - intros (r & Hr & Hlt). exists r. split; [|exact Hlt].
        apply (ge_ret_back _ _ Hge); [exact Hr|].
        subst C. unfold pos_lt, ret_pos, final_cut in Hlt. simpl in Hlt. lia.
      - intros (r & Hr & Hlt). exists r. split; [|exact Hlt].
        apply (ge_ret_fwd _ _ Hge). exact Hr.
    Qed.

    Lemma restrict_consistent s s' h' :
      tsa_ghost_wf s -> tsa_ghost_wf s' -> ghost_extends s s' ->
      consistent s' h' ->
      (forall n m p q a, h_pop h' n = Some (pair p a) -> h_pop h' m = Some (pair q a) ->
        pos_lt p (final_cut s) -> pos_lt q (final_cut s) ->
        tsa_removals s n = None -> tsa_removals s m = None -> n = m) ->
      consistent s (restrict h' (final_cut s)).
    Proof.
      intros Hwf Hwf' Hge Hc Hspec.
      set (C := final_cut s).
      assert (HC : forall q, pos_lt q C <-> fst q < tsa_now s).
      { intro q. unfold C, final_cut, pos_lt. destruct q; simpl. lia. }
      constructor.
      - intros n p Hp. apply restrict_inv_some in Hp. destruct Hp as [Hp HpC].
        destruct (c_inv_placed _ _ Hc _ _ Hp) as (Hok & _ & (i & Hi & Hile) & Hret).
        apply HC in HpC.
        repeat split; [exact Hok|exact HpC| |].
        + exists i. split; [|exact Hile]. apply (ge_inv_back _ _ Hge); [exact Hi|lia].
        + intros r Hr. apply Hret. apply (ge_ret_fwd _ _ Hge). exact Hr.
      - intros n r Hr. destruct (ge_ret_fwd _ _ Hge _ _ Hr) as [Hr' Hrnow].
        destruct (c_ret_forces_inv _ _ Hc _ _ Hr') as [p Hp].
        destruct (c_inv_placed _ _ Hc _ _ Hp) as (_ & _ & _ & Hret).
        exists p. apply restrict_inv_some. split; [exact Hp|].
        apply HC. specialize (Hret r Hr'). lia.
      - intros n p a Hp. apply restrict_pop_some in Hp. destruct Hp as [Hp HpC].
        destruct (c_pop_placed _ _ Hc _ _ _ Hp) as (Hok & _ & (q & Hq & Hqlt) & Hcase).
        pose proof (proj1 (HC p) HpC) as Hpnow.
        repeat split; [exact Hok|exact Hpnow| |].
        + exists q. split; [|exact Hqlt]. apply restrict_inv_some. split; [exact Hq|].
          eapply pos_lt_trans; eauto.
        + destruct Hcase as [Hcase|Hcase].
          * destruct Hcase as (st & rt & Hrem & Hst & Hrt).
            destruct (ge_rem_back _ _ Hge _ _ _ _ Hrem) as [Hback Hnew].
            destruct (lt_dec rt (tsa_now s)) as [Hlt|Hnlt].
            -- left. exists st, rt. auto.
            -- right. destruct (Hnew Hnlt) as [Hnone Hsnap]. split; [exact Hnone|].
               exists st. split; [exact Hsnap|]. split; [exact Hst|].
               destruct (wf_removal _ Hwf' _ _ _ _ Hrem) as (_ & _ & (i & Hi & Hilt) & _).
               exists i. split; [|exact Hilt].
               apply (ge_inv_back _ _ Hge); [exact Hi|lia].
          * destruct Hcase as (Hrem & st & Hsnap & Hst & i & Hi & Hilt).
            right. split; [apply (ge_rem_none _ _ Hge); exact Hrem|].
            exists st. split; [apply (ge_snap_back _ _ Hge); [exact Hsnap|lia]|].
            split; [exact Hst|]. exists i. split; [|exact Hilt].
            apply (ge_inv_back _ _ Hge); [exact Hi|lia].
      - intros n a st rt Hrem. pose proof (ge_rem_fwd _ _ Hge _ _ Hrem) as Hrem'.
        destruct (c_removal_popped _ _ Hc _ _ _ _ Hrem') as [p Hp].
        destruct (c_pop_placed _ _ Hc _ _ _ Hp) as (_ & _ & _ & Hcase).
        exists p. apply restrict_pop_some. split; [exact Hp|]. apply HC.
        destruct (wf_removal _ Hwf _ _ _ _ Hrem) as (_ & Hrtnow & _).
        destruct Hcase as [Hcase|[Hnone _]];
          [destruct Hcase as (st' & rt' & Hrem'' & _ & Hrt')|].
        + rewrite Hrem' in Hrem''. inversion Hrem''; subst. lia.
        + congruence.
      - intros n m p q a Hp Hq Hn Hm.
        apply restrict_pop_some in Hp. apply restrict_pop_some in Hq.
        destruct Hp as [Hp HpC]. destruct Hq as [Hq HqC].
        eapply Hspec; eauto.
      - intros n p a x q Hp Hx Hlt Hedge.
        apply restrict_pop_some in Hp. destruct Hp as [Hp HpC].
        apply restrict_inv_some in Hx. destruct Hx as [Hx HxC].
        apply restrict_abs_edge in Hedge. destruct Hedge as [Hedge _].
        assert (Hedge' : abs_edge s' h' x n).
        { destruct Hedge as (p0 & q0 & Hp0 & Hq0 & Hlt0). exists p0, q0.
          repeat split; auto. rewrite (ge_abs_ret_below s s' n q0 C Hge eq_refl); [exact Hq0|].
          rewrite Hx in Hp0. inversion Hp0; subst p0. eapply pos_lt_trans; eauto. }
        destruct (c_pop_top _ _ Hc _ _ _ _ _ Hp Hx Hlt Hedge') as (p' & a' & Hp' & Hlt').
        exists p', a'. split; [|exact Hlt']. apply restrict_pop_some. split; [exact Hp'|].
        eapply pos_lt_trans; eauto.
      - intros n m p Hn Hm. apply restrict_inv_some in Hn. apply restrict_inv_some in Hm.
        destruct Hn as [Hn _]. destruct Hm as [Hm _].
        eapply c_inv_unique; eauto.
      - intros n m p a b Hn Hm. apply restrict_pop_some in Hn. apply restrict_pop_some in Hm.
        destruct Hn as [Hn _]. destruct Hm as [Hm _].
        eapply c_pop_unique; eauto.
      - intros n m p a Hn Hm. apply restrict_inv_some in Hn. apply restrict_pop_some in Hm.
        destruct Hn as [Hn _]. destruct Hm as [Hm _].
        eapply c_inv_pop_distinct; eauto.
    Qed.

    (** Transferring a representation at the old final cut to the new
        state and phases. *)
    Lemma transfer_represents s s' phi phi' h' pd actor rho pi :
      ghost_extends s s' -> consistent s' h' ->
      (forall m, placed_before h' (final_cut s) m ->
        tsa_vertices s' m = tsa_vertices s m) ->
      (forall t, t <> actor -> phi' t = phi t) ->
      (pd = None \/ pd = Some actor) ->
      (forall t loc, t <> actor -> (latest_node s' t loc <-> latest_node s t loc)) ->
      (forall t m, t <> actor -> popped_before_by h' (final_cut s) t m ->
        (tsa_removals s' m = None <-> tsa_removals s m = None)) ->
      (forall tok, token_at s phi h' (final_cut s) None actor tok ->
        token_at s' phi' h' (final_cut s) pd actor tok) ->
      represents_at s phi h' (final_cut s) None rho pi ->
      represents_at s' phi' h' (final_cut s) pd rho pi.
    Proof.
      intros Hge Hc HV' Hphi Hpd Hlat Hrem Hactor (st & -> & HV & HVn & HE & HP & HG & Htok).
      set (C := final_cut s) in *.
      exists st. split; [reflexivity|].
      refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
      - intros m Hm. rewrite HV' by exact Hm. apply HV. exact Hm.
      - exact HVn.
      - intros x y. rewrite (HE x y). split; intros [Hx He]; split; auto.
        + destruct He as (p & q & Hp & Hq & Hlt). exists p, q. repeat split; auto.
          rewrite (ge_abs_ret_below s s' y q C Hge eq_refl); [exact Hq|].
          destruct Hx as (p' & Hp' & HpC). rewrite Hp in Hp'. inversion Hp'; subst p'.
          eapply pos_lt_trans; eauto.
        + destruct He as (p & q & Hp & Hq & Hlt). exists p, q. repeat split; auto.
          rewrite <- (ge_abs_ret_below s s' y q C Hge eq_refl); [exact Hq|].
          destruct Hx as (p' & Hp' & HpC). rewrite Hp in Hp'. inversion Hp'; subst p'.
          eapply pos_lt_trans; eauto.
      - intros t loc. rewrite (HP t loc). now rewrite (ge_ret_before s s' _ C Hge eq_refl).
      - exact HG.
      - intros t. destruct (Pos.eq_dec t actor) as [->|Hneq].
        + apply Hactor. apply Htok.
        + eapply token_at_transfer_other with (s := s) (phi := phi) (t := t).
          * apply Hphi. exact Hneq.
          * destruct Hpd as [->| ->]; [discriminate|]. intro Heq. inversion Heq. congruence.
          * intro n. apply (ge_ret_before s s' n C Hge eq_refl).
          * intro loc. apply Hlat. exact Hneq.
          * intros m Hm. apply (Hrem t m Hneq Hm).
          * intros m (q & Hq & Hlt). apply HV'.
            destruct (c_pop_placed _ _ Hc _ _ _ Hq) as (_ & _ & (q0 & Hq0 & Hlt0) & _).
            exists q0. split; [exact Hq0|]. eapply pos_lt_trans; eauto.
          * apply Htok.
    Qed.

    Definition upd (phi : @PhaseMap A) (actor : tid) (ph : @Phase A) : @PhaseMap A :=
      fun t => if Pos.eq_dec t actor then Some ph else phi t.

    Lemma upd_eq phi actor ph : upd phi actor ph actor = Some ph.
    Proof. unfold upd. destruct (Pos.eq_dec actor actor); congruence. Qed.

    Lemma upd_neq phi actor ph t : t <> actor -> upd phi actor ph t = phi t.
    Proof. unfold upd. intro H. destruct (Pos.eq_dec t actor); congruence. Qed.

    Lemma final_cut_lt s q : pos_lt q (final_cut s) <-> fst q < tsa_now s.
    Proof. unfold final_cut, pos_lt. destruct q; simpl. lia. Qed.

  End Histories.

  Section Replay.
    Context {A : Type} (D : ThreadDomain.t).

    Notation VF := (@VTryStack A D).
    Notation psteps := (@poss_steps ETryStack VF).
    Notation Ok rho pi := (@PossOk ETryStack VF rho pi).

    (** Replaying the abstract push-inv of [n] placed at [P]. *)
    Lemma replay_inv s phi h P pd n v rho pi :
      tsa_ghost_wf s -> consistent s h ->
      h_inv h n = Some P ->
      tsa_vertices s n = Some v ->
      (phi (fst n) = Some (PhPushPending v (snd n)) \/
       (phi (fst n) = Some (PhPushDone v) /\ latest_node s (fst n) (snd n))) ->
      represents_at s phi h P pd rho pi ->
      exists rho' pi',
        psteps (Ok rho pi) (Ok rho' pi') /\
        represents_at s phi h (next_pos P) pd rho' pi'.
    Proof.
      intros Hwf Hc Hp Hv Hphase (st & -> & HV & HVn & HE & HP & HG & Htok).
      destruct n as [t loc]. simpl in *.
      assert (Hok : pos_ok P) by (eapply inv_pos_ok; eauto).
      destruct (c_inv_placed _ _ Hc _ _ Hp) as (_ & Hnow & (i & Hi & Hile) & Hret).
      assert (Hnotplaced : ~ placed_before h P (pair t loc))
        by (eapply placed_before_self; eauto).
      assert (Hnotret_next : ~ ret_before s (next_pos P) (pair t loc))
        by (eapply inv_not_ret_before_next; eauto).
      assert (Hnotret : ~ ret_before s P (pair t loc)).
      { intro H. apply Hnotret_next. destruct H as (r & Hr & Hlt).
        exists r. split; [exact Hr|]. apply pos_lt_next_iff. now left. }
      assert (Hnopop : forall m a, h_pop h m <> Some (pair P a))
        by (eapply no_pop_at_inv; eauto).
      (* the pusher has no pending abstract push *)
      assert (Hpend_none : TMap.find t (ts_pending_pushes st) = None).
      { destruct (TMap.find t (ts_pending_pushes st)) as [loc'|] eqn:Hfind;
          [|reflexivity].
        exfalso. apply HP in Hfind. destruct Hfind as [Hplaced' Hnotret'].
        destruct Hplaced' as (q' & Hq' & Hlt').
        destruct (c_inv_placed _ _ Hc _ _ Hq') as (_ & _ & (i' & Hi' & Hile') & Hret').
        destruct (lt_eq_lt_dec i' i) as [[Hlt|Heq]|Hgt].
        - destruct (wf_same_actor _ Hwf _ _ _ _ _ Hi' Hi Hlt) as (r' & Hr' & Hr'lt).
          apply Hnotret'. exists r'. split; [exact Hr'|].
          unfold pos_lt, ret_pos; simpl. left. lia.
        - subst i'. pose proof (wf_inv_unique _ _ _ _ Hwf Hi' Hi) as Heq.
          inversion Heq; subst loc'. rewrite Hp in Hq'. inversion Hq'; subst q'.
          eapply pos_lt_irrefl; eauto.
        - destruct (wf_same_actor _ Hwf _ _ _ _ _ Hi Hi' Hgt) as (r & Hr & Hrlt).
          specialize (Hret r ltac:(first [exact Hr|reflexivity])).
          assert (fst q' <= fst P).
          { destruct Hlt' as [H|[H _]]; lia. }
          lia. }
      assert (Hfresh : ts_fresh_node st (pair t loc)).
      { split.
        - apply HVn. exact Hnotplaced.
        - intro Hg. apply HG in Hg. destruct Hg as (q & a & Hq & Hlt).
          pose proof (pop_after_inv _ _ _ _ _ _ Hc Hq Hp) as Hlt2.
          eapply pos_lt_irrefl. eapply pos_lt_trans; eauto. }
      assert (Htok_t : TMap.find t pi = Some (ls_inv (ts_push v))).
      { specialize (Htok t). unfold token_at in Htok.
        destruct Hphase as [Hph|[Hph Hlat]]; rewrite Hph in Htok.
        - destruct Htok as [[Hpl _]|[_ Htok]]; [contradiction|exact Htok].
        - destruct Htok as (loc0 & Hlat0 & Hcase).
          pose proof (latest_node_unique _ _ _ _ Hwf Hlat0 Hlat) as ->.
          destruct Hcase as [[Hr _]|[[_ [Hpl _]]|[_ Htok]]];
            [contradiction|contradiction|exact Htok]. }
      exists (TSReady (ts_start_push t loc v st)),
        (TMap.add t (ls_lini (ts_push v)) pi).
      split.
      - apply rt_step. eapply ps_inv; [|exact Htok_t].
        eapply step_ts_push_inv; eauto.
      - exists (ts_start_push t loc v st). split; [reflexivity|].
        refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
        + intros m Hm. apply (placed_before_next_inv _ _ _ _ _ Hc Hp) in Hm.
          unfold ts_start_push; simpl. unfold node_update.
          destruct (node_eq_dec (pair t loc) m) as [<-|Hneq].
          * now rewrite Hv.
          * destruct Hm as [Heq|Hm]; [congruence|]. now apply HV.
        + intros m Hm. unfold ts_start_push; simpl. unfold node_update.
          destruct (node_eq_dec (pair t loc) m) as [<-|Hneq].
          * exfalso. apply Hm. apply (placed_before_next_inv _ _ _ _ _ Hc Hp). now left.
          * apply HVn. intro Hm'. apply Hm.
            apply (placed_before_next_inv _ _ _ _ _ Hc Hp). now right.
        + intros x y. unfold ts_start_push; simpl.
          rewrite (placed_before_next_inv _ _ _ _ _ Hc Hp). split.
          * intros [Hxy|[-> [Hvert Hnp]]].
            -- apply HE in Hxy. destruct Hxy as [Hx He]. auto.
            -- split; [now left|].
               assert (Hy : placed_before h P y).
               { destruct (classic (placed_before h P y)) as [H|H]; [exact H|].
                 exfalso. apply Hvert. apply HVn. exact H. }
               assert (Hry : ret_before s P y).
               { destruct (classic (ret_before s P y)) as [H|H]; [exact H|].
                 exfalso. apply Hnp. unfold ts_is_pending.
                 apply HP. destruct y. auto. }
               destruct Hry as (r & Hr & Hlt).
               exists P, (ret_pos r). repeat split; auto. exists r. auto.
          * intros [[->|Hx] He].
            -- right. destruct He as (p & q & Hp' & Hq & Hlt).
               rewrite Hp in Hp'. inversion Hp'; subst p. clear Hp'.
               destruct Hq as (r & Hr & ->).
               destruct (c_ret_forces_inv _ _ Hc _ _ Hr) as [py Hpy].
               assert (Hpy_lt : pos_lt py (ret_pos r))
                 by (eapply inv_before_ret; eauto; exists r; auto).
               assert (Hplaced_y : placed_before h P y).
               { exists py. split; [exact Hpy|]. eapply pos_lt_trans; eauto. }
               refine (conj eq_refl (conj _ _)).
               ++ unfold ts_is_vertex. rewrite (HV y Hplaced_y).
                  destruct (c_inv_placed _ _ Hc _ _ Hpy) as (_ & _ & (iy & Hiy & _) & _).
                  pose proof (wf_inv_vertex _ _ _ Hwf Hiy) as Hvy.
                  unfold tsa_is_vertex in Hvy. exact Hvy.
               ++ intro Hpend. unfold ts_is_pending in Hpend.
                  destruct y as [ty ly]. simpl in Hpend. apply HP in Hpend.
                  destruct Hpend as [_ Hnr]. apply Hnr. exists r. auto.
            -- left. apply HE. auto.
        + intros t' loc'. unfold ts_start_push; simpl.
          destruct (Pos.eq_dec t' t) as [->|Hneq].
          * rewrite TMap.gss. split.
            -- intro Heq. inversion Heq; subst loc'. split; [|exact Hnotret_next].
               apply (placed_before_next_inv _ _ _ _ _ Hc Hp). now left.
            -- intros [Hpl Hnr].
               apply (placed_before_next_inv _ _ _ _ _ Hc Hp) in Hpl.
               destruct Hpl as [Heq|Hpl]; [inversion Heq; reflexivity|].
               exfalso.
               assert (Hfind : TMap.find t (ts_pending_pushes st) = Some loc').
               { apply HP. split; [exact Hpl|]. intro Hr. apply Hnr.
                 destruct Hr as (r & Hr & Hlt). exists r. split; [exact Hr|].
                 apply pos_lt_next_iff. now left. }
               congruence.
          * rewrite TMap.gso by exact Hneq. rewrite (HP t' loc').
            rewrite (ret_before_next_noret _ _ _ (no_ret_at_ok s _ P Hok)).
            rewrite (placed_before_next_inv _ _ _ _ _ Hc Hp).
            split; intros [Hpl Hnr]; split; auto.
            -- destruct Hpl as [Heq|Hpl]; [|exact Hpl]. inversion Heq. congruence.
        + intros m. unfold ts_start_push; simpl. rewrite (HG m).
          symmetry. apply popped_before_next_nopop. exact Hnopop.
        + intros t'. destruct (Pos.eq_dec t' t) as [->|Hneq].
          * rewrite TMap.gss. unfold token_at.
            assert (Hpl : placed_before h (next_pos P) (pair t loc)).
            { apply (placed_before_next_inv _ _ _ _ _ Hc Hp). now left. }
            destruct Hphase as [Hph|[Hph Hlat]]; rewrite Hph.
            -- left. auto.
            -- exists loc. split; [exact Hlat|]. right. left. auto.
          * rewrite TMap.gso by exact Hneq.
            apply (token_at_next_inv_other s phi h P pd (pair t loc)); auto.
    Qed.

    (** Replaying the abstract push response of [(t,loc)] at [ret_pos r]. *)
    Lemma replay_ret s phi h pd t loc r v rho pi :
      tsa_ghost_wf s -> consistent s h ->
      tsa_node_ret s (pair t loc) = Some r ->
      phi t = Some (PhPushDone v) -> latest_node s t loc ->
      represents_at s phi h (ret_pos r) pd rho pi ->
      exists rho' pi',
        psteps (Ok rho pi) (Ok rho' pi') /\
        represents_at s phi h (next_pos (ret_pos r)) pd rho' pi'.
    Proof.
      intros Hwf Hc Hr Hph Hlat (st & -> & HV & HVn & HE & HP & HG & Htok).
      set (P := ret_pos r) in *.
      destruct (c_ret_forces_inv _ _ Hc _ _ Hr) as [p Hp].
      assert (Hp_lt : pos_lt p P).
      { eapply inv_before_ret; eauto. exists r. auto. }
      assert (Hplaced : placed_before h P (pair t loc)) by (exists p; auto).
      assert (Hnotret : ~ ret_before s P (pair t loc)).
      { intros (r' & Hr' & Hlt). rewrite Hr in Hr'. inversion Hr'; subst r'.
        eapply pos_lt_irrefl; eauto. }
      assert (Hret_next : ret_before s (next_pos P) (pair t loc)).
      { exists r. split; [exact Hr|]. apply pos_lt_next. }
      assert (Hnoinv : forall m, h_inv h m <> Some P).
      { intros m Hm. apply (ret_pos_not_ok r). eapply inv_pos_ok; eauto. }
      assert (Hnopop : forall m a, h_pop h m <> Some (pair P a)).
      { intros m a Hm. apply (ret_pos_not_ok r). eapply pop_pos_ok; eauto. }
      assert (Hfind : TMap.find t (ts_pending_pushes st) = Some loc).
      { apply HP. auto. }
      assert (Htok_t : TMap.find t pi = Some (ls_lini (ts_push v))).
      { specialize (Htok t). unfold token_at in Htok. rewrite Hph in Htok.
        destruct Htok as (loc0 & Hlat0 & Hcase).
        pose proof (latest_node_unique _ _ _ _ Hwf Hlat0 Hlat) as ->.
        destruct Hcase as [[Hr' _]|[[_ [_ Htok]]|[Hnp _]]];
          [contradiction|exact Htok|contradiction]. }
      exists (TSReady (ts_finish_push t st)),
        (TMap.add t (ls_linr (ts_push v) tt) pi).
      split.
      - apply rt_step. eapply ps_ret; [|exact Htok_t].
        eapply step_ts_push_res; eauto.
      - exists (ts_finish_push t st). split; [reflexivity|].
        refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
        + intros m Hm. apply HV. now rewrite <- (placed_before_next_noinv _ _ _ Hnoinv).
        + intros m Hm. apply HVn. now rewrite <- (placed_before_next_noinv _ _ _ Hnoinv).
        + intros x y. unfold ts_finish_push; simpl. rewrite (HE x y).
          now rewrite (placed_before_next_noinv _ _ _ Hnoinv).
        + intros t' loc'. unfold ts_finish_push; simpl.
          destruct (Pos.eq_dec t' t) as [->|Hneq].
          * rewrite TMap.grs. split; [discriminate|].
            intros [Hpl Hnr]. exfalso.
            destruct (Nat.eq_dec loc' loc) as [->|Hneql]; [contradiction|].
            assert (Hfind' : TMap.find t (ts_pending_pushes st) = Some loc').
            { apply HP. split.
              - now rewrite <- (placed_before_next_noinv _ _ _ Hnoinv).
              - intro Hr'. apply Hnr. destruct Hr' as (r' & Hr' & Hlt).
                exists r'. split; [exact Hr'|]. apply pos_lt_next_iff. now left. }
            congruence.
          * rewrite TMap.gro by exact Hneq. rewrite (HP t' loc').
            rewrite (placed_before_next_noinv _ _ _ Hnoinv).
            assert (Hnoret : ~ abs_ret s (pair t' loc') P).
            { intros (r' & Hr' & Heq). unfold P, ret_pos in Heq.
              inversion Heq; subst r'.
              pose proof (wf_ret_unique _ _ _ _ Hwf Hr' Hr) as Heq'.
              inversion Heq'. congruence. }
            now rewrite (ret_before_next_noret _ _ _ Hnoret).
        + intros m. unfold ts_finish_push; simpl. rewrite (HG m).
          symmetry. apply popped_before_next_nopop. exact Hnopop.
        + intros t'. destruct (Pos.eq_dec t' t) as [->|Hneq].
          * rewrite TMap.gss. unfold token_at. rewrite Hph.
            exists loc. split; [exact Hlat|]. left. auto.
          * rewrite TMap.gso by exact Hneq.
            eapply token_at_next_ret_other; eauto.
    Qed.

    (** Replaying the atomic pop of [n] by [a] placed at [P]. *)
    Lemma replay_pop s phi h P pd n a v rho pi :
      tsa_ghost_wf s -> consistent s h ->
      h_pop h n = Some (pair P a) ->
      tsa_vertices s n = Some v ->
      ((phi a = Some PhPopSnapshot /\ tsa_removals s n = None) \/
       phi a = Some (PhPopDone (TSuccNode v (fst n) (snd n)))) ->
      represents_at s phi h P pd rho pi ->
      exists rho' pi',
        psteps (Ok rho pi) (Ok rho' pi') /\
        represents_at s phi h (next_pos P) pd rho' pi'.
    Proof.
      intros Hwf Hc Hp Hv Hphase (st & -> & HV & HVn & HE & HP & HG & Htok).
      assert (Hok : pos_ok P) by (eapply pop_pos_ok; eauto).
      destruct (c_pop_placed _ _ Hc _ _ _ Hp) as (_ & _ & (q & Hq & Hqlt) & _).
      assert (Hplaced : placed_before h P n) by (exists q; auto).
      assert (Hnoinv : forall m, h_inv h m <> Some P) by (eapply no_inv_at_pop; eauto).
      assert (Hnotpopped : ~ popped_before h P n).
      { intros (q' & b & Hq' & Hlt). rewrite Hp in Hq'. inversion Hq'; subst.
        eapply pos_lt_irrefl; eauto. }
      assert (Hnotpopped_by : ~ popped_before_by h P a n).
      { intros (q' & Hq' & Hlt). apply Hnotpopped. exists q', a. auto. }
      assert (Hlive : ts_is_live st n).
      { split.
        - unfold ts_is_vertex. rewrite (HV n Hplaced), Hv. discriminate.
        - intro Hg. apply HG in Hg. contradiction. }
      assert (Htop : lp_top (fun n' => ts_is_live st n') (ts_edges st) n).
      { split; [exact Hlive|].
        intros n' [Hvert Hng] Hedge. apply HE in Hedge.
        destruct Hedge as [Hpl' Habs]. destruct Hpl' as (q' & Hq' & Hlt').
        destruct (c_pop_top _ _ Hc _ _ _ _ _ Hp Hq' Hlt' Habs) as (p' & a' & Hp' & Hlt'').
        apply Hng. apply HG. exists p', a'. auto. }
      assert (Hvst : ts_vertices st n = Some v) by (rewrite (HV n Hplaced); exact Hv).
      assert (Htok_a : TMap.find a pi = Some (ls_inv ts_trypop)).
      { specialize (Htok a). unfold token_at in Htok.
        destruct Hphase as [[Hph Hrem]|Hph]; rewrite Hph in Htok.
        - destruct Htok as [H|[_ Htok]]; [|exact Htok].
          destruct H as (m & v' & Hpop & Hrem' & _).
          exfalso. destruct Hpop as (q' & Hq' & Hlt').
          pose proof (c_spec_unique _ _ Hc _ _ _ _ _ Hq' Hp Hrem' Hrem) as ->.
          apply Hnotpopped_by. exists q'. auto.
        - destruct n as [owner loc]. simpl in Htok.
          destruct Htok as [[Hpop _]|[_ Htok]]; [contradiction|exact Htok]. }
      exists (TSReady (ts_mark_garbage n st)),
        (TMap.add a (ls_linr ts_trypop (TSuccNode v (fst n) (snd n)))
          (TMap.add a (ls_lini ts_trypop) pi)).
      split.
      - eapply rt_trans.
        + apply rt_step. eapply ps_inv; [|exact Htok_a].
          eapply step_ts_trypop_inv. reflexivity.
        + apply rt_step. eapply ps_ret; [|apply TMap.gss].
          eapply step_ts_trypop_succ; eauto.
      - exists (ts_mark_garbage n st). split; [reflexivity|].
        refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
        + intros m Hm. apply HV. now rewrite <- (placed_before_next_noinv _ _ _ Hnoinv).
        + intros m Hm. apply HVn. now rewrite <- (placed_before_next_noinv _ _ _ Hnoinv).
        + intros x y. unfold ts_mark_garbage; simpl. rewrite (HE x y).
          now rewrite (placed_before_next_noinv _ _ _ Hnoinv).
        + intros t' loc'. unfold ts_mark_garbage; simpl. rewrite (HP t' loc').
          rewrite (placed_before_next_noinv _ _ _ Hnoinv),
            (ret_before_next_noret _ _ _ (no_ret_at_ok s _ P Hok)).
          reflexivity.
        + intros m. unfold ts_mark_garbage; simpl. unfold set_add.
          rewrite (HG m). rewrite (popped_before_next_pop _ _ _ _ _ _ Hc Hp).
          reflexivity.
        + intros t'. destruct (Pos.eq_dec t' a) as [->|Hneq].
          * rewrite TMap.gss. unfold token_at.
            assert (Hpb : popped_before_by h (next_pos P) a n).
            { exists P. split; [exact Hp|apply pos_lt_next]. }
            destruct Hphase as [[Hph Hrem]|Hph]; rewrite Hph.
            -- left. exists n, v. auto.
            -- destruct n as [owner loc]. simpl. left. auto.
          * rewrite TMap.gso by exact Hneq. rewrite TMap.gso by exact Hneq.
            eapply token_at_next_pop_other; eauto.
    Qed.

    (** Replaying every abstract event of gap [g] from rank [k] on. *)
    Lemma replay_gap s phi h pd g k rho pi :
      tsa_ghost_wf s -> consistent s h -> gap_phases s phi h g ->
      k <= 2 * g + 3 ->
      represents_at s phi h (pair g k) pd rho pi ->
      exists rho' pi',
        psteps (Ok rho pi) (Ok rho' pi') /\
        represents_at s phi h (pair g (2 * g + 3)) pd rho' pi'.
    Proof.
      intros Hwf Hc Hgap.
      remember (2 * g + 3 - k) as m eqn:Hm.
      revert k Hm rho pi.
      induction m as [|m IH]; intros k Hm rho pi Hk Hrep.
      - assert (k = 2 * g + 3) by lia. subst k.
        exists rho, pi. split; [apply rt_refl|exact Hrep].
      - set (P := pair g k) in *.
        assert (Hnext : next_pos P = pair g (S k)) by reflexivity.
        destruct Hgap as (Hginv & Hgpop & Hgret).
        destruct (classic (exists n, h_inv h n = Some P)) as [[n Hn]|Hnoinv].
        + destruct (Hginv n k Hn) as (v & Hv & Hph).
          destruct (replay_inv s phi h P pd n v rho pi Hwf Hc Hn Hv Hph Hrep)
            as (rho1 & pi1 & Hsteps1 & Hrep1).
          rewrite Hnext in Hrep1.
          destruct (IH (S k) ltac:(lia) rho1 pi1 ltac:(lia) Hrep1)
            as (rho' & pi' & Hsteps' & Hrep').
          exists rho', pi'. split; [eapply rt_trans; eauto|exact Hrep'].
        + destruct (classic (exists n a, h_pop h n = Some (pair P a))) as [Hex|Hnopop];
            [destruct Hex as (n & a & Hn)|].
          * destruct (Hgpop n k a Hn) as (v & Hv & Hph).
            destruct (replay_pop s phi h P pd n a v rho pi Hwf Hc Hn Hv Hph Hrep)
              as (rho1 & pi1 & Hsteps1 & Hrep1).
            rewrite Hnext in Hrep1.
            destruct (IH (S k) ltac:(lia) rho1 pi1 ltac:(lia) Hrep1)
              as (rho' & pi' & Hsteps' & Hrep').
            exists rho', pi'. split; [eapply rt_trans; eauto|exact Hrep'].
          * destruct (classic (exists n, abs_ret s n P)) as [Hex|Hnoret];
              [destruct Hex as (n & r & Hr & HP)|].
            -- (* the push response of n *)
               unfold P, ret_pos in HP. inversion HP; subst r.
               assert (Hk2 : k = 2 * g + 2) by lia. subst k.
               destruct n as [t loc].
               destruct (Hgret t loc Hr) as (v & Hph & Hlat).
               assert (HrepP : represents_at s phi h (ret_pos g) pd rho pi).
               { unfold ret_pos. exact Hrep. }
               destruct (replay_ret s phi h pd t loc g v rho pi Hwf Hc Hr Hph Hlat HrepP)
                 as (rho1 & pi1 & Hsteps1 & Hrep1).
               assert (Hnext' : next_pos (ret_pos g) = pair g (2 * g + 3))
                 by (unfold next_pos, ret_pos; simpl; f_equal; lia).
               rewrite Hnext' in Hrep1.
               exists rho1, pi1. split; [exact Hsteps1|exact Hrep1].
            -- assert (Hno : no_event_at s h P).
               { repeat split.
                 - intros n Hn. apply Hnoinv. eauto.
                 - intros n a Hn. apply Hnopop. eauto.
                 - intros n Hn. apply Hnoret. eauto. }
               pose proof (represents_at_next_none _ _ _ _ _ _ _ Hno Hrep) as Hrep1.
               rewrite Hnext in Hrep1.
               destruct (IH (S k) ltac:(lia) rho pi ltac:(lia) Hrep1)
                 as (rho' & pi' & Hsteps' & Hrep').
               exists rho', pi'. split; [exact Hsteps'|exact Hrep'].
    Qed.

    (** Replaying the whole last gap [g], ending at the cut [(g+1, 0)]. *)
    Lemma replay_last_gap s phi h pd g rho pi :
      tsa_ghost_wf s -> consistent s h -> gap_phases s phi h g ->
      represents_at s phi h (pair g 0) pd rho pi ->
      exists rho' pi',
        psteps (Ok rho pi) (Ok rho' pi') /\
        represents_at s phi h (pair (S g) 0) pd rho' pi'.
    Proof.
      intros Hwf Hc Hgap Hrep.
      destruct (replay_gap s phi h pd g 0 rho pi Hwf Hc Hgap ltac:(lia) Hrep)
        as (rho' & pi' & Hsteps & Hrep').
      exists rho', pi'. split; [exact Hsteps|].
      eapply represents_at_cut_equiv; [|exact Hrep'].
      apply cut_equiv_gap_end. exact Hc.
    Qed.

    (** The result steps of a failed or empty pop. *)
    Lemma replay_done s phi h P t r rho pi :
      tsa_ghost_wf s -> consistent s h ->
      phi t = Some (PhPopDone r) ->
      (r = TFail \/
       (r = TSuccEmpty /\ forall n, placed_before h P n -> popped_before h P n)) ->
      represents_at s phi h P (Some t) rho pi ->
      exists rho' pi',
        psteps (Ok rho pi) (Ok rho' pi') /\
        represents_at s phi h P None rho' pi'.
    Proof.
      intros Hwf Hc Hph Hr (st & -> & HV & HVn & HE & HP & HG & Htok).
      assert (Htok_t : TMap.find t pi = Some (ls_inv ts_trypop)).
      { specialize (Htok t). unfold token_at in Htok. rewrite Hph in Htok.
        destruct r as [v owner loc| |].
        - destruct Hr as [Hr|[Hr _]]; discriminate.
        - destruct Htok as [[_ Htok]|[Hne _]]; [exact Htok|congruence].
        - destruct Htok as [[_ Htok]|[Hne _]]; [exact Htok|congruence]. }
      exists (TSReady st),
        (TMap.add t (ls_linr ts_trypop r) (TMap.add t (ls_lini ts_trypop) pi)).
      split.
      - eapply rt_trans.
        + apply rt_step. eapply ps_inv; [|exact Htok_t].
          eapply step_ts_trypop_inv. reflexivity.
        + apply rt_step. eapply ps_ret; [|apply TMap.gss].
          destruct Hr as [->|[-> Hall]].
          * eapply step_ts_trypop_fail. reflexivity.
          * eapply step_ts_trypop_empty; [|reflexivity].
            intro n. split.
            -- intro Hvert. apply HG. apply Hall.
               destruct (classic (placed_before h P n)) as [H|H]; [exact H|].
               exfalso. apply Hvert. apply HVn. exact H.
            -- intro Hg. apply HG in Hg. destruct Hg as (q & a & Hq & Hlt).
               destruct (c_pop_placed _ _ Hc _ _ _ Hq) as (_ & _ & (q0 & Hq0 & Hlt0) & _).
               assert (Hpl : placed_before h P n).
               { exists q0. split; [exact Hq0|]. eapply pos_lt_trans; eauto. }
               unfold ts_is_vertex. rewrite (HV n Hpl).
               destruct (c_inv_placed _ _ Hc _ _ Hq0) as (_ & _ & (i & Hi & _) & _).
               pose proof (wf_inv_vertex _ _ _ Hwf Hi) as Hvn. exact Hvn.
      - exists st. split; [reflexivity|].
        refine (conj HV (conj HVn (conj HE (conj HP (conj HG _))))).
        intros t'. destruct (Pos.eq_dec t' t) as [->|Hneq].
        + rewrite TMap.gss. unfold token_at. rewrite Hph.
          destruct r as [v owner loc| |].
          * destruct Hr as [Hr|[Hr _]]; discriminate.
          * right. split; [discriminate|reflexivity].
          * right. split; [discriminate|reflexivity].
        + rewrite TMap.gso by exact Hneq. rewrite TMap.gso by exact Hneq.
          apply (token_at_done_other s phi h P t t'); auto.
    Qed.

    (** * Concrete events *)

    (** ** Push invocation *)
    Lemma real_step_push_inv s actor loc v phi h' :
      tsa_ghost_wf s -> phase_consistent (TSAReady s) phi ->
      TMap.find actor (tsa_pending_pushes s) = None ->
      tsa_fresh_node s (pair actor loc) ->
      phi actor = Some (PhPushInvoked v) ->
      consistent (tsa_start_push actor loc v s) h' ->
      consistent s (restrict h' (final_cut s)) /\
      forall rho pi,
        represents_at s phi (restrict h' (final_cut s)) (final_cut s) None rho pi ->
        exists rho' pi',
          psteps (Ok rho pi) (Ok rho' pi') /\
          represents_at (tsa_start_push actor loc v s)
            (upd phi actor (PhPushPending v loc)) h'
            (final_cut (tsa_start_push actor loc v s)) None rho' pi'.
    Proof.
      intros Hwf Hpc Hnone Hfresh Hph Hc'.
      set (s' := tsa_start_push actor loc v s) in *.
      set (phi' := upd phi actor (PhPushPending v loc)).
      destruct Hpc as (Hpc1 & Hpc2 & Hpc3 & Hpc4 & Hpc5 & Hpc6 & Hpc7). simpl in *.
      assert (Hwf' : tsa_ghost_wf s') by (apply start_push_wf; auto).
      assert (Hinv0 : tsa_node_inv s (pair actor loc) = None).
      { destruct (tsa_node_inv s (pair actor loc)) as [i|] eqn:Hi; [|reflexivity].
        exfalso. destruct Hfresh as [Hfresh _].
        pose proof (wf_inv_vertex _ _ _ Hwf Hi) as Hv. unfold tsa_is_vertex in Hv.
        congruence. }
      assert (Hinv_eq : tsa_node_inv s' (pair actor loc) = Some (tsa_now s)).
      { unfold s', tsa_start_push; simpl. unfold node_update.
        destruct (node_eq_dec (pair actor loc) (pair actor loc)); congruence. }
      assert (Hinv_ne : forall m, m <> pair actor loc ->
        tsa_node_inv s' m = tsa_node_inv s m).
      { intros m Hm. unfold s', tsa_start_push; simpl. unfold node_update.
        destruct (node_eq_dec (pair actor loc) m); congruence. }
      assert (Hge : ghost_extends s s').
      { constructor; unfold s', tsa_start_push; simpl; try tauto.
        - lia.
        - intros m i Hm Hlt. unfold node_update in Hm.
          destruct (node_eq_dec (pair actor loc) m) as [<-|Hneq]; [inversion Hm; lia|exact Hm].
        - intros m i Hm. unfold node_update.
          destruct (node_eq_dec (pair actor loc) m) as [<-|Hneq]; [congruence|exact Hm].
        - intros m r Hr. split; [exact Hr|]. eapply wf_ret_now; eauto.
        - intros m a st rt Hrem. split; [intros _; exact Hrem|].
          intro Hnlt. exfalso. apply Hnlt. eapply wf_removal; eauto. }
      assert (Hnot_placed_n0 : ~ placed_before h' (final_cut s) (pair actor loc)).
      { intros (q & Hq & Hlt). destruct (c_inv_placed _ _ Hc' _ _ Hq) as (_ & _ & (i & Hi & Hile) & _).
        rewrite Hinv_eq in Hi. inversion Hi; subst i. apply final_cut_lt in Hlt. lia. }
      split.
      - eapply restrict_consistent; eauto.
        intros n m p q a Hp Hq _ _ Hn Hm. eapply c_spec_unique; eauto.
      - intros rho pi Hrep.
        rewrite represents_at_restrict in Hrep.
        assert (Hrep' : represents_at s' phi' h' (final_cut s) None rho pi).
        { refine (transfer_represents s s' phi phi' h' None actor rho pi Hge Hc'
            _ _ _ _ _ _ Hrep).
          - intros m Hm. unfold s', tsa_start_push; simpl. unfold node_update.
            destruct (node_eq_dec (pair actor loc) m) as [<-|Hneq]; [contradiction|reflexivity].
          - intros t Hneq. apply upd_neq. exact Hneq.
          - now left.
          - intros t loc' Hneq. unfold latest_node.
            assert (Hio : forall l, tsa_node_inv s' (pair t l) = tsa_node_inv s (pair t l)).
            { intro l. unfold s', tsa_start_push; simpl. unfold node_update.
              destruct (node_eq_dec (pair actor loc) (pair t l)) as [Heq|Hne];
                [inversion Heq; congruence|reflexivity]. }
            split.
            + intros (i & Hi & Hmax). rewrite Hio in Hi. exists i. split; [exact Hi|].
              intros l' i' Hi'. apply (Hmax l' i'). rewrite Hio. exact Hi'.
            + intros (i & Hi & Hmax). exists i. split; [rewrite Hio; exact Hi|].
              intros l' i' Hi'. rewrite Hio in Hi'. apply (Hmax l' i'). exact Hi'.
          - intros t m _ _. reflexivity.
          - intros tok Htok. unfold token_at in *. rewrite Hph in Htok.
            unfold phi'. rewrite upd_eq. right. split; [exact Hnot_placed_n0|exact Htok]. }
        assert (Hgap : gap_phases s' phi' h' (tsa_now s)).
        { repeat split.
          - intros m k Hm.
            destruct (c_inv_placed _ _ Hc' _ _ Hm) as (_ & _ & (i & Hi & Hile) & Hret).
            simpl in Hile.
            destruct (node_eq_dec (pair actor loc) m) as [<-|Hneq];
              [rewrite Hinv_eq in Hi|rewrite Hinv_ne in Hi by congruence].
            + exists v. split.
              * unfold s', tsa_start_push; simpl. unfold node_update.
                destruct (node_eq_dec (pair actor loc) (pair actor loc)); congruence.
              * left. unfold phi'. simpl. rewrite upd_eq. reflexivity.
            + (* an old vertex lagging into this gap must be pending *)
              assert (Hretnone : tsa_node_ret s m = None).
              { destruct (tsa_node_ret s m) as [r|] eqn:Hr; [|reflexivity].
                exfalso. specialize (Hret r ltac:(first [exact Hr|reflexivity])). simpl in Hret.
                pose proof (wf_ret_now _ Hwf _ _ Hr). lia. }
              assert (Hpend : tsa_is_pending s m).
              { apply (wf_pending _ Hwf). eauto. }
              unfold tsa_is_pending in Hpend.
              apply Hpc1 in Hpend. destruct Hpend as [v' Hphm].
              exists v'. split.
              * unfold s', tsa_start_push; simpl. unfold node_update.
                destruct (node_eq_dec (pair actor loc) m); [congruence|].
                destruct m as [tm lm]. apply Hpc4. exact Hphm.
              * left. unfold phi'. rewrite upd_neq; [exact Hphm|].
                intro Heq. rewrite Heq in Hphm.
                assert (Hf : TMap.find actor (tsa_pending_pushes s) = Some (snd m))
                  by (apply Hpc1; eauto).
                congruence.
          - intros m k a Hm.
            destruct (c_pop_placed _ _ Hc' _ _ _ Hm) as (_ & _ & (q & Hq & Hqlt) & Hcase).
            destruct Hcase as [Hcase|Hcase].
            + destruct Hcase as (st & rt & Hrem & _ & Hrt). simpl in Hrt.
              exfalso. destruct (wf_removal _ Hwf _ _ _ _ Hrem) as (_ & Hrtnow & _). lia.
            + destruct Hcase as (Hrem & st & Hsnap & Hst & i & Hi & Hilt). simpl in *.
              destruct (node_eq_dec (pair actor loc) m) as [<-|Hneq];
                [rewrite Hinv_eq in Hi|rewrite Hinv_ne in Hi by congruence].
              * inversion Hi; subst. destruct (wf_snap_time _ Hwf _ _ Hsnap) as [Hlt _]. lia.
              * assert (Hsnapa : phi a = Some PhPopSnapshot).
                { apply Hpc2. destruct (wf_snap_time _ Hwf _ _ Hsnap) as [_ HN]. exact HN. }
                pose proof (wf_inv_vertex _ _ _ Hwf Hi) as Hvm. unfold tsa_is_vertex in Hvm.
                destruct (tsa_vertices s m) as [vm|] eqn:Hvm'; [|congruence].
                exists vm. split.
                -- unfold s', tsa_start_push; simpl. unfold node_update.
                   destruct (node_eq_dec (pair actor loc) m); congruence.
                -- left. split; [|exact Hrem]. unfold phi'. rewrite upd_neq; [exact Hsnapa|].
                   intro Heq. subst a. congruence.
          - intros t l Hr. simpl in Hr. exfalso.
            pose proof (wf_ret_now _ Hwf _ _ Hr). lia. }
        assert (Hcut : final_cut s = pair (tsa_now s) 0) by reflexivity.
        rewrite Hcut in Hrep'.
        destruct (replay_last_gap s' phi' h' None (tsa_now s) rho pi Hwf' Hc' Hgap Hrep')
          as (rho' & pi' & Hsteps & Hrep'').
        exists rho', pi'. split; [exact Hsteps|]. exact Hrep''.
    Qed.

    (** ** Push response *)
    Lemma real_step_push_res s actor loc v phi h' :
      tsa_ghost_wf s -> phase_consistent (TSAReady s) phi ->
      TMap.find actor (tsa_pending_pushes s) = Some loc ->
      phi actor = Some (PhPushPending v loc) ->
      consistent (tsa_finish_push actor s) h' ->
      consistent s (restrict h' (final_cut s)) /\
      forall rho pi,
        represents_at s phi (restrict h' (final_cut s)) (final_cut s) None rho pi ->
        exists rho' pi',
          psteps (Ok rho pi) (Ok rho' pi') /\
          represents_at (tsa_finish_push actor s)
            (upd phi actor (PhPushDone v)) h'
            (final_cut (tsa_finish_push actor s)) None rho' pi'.
    Proof.
      intros Hwf Hpc Hfind Hph Hc'.
      set (s' := tsa_finish_push actor s) in *.
      set (phi' := upd phi actor (PhPushDone v)).
      destruct Hpc as (Hpc1 & Hpc2 & Hpc3 & Hpc4 & Hpc5 & Hpc6 & Hpc7). simpl in *.
      assert (Hwf' : tsa_ghost_wf s') by (apply (finish_push_wf s actor loc); auto).
      destruct (wf_pending_node_ret s actor loc Hwf Hfind) as [Hret0 [i0 Hinv0]].
      assert (Hret_eq : tsa_node_ret s' (pair actor loc) = Some (tsa_now s)).
      { unfold s', tsa_finish_push; simpl. rewrite Hfind. unfold node_update.
        destruct (node_eq_dec (pair actor loc) (pair actor loc)); congruence. }
      assert (Hret_ne : forall m, m <> pair actor loc ->
        tsa_node_ret s' m = tsa_node_ret s m).
      { intros m Hm. unfold s', tsa_finish_push; simpl. rewrite Hfind. unfold node_update.
        destruct (node_eq_dec (pair actor loc) m); congruence. }
      assert (Hlat : latest_node s actor loc).
      { exists i0. split; [exact Hinv0|]. intros l' i' Hi'.
        destruct (le_lt_dec i' i0) as [Hle|Hlt]; [exact Hle|].
        exfalso. destruct (wf_same_actor _ Hwf _ _ _ _ _ Hinv0 Hi' Hlt) as (r & Hr & _).
        congruence. }
      assert (Hlat' : latest_node s' actor loc).
      { unfold latest_node. unfold s', tsa_finish_push; simpl. exact Hlat. }
      assert (Hge : ghost_extends s s').
      { constructor; unfold s', tsa_finish_push; simpl; try tauto.
        - lia.
        - intros m r Hr Hlt. rewrite Hfind in Hr. unfold node_update in Hr.
          destruct (node_eq_dec (pair actor loc) m) as [<-|Hneq]; [inversion Hr; lia|exact Hr].
        - intros m r Hr. rewrite Hfind. unfold node_update. split.
          + destruct (node_eq_dec (pair actor loc) m) as [<-|Hneq]; [congruence|exact Hr].
          + eapply wf_ret_now; eauto.
        - intros m a st rt Hrem. split; [intros _; exact Hrem|].
          intro Hnlt. exfalso. apply Hnlt. eapply wf_removal; eauto. }
      assert (Hnotret : ~ ret_before s' (final_cut s) (pair actor loc)).
      { intros (r & Hr & Hlt). rewrite Hret_eq in Hr. inversion Hr; subst r.
        unfold pos_lt, ret_pos, final_cut in Hlt. simpl in Hlt. lia. }
      split.
      - eapply restrict_consistent; eauto.
        intros n m p q a Hp Hq _ _ Hn Hm. eapply c_spec_unique; eauto.
      - intros rho pi Hrep.
        rewrite represents_at_restrict in Hrep.
        assert (Hrep' : represents_at s' phi' h' (final_cut s) None rho pi).
        { refine (transfer_represents s s' phi phi' h' None actor rho pi Hge Hc'
            _ _ _ _ _ _ Hrep).
          - intros m _. reflexivity.
          - intros t Hneq. apply upd_neq. exact Hneq.
          - now left.
          - intros t loc' Hneq. unfold latest_node. unfold s', tsa_finish_push; simpl. tauto.
          - intros t m _ _. reflexivity.
          - intros tok Htok. unfold token_at in *. rewrite Hph in Htok.
            unfold phi'. rewrite upd_eq. exists loc. split; [exact Hlat'|].
            destruct Htok as [[Hpl Htok]|[Hnpl Htok]].
            + right. left. auto.
            + right. right. auto. }
        assert (Hgap : gap_phases s' phi' h' (tsa_now s)).
        { repeat split.
          - intros m k Hm.
            destruct (c_inv_placed _ _ Hc' _ _ Hm) as (_ & _ & (i & Hi & Hile) & Hret).
            simpl in Hile. unfold s', tsa_finish_push in Hi; simpl in Hi.
            destruct (node_eq_dec (pair actor loc) m) as [<-|Hneq].
            + exists v. split.
              * unfold s', tsa_finish_push; simpl. apply Hpc4. exact Hph.
              * right. split; [unfold phi'; rewrite upd_eq; reflexivity|exact Hlat'].
            + assert (Hneq' : m <> pair actor loc) by congruence.
              assert (Hretnone : tsa_node_ret s m = None).
              { destruct (tsa_node_ret s m) as [r|] eqn:Hr; [|reflexivity].
                exfalso. rewrite <- (Hret_ne m Hneq') in Hr. specialize (Hret r ltac:(first [exact Hr|reflexivity])).
                simpl in Hret. rewrite Hret_ne in Hr by exact Hneq'.
                pose proof (wf_ret_now _ Hwf _ _ Hr). lia. }
              assert (Hpend : tsa_is_pending s m).
              { apply (wf_pending _ Hwf). eauto. }
              unfold tsa_is_pending in Hpend.
              apply Hpc1 in Hpend. destruct Hpend as [v' Hphm].
              exists v'. split.
              * unfold s', tsa_finish_push; simpl. destruct m as [tm lm]. apply Hpc4. exact Hphm.
              * left. unfold phi'. rewrite upd_neq; [exact Hphm|].
                intro Heq. rewrite Heq in Hphm.
                assert (Hf : TMap.find actor (tsa_pending_pushes s) = Some (snd m))
                  by (apply Hpc1; eauto).
                rewrite Hfind in Hf. inversion Hf. apply Hneq.
                destruct m as [tm lm]. simpl in *. congruence.
          - intros m k a Hm.
            destruct (c_pop_placed _ _ Hc' _ _ _ Hm) as (_ & _ & (q & Hq & Hqlt) & Hcase).
            destruct Hcase as [Hcase|Hcase].
            + destruct Hcase as (st & rt & Hrem & _ & Hrt). simpl in Hrt.
              exfalso. destruct (wf_removal _ Hwf _ _ _ _ Hrem) as (_ & Hrtnow & _). lia.
            + destruct Hcase as (Hrem & st & Hsnap & Hst & i & Hi & Hilt). simpl in *.
              assert (Hsnapa : phi a = Some PhPopSnapshot).
              { apply Hpc2. destruct (wf_snap_time _ Hwf _ _ Hsnap) as [_ HN]. exact HN. }
              pose proof (wf_inv_vertex _ _ _ Hwf Hi) as Hvm. unfold tsa_is_vertex in Hvm.
              destruct (tsa_vertices s m) as [vm|] eqn:Hvm'; [|congruence].
              exists vm. split; [first [exact Hvm'|reflexivity|unfold s'; simpl; exact Hvm']|].
              left. split; [|exact Hrem]. unfold phi'. rewrite upd_neq; [exact Hsnapa|].
              intro Heq. subst a. congruence.
          - intros t l Hr.
            destruct (node_eq_dec (pair actor loc) (pair t l)) as [Heq|Hneq].
            + inversion Heq; subst t l. exists v. split; [unfold phi'; rewrite upd_eq; reflexivity|exact Hlat'].
            + rewrite Hret_ne in Hr by (apply not_eq_sym; exact Hneq). exfalso.
              pose proof (wf_ret_now _ Hwf _ _ Hr). lia. }
        assert (Hcut : final_cut s = pair (tsa_now s) 0) by reflexivity.
        rewrite Hcut in Hrep'.
        destruct (replay_last_gap s' phi' h' None (tsa_now s) rho pi Hwf' Hc' Hgap Hrep')
          as (rho' & pi' & Hsteps & Hrep'').
        exists rho', pi'. split; [exact Hsteps|]. exact Hrep''.
    Qed.

    (** ** Snapshot (interval trypop invocation) *)
    Lemma real_step_snapshot s actor phi h' :
      tsa_ghost_wf s -> phase_consistent (TSAReady s) phi ->
      TMap.find actor (tsa_snapshots s) = None ->
      phi actor = Some PhPopInvoked ->
      consistent (tsa_start_snapshot actor s) h' ->
      consistent s (restrict h' (final_cut s)) /\
      forall rho pi,
        represents_at s phi (restrict h' (final_cut s)) (final_cut s) None rho pi ->
        exists rho' pi',
          psteps (Ok rho pi) (Ok rho' pi') /\
          represents_at (tsa_start_snapshot actor s)
            (upd phi actor PhPopSnapshot) h'
            (final_cut (tsa_start_snapshot actor s)) None rho' pi'.
    Proof.
      intros Hwf Hpc Hnone Hph Hc'.
      set (s' := tsa_start_snapshot actor s) in *.
      set (phi' := upd phi actor PhPopSnapshot).
      destruct Hpc as (Hpc1 & Hpc2 & Hpc3 & Hpc4 & Hpc5 & Hpc6 & Hpc7). simpl in *.
      assert (Hwf' : tsa_ghost_wf s') by (apply start_snapshot_wf; auto).
      assert (Hsnap_eq : TMap.find actor (tsa_snap_time s') = Some (tsa_now s)).
      { unfold s', tsa_start_snapshot; simpl. apply TMap.gss. }
      assert (Hsnap_ne : forall a, a <> actor ->
        TMap.find a (tsa_snap_time s') = TMap.find a (tsa_snap_time s)).
      { intros a Ha. unfold s', tsa_start_snapshot; simpl. apply TMap.gso. exact Ha. }
      assert (Hge : ghost_extends s s').
      { constructor; unfold s', tsa_start_snapshot; simpl; try tauto.
        - lia.
        - intros m r Hr. split; [exact Hr|]. eapply wf_ret_now; eauto.
        - intros m a st rt Hrem. split; [intros _; exact Hrem|].
          intro Hnlt. exfalso. apply Hnlt. eapply wf_removal; eauto.
        - intros a st Hst Hlt. destruct (Pos.eq_dec a actor) as [->|Hneq].
          + rewrite TMap.gss in Hst. inversion Hst. lia.
          + rewrite TMap.gso in Hst by exact Hneq. exact Hst. }
      split.
      - eapply restrict_consistent; eauto.
        intros n m p q a Hp Hq _ _ Hn Hm. eapply c_spec_unique; eauto.
      - intros rho pi Hrep.
        rewrite represents_at_restrict in Hrep.
        assert (Hrep' : represents_at s' phi' h' (final_cut s) None rho pi).
        { refine (transfer_represents s s' phi phi' h' None actor rho pi Hge Hc'
            _ _ _ _ _ _ Hrep).
          - intros m _. reflexivity.
          - intros t Hneq. apply upd_neq. exact Hneq.
          - now left.
          - intros t loc' Hneq. unfold latest_node. unfold s', tsa_start_snapshot; simpl. tauto.
          - intros t m _ _. reflexivity.
          - intros tok Htok. unfold token_at in *. rewrite Hph in Htok.
            unfold phi'. rewrite upd_eq. right. split; [|exact Htok].
            intros m (q & Hq & Hlt).
            destruct (c_pop_placed _ _ Hc' _ _ _ Hq) as (_ & _ & _ & Hcase).
            destruct Hcase as [Hcase|Hcase].
            + destruct Hcase as (st & rt & Hrem & _ & _). unfold s' in *; simpl in *. congruence.
            + destruct Hcase as (_ & st & Hst & Hstle & _). rewrite Hsnap_eq in Hst.
              inversion Hst; subst st. apply final_cut_lt in Hlt. lia. }
        assert (Hgap : gap_phases s' phi' h' (tsa_now s)).
        { repeat split.
          - intros m k Hm.
            destruct (c_inv_placed _ _ Hc' _ _ Hm) as (_ & _ & (i & Hi & Hile) & Hret).
            simpl in Hile, Hi, Hret.
            assert (Hretnone : tsa_node_ret s m = None).
            { destruct (tsa_node_ret s m) as [r|] eqn:Hr; [|reflexivity].
              exfalso. specialize (Hret r ltac:(first [exact Hr|reflexivity])). pose proof (wf_ret_now _ Hwf _ _ Hr). lia. }
            assert (Hpend : tsa_is_pending s m).
            { apply (wf_pending _ Hwf). eauto. }
            unfold tsa_is_pending in Hpend.
            apply Hpc1 in Hpend. destruct Hpend as [v' Hphm].
            exists v'. split.
            + unfold s', tsa_start_snapshot; simpl. destruct m as [tm lm]. apply Hpc4. exact Hphm.
            + left. unfold phi'. rewrite upd_neq; [exact Hphm|].
              intro Heq. rewrite Heq in Hphm. congruence.
          - intros m k a Hm.
            destruct (c_pop_placed _ _ Hc' _ _ _ Hm) as (_ & _ & (q & Hq & Hqlt) & Hcase).
            destruct Hcase as [Hcase|Hcase].
            + destruct Hcase as (st & rt & Hrem & _ & Hrt). simpl in Hrt, Hrem.
              exfalso. destruct (wf_removal _ Hwf _ _ _ _ Hrem) as (_ & Hrtnow & _). lia.
            + destruct Hcase as (Hrem & st & Hsnap & Hst & i & Hi & Hilt). simpl in *.
              pose proof (wf_inv_vertex _ _ _ Hwf Hi) as Hvm. unfold tsa_is_vertex in Hvm.
              destruct (tsa_vertices s m) as [vm|] eqn:Hvm'; [|congruence].
              exists vm. split; [first [exact Hvm'|reflexivity|unfold s'; simpl; exact Hvm']|].
              left. split; [|exact Hrem].
              destruct (Pos.eq_dec a actor) as [->|Hneq].
              * unfold phi'. rewrite upd_eq. reflexivity.
              * rewrite Hsnap_ne in Hsnap by exact Hneq.
                unfold phi'. rewrite upd_neq by exact Hneq. apply Hpc2.
                destruct (wf_snap_time _ Hwf _ _ Hsnap) as [_ HN]. exact HN.
          - intros t l Hr. simpl in Hr. exfalso.
            pose proof (wf_ret_now _ Hwf _ _ Hr). lia. }
        assert (Hcut : final_cut s = pair (tsa_now s) 0) by reflexivity.
        rewrite Hcut in Hrep'.
        destruct (replay_last_gap s' phi' h' None (tsa_now s) rho pi Hwf' Hc' Hgap Hrep')
          as (rho' & pi' & Hsteps & Hrep'').
        exists rho', pi'. split; [exact Hsteps|]. exact Hrep''.
    Qed.

    (** ** Successful trypop response *)
    Lemma real_step_remove s actor n N v phi h' :
      tsa_ghost_wf s -> phase_consistent (TSAReady s) phi ->
      TMap.find actor (tsa_snapshots s) = Some N ->
      lp_top (fun n' => N n' /\ ~ tsa_garbage s n') (tsa_edges s) n ->
      tsa_vertices s n = Some v ->
      phi actor = Some PhPopSnapshot ->
      consistent (tsa_remove_node actor n s) h' ->
      consistent s (restrict h' (final_cut s)) /\
      forall rho pi,
        represents_at s phi (restrict h' (final_cut s)) (final_cut s) None rho pi ->
        exists rho' pi',
          psteps (Ok rho pi) (Ok rho' pi') /\
          represents_at (tsa_remove_node actor n s)
            (upd phi actor (PhPopDone (TSuccNode v (fst n) (snd n)))) h'
            (final_cut (tsa_remove_node actor n s)) None rho' pi'.
    Proof.
      intros Hwf Hpc HN Htop Hv Hph Hc'.
      set (s' := tsa_remove_node actor n s) in *.
      set (phi' := upd phi actor (PhPopDone (TSuccNode v (fst n) (snd n)))).
      destruct Hpc as (Hpc1 & Hpc2 & Hpc3 & Hpc4 & Hpc5 & Hpc6 & Hpc7). simpl in *.
      assert (Hwf' : tsa_ghost_wf s') by (eapply remove_node_wf; eauto).
      destruct (wf_snapshot _ Hwf _ _ HN) as (st & Hst & Hmem).
      destruct Htop as [[HNn Hnog] Htop].
      assert (Hrem0 : tsa_removals s n = None).
      { destruct (tsa_removals s n) as [rec|] eqn:Hrec; [|reflexivity].
        exfalso. apply Hnog. apply (wf_garbage _ Hwf). eauto. }
      assert (Hrem_eq : tsa_removals s' n = Some (pair (pair actor st) (tsa_now s))).
      { unfold s', tsa_remove_node; simpl. rewrite Hst. unfold node_update.
        destruct (node_eq_dec n n); congruence. }
      assert (Hrem_ne : forall m, m <> n -> tsa_removals s' m = tsa_removals s m).
      { intros m Hm. unfold s', tsa_remove_node; simpl. rewrite Hst. unfold node_update.
        destruct (node_eq_dec n m); congruence. }
      assert (Hsnap_ne : forall a, a <> actor ->
        TMap.find a (tsa_snap_time s') = TMap.find a (tsa_snap_time s)).
      { intros a Ha. unfold s', tsa_remove_node; simpl. apply TMap.gro. exact Ha. }
      assert (Hsnap_actor : TMap.find actor (tsa_snap_time s') = None).
      { unfold s', tsa_remove_node; simpl. apply TMap.grs. }
      assert (Hge : ghost_extends s s').
      { constructor; unfold s', tsa_remove_node; simpl; try tauto.
        - lia.
        - intros m r Hr. split; [exact Hr|]. eapply wf_ret_now; eauto.
        - intros m rec Hrec. rewrite Hst. unfold node_update.
          destruct (node_eq_dec n m) as [<-|Hneq]; [congruence|exact Hrec].
        - intros m a st' rt Hrem. rewrite Hst in Hrem. unfold node_update in Hrem.
          destruct (node_eq_dec n m) as [<-|Hneq].
          + inversion Hrem; subst a st' rt. split; [intro; lia|]. intros _. auto.
          + split; [intros _; exact Hrem|]. intro Hnlt. exfalso. apply Hnlt.
            eapply wf_removal; eauto.
        - intros m Hm. rewrite Hst in Hm. unfold node_update in Hm.
          destruct (node_eq_dec n m) as [<-|Hneq]; [discriminate|exact Hm].
        - intros a st' Hst' Hlt. destruct (Pos.eq_dec a actor) as [->|Hneq].
          + rewrite TMap.grs in Hst'. discriminate.
          + rewrite TMap.gro in Hst' by exact Hneq. exact Hst'. }
      (* the pop of n in h' is by actor *)
      destruct (c_removal_popped _ _ Hc' _ _ _ _ Hrem_eq) as [pn Hpn].
      split.
      - eapply restrict_consistent; eauto.
        intros m1 m2 p q a Hp Hq HpC HqC Hm1 Hm2.
        destruct (c_pop_placed _ _ Hc' _ _ _ Hp) as (_ & _ & _ & Hcase1).
        destruct (c_pop_placed _ _ Hc' _ _ _ Hq) as (_ & _ & _ & Hcase2).
        (* both speculative in s: in s' either speculative (other actor) or the removal *)
        destruct (node_eq_dec m1 n) as [->|Hne1]; destruct (node_eq_dec m2 n) as [->|Hne2];
          try reflexivity.
        + (* m1 = n, so a = actor; m2 <> n popped by actor: impossible in s' *)
          rewrite Hpn in Hp. inversion Hp; subst a.
          destruct Hcase2 as [Hcase2|Hcase2].
          * destruct Hcase2 as (st2 & rt2 & Hrem2 & _). rewrite Hrem_ne in Hrem2 by exact Hne2.
            congruence.
          * destruct Hcase2 as (_ & st2 & Hst2 & _). congruence.
        + rewrite Hpn in Hq. inversion Hq; subst a.
          destruct Hcase1 as [Hcase1|Hcase1].
          * destruct Hcase1 as (st1 & rt1 & Hrem1 & _). rewrite Hrem_ne in Hrem1 by exact Hne1.
            congruence.
          * destruct Hcase1 as (_ & st1 & Hst1 & _). congruence.
        + eapply c_spec_unique; eauto; rewrite Hrem_ne; auto.
      - intros rho pi Hrep.
        rewrite represents_at_restrict in Hrep.
        assert (Hrep' : represents_at s' phi' h' (final_cut s) None rho pi).
        { refine (transfer_represents s s' phi phi' h' None actor rho pi Hge Hc'
            _ _ _ _ _ _ Hrep).
          - intros m _. reflexivity.
          - intros t Hneq. apply upd_neq. exact Hneq.
          - now left.
          - intros t loc' Hneq. unfold latest_node. unfold s', tsa_remove_node; simpl. tauto.
          - intros t m Hneq (q & Hq & Hlt).
            assert (Hmn : m <> n).
            { intro Heq. subst m. rewrite Hpn in Hq. inversion Hq. congruence. }
            rewrite Hrem_ne by exact Hmn. tauto.
          - intros tok Htok. unfold token_at in *. rewrite Hph in Htok.
            unfold phi'. rewrite upd_eq.
            destruct Htok as [Htok|[Hnone Htok]].
            + destruct Htok as (m & v' & Hpop & Hremm & Hvm & Htok).
              destruct Hpop as (q & Hq & Hlt).
              destruct (c_pop_placed _ _ Hc' _ _ _ Hq) as (_ & _ & _ & Hcase).
              assert (Hmn : m = n).
              { destruct (node_eq_dec m n) as [Heq|Hne]; [exact Heq|]. exfalso.
                destruct Hcase as [Hcase|Hcase].
                - destruct Hcase as (st' & rt & Hrem & _). rewrite Hrem_ne in Hrem by exact Hne.
                  congruence.
                - destruct Hcase as (_ & st' & Hst' & _). congruence. }
              subst m. rewrite Hv in Hvm. inversion Hvm; subst v'.
              left. split; [|exact Htok]. exists q. destruct n; simpl in *; auto.
            + right. split; [|exact Htok]. intros (q & Hq & Hlt).
              apply (Hnone n); [|exact Hrem0]. exists q. destruct n; simpl in *; auto. }
        assert (Hgap : gap_phases s' phi' h' (tsa_now s)).
        { repeat split.
          - intros m k Hm.
            destruct (c_inv_placed _ _ Hc' _ _ Hm) as (_ & _ & (i & Hi & Hile) & Hret).
            simpl in Hile, Hi, Hret.
            assert (Hretnone : tsa_node_ret s m = None).
            { destruct (tsa_node_ret s m) as [r|] eqn:Hr; [|reflexivity].
              exfalso. specialize (Hret r ltac:(first [exact Hr|reflexivity])). pose proof (wf_ret_now _ Hwf _ _ Hr). lia. }
            assert (Hpend : tsa_is_pending s m).
            { apply (wf_pending _ Hwf). eauto. }
            unfold tsa_is_pending in Hpend.
            apply Hpc1 in Hpend. destruct Hpend as [v' Hphm].
            exists v'. split.
            + unfold s', tsa_remove_node; simpl. destruct m as [tm lm]. apply Hpc4. exact Hphm.
            + left. unfold phi'. rewrite upd_neq; [exact Hphm|].
              intro Heq. rewrite Heq in Hphm. congruence.
          - intros m k a Hm.
            destruct (c_pop_placed _ _ Hc' _ _ _ Hm) as (_ & _ & (q & Hq & Hqlt) & Hcase).
            destruct Hcase as [Hcase|Hcase].
            + destruct Hcase as (st' & rt & Hrem & _ & Hrt). simpl in Hrt.
              destruct (node_eq_dec m n) as [->|Hne].
              * rewrite Hrem_eq in Hrem. inversion Hrem; subst a st' rt.
                exists v. split; [exact Hv|]. right. unfold phi'. rewrite upd_eq. reflexivity.
              * rewrite Hrem_ne in Hrem by exact Hne. exfalso.
                destruct (wf_removal _ Hwf _ _ _ _ Hrem) as (_ & Hrtnow & _). lia.
            + destruct Hcase as (Hrem & st' & Hsnap & Hst' & i & Hi & Hilt). simpl in *.
              assert (Hneq : a <> actor).
              { intro Heq. subst a. congruence. }
              rewrite Hsnap_ne in Hsnap by exact Hneq.
              assert (Hmn : m <> n).
              { intro Heq. subst m. congruence. }
              rewrite Hrem_ne in Hrem by exact Hmn.
              pose proof (wf_inv_vertex _ _ _ Hwf Hi) as Hvm. unfold tsa_is_vertex in Hvm.
              destruct (tsa_vertices s m) as [vm|] eqn:Hvm'; [|congruence].
              exists vm. split; [first [exact Hvm'|reflexivity|unfold s'; simpl; exact Hvm']|].
              left. split; [|rewrite Hrem_ne by exact Hmn; exact Hrem].
              unfold phi'. rewrite upd_neq by exact Hneq. apply Hpc2.
              destruct (wf_snap_time _ Hwf _ _ Hsnap) as [_ HN']. exact HN'.
          - intros t l Hr. simpl in Hr. exfalso.
            pose proof (wf_ret_now _ Hwf _ _ Hr). lia. }
        assert (Hcut : final_cut s = pair (tsa_now s) 0) by reflexivity.
        rewrite Hcut in Hrep'.
        destruct (replay_last_gap s' phi' h' None (tsa_now s) rho pi Hwf' Hc' Hgap Hrep')
          as (rho' & pi' & Hsteps & Hrep'').
        exists rho', pi'. split; [exact Hsteps|]. exact Hrep''.
    Qed.

    (** ** Failed trypop response *)
    Lemma real_step_fail s actor N phi h' :
      tsa_ghost_wf s -> phase_consistent (TSAReady s) phi ->
      TMap.find actor (tsa_snapshots s) = Some N ->
      phi actor = Some PhPopSnapshot ->
      consistent (tsa_clear_snapshot actor s) h' ->
      consistent s (restrict h' (final_cut s)) /\
      forall rho pi,
        represents_at s phi (restrict h' (final_cut s)) (final_cut s) None rho pi ->
        exists rho' pi',
          psteps (Ok rho pi) (Ok rho' pi') /\
          represents_at (tsa_clear_snapshot actor s)
            (upd phi actor (PhPopDone TFail)) h'
            (final_cut (tsa_clear_snapshot actor s)) None rho' pi'.
    Proof.
      intros Hwf Hpc HN Hph Hc'.
      set (s' := tsa_clear_snapshot actor s) in *.
      set (phi' := upd phi actor (PhPopDone TFail)).
      destruct Hpc as (Hpc1 & Hpc2 & Hpc3 & Hpc4 & Hpc5 & Hpc6 & Hpc7). simpl in *.
      assert (Hwf' : tsa_ghost_wf s') by (apply clear_snapshot_wf; auto).
      assert (Hsnap_ne : forall a, a <> actor ->
        TMap.find a (tsa_snap_time s') = TMap.find a (tsa_snap_time s)).
      { intros a Ha. unfold s', tsa_clear_snapshot; simpl. apply TMap.gro. exact Ha. }
      assert (Hsnap_actor : TMap.find actor (tsa_snap_time s') = None).
      { unfold s', tsa_clear_snapshot; simpl. apply TMap.grs. }
      assert (Hge : ghost_extends s s').
      { constructor; unfold s', tsa_clear_snapshot; simpl; try tauto.
        - lia.
        - intros m r Hr. split; [exact Hr|]. eapply wf_ret_now; eauto.
        - intros m a st rt Hrem. split; [intros _; exact Hrem|].
          intro Hnlt. exfalso. apply Hnlt. eapply wf_removal; eauto.
        - intros a st Hst Hlt. destruct (Pos.eq_dec a actor) as [->|Hneq].
          + rewrite TMap.grs in Hst. discriminate.
          + rewrite TMap.gro in Hst by exact Hneq. exact Hst. }
      split.
      - eapply restrict_consistent; eauto.
        intros n m p q a Hp Hq _ _ Hn Hm. eapply c_spec_unique; eauto.
      - intros rho pi Hrep.
        rewrite represents_at_restrict in Hrep.
        assert (Hrep' : represents_at s' phi' h' (final_cut s) (Some actor) rho pi).
        { refine (transfer_represents s s' phi phi' h' (Some actor) actor rho pi Hge Hc'
            _ _ _ _ _ _ Hrep).
          - intros m _. reflexivity.
          - intros t Hneq. apply upd_neq. exact Hneq.
          - now right.
          - intros t loc' Hneq. unfold latest_node. unfold s', tsa_clear_snapshot; simpl. tauto.
          - intros t m _ _. reflexivity.
          - intros tok Htok. unfold token_at in *. rewrite Hph in Htok.
            unfold phi'. rewrite upd_eq.
            destruct Htok as [Htok|[Hnone Htok]].
            + destruct Htok as (m & v' & Hpop & Hremm & Hvm & Htok).
              destruct Hpop as (q & Hq & Hlt). exfalso.
              destruct (c_pop_placed _ _ Hc' _ _ _ Hq) as (_ & _ & _ & Hcase).
              destruct Hcase as [Hcase|Hcase].
              * destruct Hcase as (st & rt & Hrem & _). simpl in Hrem. congruence.
              * destruct Hcase as (_ & st & Hst & _). congruence.
            + left. auto. }
        assert (Hgap : gap_phases s' phi' h' (tsa_now s)).
        { repeat split.
          - intros m k Hm.
            destruct (c_inv_placed _ _ Hc' _ _ Hm) as (_ & _ & (i & Hi & Hile) & Hret).
            simpl in Hile, Hi, Hret.
            assert (Hretnone : tsa_node_ret s m = None).
            { destruct (tsa_node_ret s m) as [r|] eqn:Hr; [|reflexivity].
              exfalso. specialize (Hret r ltac:(first [exact Hr|reflexivity])). pose proof (wf_ret_now _ Hwf _ _ Hr). lia. }
            assert (Hpend : tsa_is_pending s m).
            { apply (wf_pending _ Hwf). eauto. }
            unfold tsa_is_pending in Hpend.
            apply Hpc1 in Hpend. destruct Hpend as [v' Hphm].
            exists v'. split.
            + unfold s', tsa_clear_snapshot; simpl. destruct m as [tm lm]. apply Hpc4. exact Hphm.
            + left. unfold phi'. rewrite upd_neq; [exact Hphm|].
              intro Heq. rewrite Heq in Hphm. congruence.
          - intros m k a Hm.
            destruct (c_pop_placed _ _ Hc' _ _ _ Hm) as (_ & _ & (q & Hq & Hqlt) & Hcase).
            destruct Hcase as [Hcase|Hcase].
            + destruct Hcase as (st & rt & Hrem & _ & Hrt). simpl in Hrt, Hrem.
              exfalso. destruct (wf_removal _ Hwf _ _ _ _ Hrem) as (_ & Hrtnow & _). lia.
            + destruct Hcase as (Hrem & st & Hsnap & Hst & i & Hi & Hilt). simpl in *.
              assert (Hneq : a <> actor).
              { intro Heq. subst a. congruence. }
              rewrite Hsnap_ne in Hsnap by exact Hneq.
              pose proof (wf_inv_vertex _ _ _ Hwf Hi) as Hvm. unfold tsa_is_vertex in Hvm.
              destruct (tsa_vertices s m) as [vm|] eqn:Hvm'; [|congruence].
              exists vm. split; [first [exact Hvm'|reflexivity|unfold s'; simpl; exact Hvm']|].
              left. split; [|exact Hrem].
              unfold phi'. rewrite upd_neq by exact Hneq. apply Hpc2.
              destruct (wf_snap_time _ Hwf _ _ Hsnap) as [_ HN']. exact HN'.
          - intros t l Hr. simpl in Hr. exfalso.
            pose proof (wf_ret_now _ Hwf _ _ Hr). lia. }
        assert (Hcut : final_cut s = pair (tsa_now s) 0) by reflexivity.
        rewrite Hcut in Hrep'.
        destruct (replay_last_gap s' phi' h' (Some actor) (tsa_now s) rho pi Hwf' Hc' Hgap Hrep')
          as (rho1 & pi1 & Hsteps1 & Hrep1).
        destruct (replay_done s' phi' h' (final_cut s') actor TFail rho1 pi1 Hwf' Hc'
          ltac:(unfold phi'; apply upd_eq) (or_introl eq_refl) Hrep1)
          as (rho' & pi' & Hsteps2 & Hrep2).
        exists rho', pi'. split; [eapply rt_trans; eauto|exact Hrep2].
    Qed.

    (** ** Empty trypop: invocation and response leave the ghost state unchanged. *)
    Lemma real_step_empty_inv (s : @TryStackAuxState A) actor (phi : @PhaseMap A) h rho pi :
      phi actor = Some PhPopInvoked ->
      represents_at s phi h (final_cut s) None rho pi ->
      represents_at s (upd phi actor PhPopEmptyPending) h (final_cut s) None rho pi.
    Proof.
      intros Hph (st & -> & HV & HVn & HE & HP & HG & Htok).
      exists st. split; [reflexivity|].
      refine (conj HV (conj HVn (conj HE (conj HP (conj HG _))))).
      intros t. specialize (Htok t). unfold token_at in *.
      destruct (Pos.eq_dec t actor) as [->|Hneq].
      - rewrite upd_eq. rewrite Hph in Htok. exact Htok.
      - rewrite upd_neq by exact Hneq. exact Htok.
    Qed.

    Lemma real_step_empty_res (s : @TryStackAuxState A) actor (phi : @PhaseMap A) h rho pi :
      tsa_ghost_wf s -> consistent s h ->
      tsa_all_vertices_garbage s ->
      phi actor = Some PhPopEmptyPending ->
      represents_at s phi h (final_cut s) None rho pi ->
      exists rho' pi',
        psteps (Ok rho pi) (Ok rho' pi') /\
        represents_at s (upd phi actor (PhPopDone TSuccEmpty)) h (final_cut s) None rho' pi'.
    Proof.
      intros Hwf Hc Hall Hph Hrep.
      set (phi' := upd phi actor (PhPopDone TSuccEmpty)).
      assert (Hrep' : represents_at s phi' h (final_cut s) (Some actor) rho pi).
      { destruct Hrep as (st & -> & HV & HVn & HE & HP & HG & Htok).
        exists st. split; [reflexivity|].
        refine (conj HV (conj HVn (conj HE (conj HP (conj HG _))))).
        intros t. specialize (Htok t). unfold token_at in *.
        destruct (Pos.eq_dec t actor) as [->|Hneq].
        - unfold phi'. rewrite upd_eq. rewrite Hph in Htok. left. auto.
        - unfold phi'. rewrite upd_neq by exact Hneq.
          destruct (phi t) as [ph|]; [|exact Htok].
          destruct ph as [v|v loc|v| | | |r]; try exact Htok.
          destruct r as [v owner loc| |]; try exact Htok.
          + destruct Htok as [[Hne _]|[_ Htok]]; [discriminate|].
            right. split; [|exact Htok]. intro Heq. inversion Heq. congruence.
          + destruct Htok as [[Hne _]|[_ Htok]]; [discriminate|].
            right. split; [|exact Htok]. intro Heq. inversion Heq. congruence. }
      apply (replay_done s phi' h (final_cut s) actor TSuccEmpty rho pi Hwf Hc); auto.
      - unfold phi'. apply upd_eq.
      - right. split; [reflexivity|]. intros m (q & Hq & Hlt).
        destruct (c_inv_placed _ _ Hc _ _ Hq) as (_ & _ & (i & Hi & _) & _).
        pose proof (wf_inv_vertex _ _ _ Hwf Hi) as Hvm.
        apply Hall in Hvm. apply (wf_garbage _ Hwf) in Hvm.
        destruct Hvm as [[[a st] rt] Hrem].
        destruct (c_removal_popped _ _ Hc _ _ _ _ Hrem) as [p Hp].
        destruct (c_pop_placed _ _ Hc _ _ _ Hp) as (_ & Hnow & _).
        exists p, a. split; [exact Hp|]. apply final_cut_lt. exact Hnow.
    Qed.

    (** * The abstract configuration after a concrete event

        The new configuration keeps exactly the successors of the old
        possibilities that realise a consistent history of the new state. *)
    Definition real_step_prop (Delta : @AbstractConfig ETryStack VF)
        (c' : @TryStackAuxControl A) (phi' : @PhaseMap A) :
        @AbstractConfigProp ETryStack VF :=
      fun rho pi => ac_steps Delta rho pi /\ Real c' phi' rho pi.

    Program Definition ac_real_step (Delta : @AbstractConfig ETryStack VF)
        (c' : @TryStackAuxControl A) (phi' : @PhaseMap A)
        (Hne : exists rho pi, real_step_prop Delta c' phi' rho pi) :
        @AbstractConfig ETryStack VF :=
      {| ac_active := ac_active Delta;
         ac_prop := real_step_prop Delta c' phi' |}.
    Next Obligation.
      intros. exact Hne.
    Qed.
    Next Obligation.
      intros. try unfold real_step_prop in *.
      match goal with
      | H : _ /\ _ |- _ =>
          destruct H as [Hsteps _]; eapply (ac_domain (ac_steps _)); exact Hsteps
      end.
    Qed.

    Lemma ac_real_step_subset_steps (Delta : @AbstractConfig ETryStack VF) c' phi' Hne :
      ac_subset (ac_real_step Delta c' phi' Hne) (ac_steps Delta).
    Proof. intros rho pi [H _]. exact H. Qed.

    Lemma ac_real_step_real (Delta : @AbstractConfig ETryStack VF) c' phi' Hne
        (rho : @TryStackControl A)
        (pi : tmap (@LinState ETryStack)) :
      ac_real_step Delta c' phi' Hne rho pi -> Real c' phi' rho pi.
    Proof. intros [_ H]. exact H. Qed.

    Lemma ac_real_step_intro (Delta : @AbstractConfig ETryStack VF) c' phi' Hne
        (rho : @TryStackControl A)
        (pi : tmap (@LinState ETryStack)) :
      ac_steps Delta rho pi -> Real c' phi' rho pi ->
      ac_real_step Delta c' phi' Hne rho pi.
    Proof. intros H1 H2. split; assumption. Qed.

  End Replay.

  (** * Sanity checks of the history model *)
  Section Sanity.
    Context {A : Type}.

    (** Without completed removals, the lock-step history (every push-inv
        placed at its concrete time, no pops) is consistent. *)
    Definition lockstep_history (s : @TryStackAuxState A) : History :=
      {| h_inv := fun n => match tsa_node_inv s n with
                           | Some i => Some (pair i 0)
                           | None => None
                           end;
         h_pop := fun _ => None |}.

    Lemma lockstep_consistent (s : @TryStackAuxState A) :
      tsa_ghost_wf s ->
      (forall n, tsa_removals s n = None) ->
      consistent s (lockstep_history s).
    Proof.
      intros Hwf Hnorem. constructor; simpl.
      - intros n p Hp. destruct (tsa_node_inv s n) as [i|] eqn:Hi; [|discriminate].
        inversion Hp; subst p. repeat split; simpl.
        + unfold pos_ok; simpl. lia.
        + eapply wf_inv_now; eauto.
        + exists i. split; [first [exact Hi|reflexivity]|lia].
        + intros r Hr. destruct (wf_ret_inv _ Hwf _ _ Hr) as (i' & Hi' & Hlt).
          assert (Hii : i = i') by (rewrite Hi in Hi'; inversion Hi'; reflexivity).
          subst i'. lia.
      - intros n r Hr. destruct (wf_ret_inv _ Hwf _ _ Hr) as (i & Hi & _).
        rewrite Hi. eauto.
      - intros n p a H. discriminate.
      - intros n a st rt H. rewrite Hnorem in H. discriminate.
      - intros n m p q a H. discriminate.
      - intros n p a x q H. discriminate.
      - intros n m p Hn Hm.
        destruct (tsa_node_inv s n) as [i|] eqn:Hi; [|discriminate].
        destruct (tsa_node_inv s m) as [j|] eqn:Hj; [|discriminate].
        inversion Hn; subst p. inversion Hm; subst j.
        exact (wf_inv_unique _ _ _ _ Hwf Hi Hj).
      - intros n m p a b Hn. discriminate.
      - intros n m p a Hn Hm. discriminate.
    Qed.

    (** The counterexample trace F1 of the design notes.  Thread 1 pushes
        [m] and completes; thread 2 starts pushing [n]; thread 3 snapshots
        {m,n}; thread 4 starts pushing [x]; thread 2 completes; thread 5
        snapshots {m,n,x}; thread 5 removes [n]; thread 3 removes [m].  The
        abstract push-inv of [n] lags until after thread 3's pop of [m]. *)
    Definition f1_state (vm vn vx : A) : @TryStackAuxState A :=
      tsa_remove_node 3%positive (pair 1%positive 0)
        (tsa_remove_node 5%positive (pair 2%positive 0)
          (tsa_start_snapshot 5%positive
            (tsa_finish_push 2%positive
              (tsa_start_push 4%positive 0 vx
                (tsa_start_snapshot 3%positive
                  (tsa_start_push 2%positive 0 vn
                    (tsa_finish_push 1%positive
                      (tsa_start_push 1%positive 0 vm
                        (@empty_try_stack_aux_state A))))))))).

    Definition f1_history : History :=
      {| h_inv := fun nd =>
           if node_eq_dec nd (pair 1%positive 0) then Some (pair 0 0)
           else if node_eq_dec nd (pair 2%positive 0) then Some (pair 3 1)
           else if node_eq_dec nd (pair 4%positive 0) then Some (pair 4 0)
           else None;
         h_pop := fun nd =>
           if node_eq_dec nd (pair 1%positive 0) then Some (pair (pair 3 0) 3%positive)
           else if node_eq_dec nd (pair 2%positive 0) then Some (pair (pair 6 0) 5%positive)
           else None |}.

    Lemma f1_now vm vn vx : tsa_now (f1_state vm vn vx) = 9.
    Proof. reflexivity. Qed.

    Lemma f1_inv_eq vm vn vx :
      tsa_node_inv (f1_state vm vn vx) =
        node_update (pair 4%positive 0) 4
          (node_update (pair 2%positive 0) 2
            (node_update (pair 1%positive 0) 0 empty_node_map)).
    Proof. reflexivity. Qed.

    Lemma f1_ret_eq vm vn vx :
      tsa_node_ret (f1_state vm vn vx) =
        node_update (pair 2%positive 0) 5
          (node_update (pair 1%positive 0) 1 empty_node_map).
    Proof. reflexivity. Qed.

    Lemma f1_rem_eq vm vn vx :
      tsa_removals (f1_state vm vn vx) =
        node_update (pair 1%positive 0) (pair (pair 3%positive 3) 8)
          (node_update (pair 2%positive 0) (pair (pair 5%positive 6) 7) empty_node_map).
    Proof. reflexivity. Qed.

    Ltac f1_lookup_case :=
      repeat first
        [ rewrite node_update_eq
        | rewrite node_update_neq by congruence ];
      unfold empty_node_map.

    Lemma f1_inv vm vn vx nd :
      tsa_node_inv (f1_state vm vn vx) nd =
        if node_eq_dec nd (pair 1%positive 0) then Some 0
        else if node_eq_dec nd (pair 2%positive 0) then Some 2
        else if node_eq_dec nd (pair 4%positive 0) then Some 4 else None.
    Proof.
      rewrite f1_inv_eq.
      destruct (node_eq_dec nd (pair 1%positive 0)) as [->|H1]; [f1_lookup_case; reflexivity|].
      destruct (node_eq_dec nd (pair 2%positive 0)) as [->|H2]; [f1_lookup_case; reflexivity|].
      destruct (node_eq_dec nd (pair 4%positive 0)) as [->|H4]; [f1_lookup_case; reflexivity|].
      f1_lookup_case. reflexivity.
    Qed.

    Lemma f1_ret vm vn vx nd :
      tsa_node_ret (f1_state vm vn vx) nd =
        if node_eq_dec nd (pair 1%positive 0) then Some 1
        else if node_eq_dec nd (pair 2%positive 0) then Some 5 else None.
    Proof.
      rewrite f1_ret_eq.
      destruct (node_eq_dec nd (pair 1%positive 0)) as [->|H1]; [f1_lookup_case; reflexivity|].
      destruct (node_eq_dec nd (pair 2%positive 0)) as [->|H2]; [f1_lookup_case; reflexivity|].
      f1_lookup_case. reflexivity.
    Qed.

    Lemma f1_rem vm vn vx nd :
      tsa_removals (f1_state vm vn vx) nd =
        if node_eq_dec nd (pair 1%positive 0) then Some (pair (pair 3%positive 3) 8)
        else if node_eq_dec nd (pair 2%positive 0) then Some (pair (pair 5%positive 6) 7)
        else None.
    Proof.
      rewrite f1_rem_eq.
      destruct (node_eq_dec nd (pair 1%positive 0)) as [->|H1]; [f1_lookup_case; reflexivity|].
      destruct (node_eq_dec nd (pair 2%positive 0)) as [->|H2]; [f1_lookup_case; reflexivity|].
      f1_lookup_case. reflexivity.
    Qed.

    Lemma f1_snap_eq vm vn vx :
      tsa_snap_time (f1_state vm vn vx) =
        TMap.remove 3%positive (TMap.remove 5%positive
          (TMap.add 5%positive 6 (TMap.add 3%positive 3 (TMap.empty nat)))).
    Proof. reflexivity. Qed.

    Lemma f1_snap vm vn vx a :
      TMap.find a (tsa_snap_time (f1_state vm vn vx)) = None.
    Proof.
      rewrite f1_snap_eq.
      destruct (Pos.eq_dec a 3%positive) as [->|Hne3]; [apply TMap.grs|].
      rewrite TMap.gro by exact Hne3.
      destruct (Pos.eq_dec a 5%positive) as [->|Hne5]; [apply TMap.grs|].
      rewrite TMap.gro by exact Hne5. rewrite TMap.gso by exact Hne5.
      rewrite TMap.gso by exact Hne3. apply TMap.gempty.
    Qed.

    Ltac f1_cases nd :=
      destruct (node_eq_dec nd (pair 1%positive 0)) as [->|];
      [|destruct (node_eq_dec nd (pair 2%positive 0)) as [->|];
        [|destruct (node_eq_dec nd (pair 4%positive 0)) as [->|]]].

    Lemma f1_consistent vm vn vx : consistent (f1_state vm vn vx) f1_history.
    Proof.
      constructor.
      - intros nd p Hp. simpl in Hp. rewrite f1_inv, f1_ret, f1_now.
        f1_cases nd; try discriminate; inversion Hp; subst p;
          (refine (conj _ (conj _ (conj _ _)));
           [unfold pos_ok; simpl; lia|simpl; lia
           |eexists; split; [reflexivity|simpl; lia]
           |intros r Hr; inversion Hr; simpl; lia]).
      - intros nd r Hr. rewrite f1_ret in Hr. simpl. f1_cases nd; try discriminate; eauto.
      - intros nd p a Hp. simpl in Hp. rewrite f1_inv, f1_rem, f1_now.
        f1_cases nd; try discriminate; inversion Hp; subst p a; simpl.
        + refine (conj _ (conj _ (conj _ _))); [unfold pos_ok; simpl; lia|lia| |].
          * exists (pair 0 0). split; [reflexivity|]. unfold pos_lt; simpl. lia.
          * left. exists 3, 8. split; [reflexivity|simpl; lia].
        + refine (conj _ (conj _ (conj _ _))); [unfold pos_ok; simpl; lia|lia| |].
          * exists (pair 3 1). split; [reflexivity|]. unfold pos_lt; simpl. lia.
          * left. exists 6, 7. split; [reflexivity|simpl; lia].
      - intros nd a st rt H. rewrite f1_rem in H. simpl.
        f1_cases nd; try discriminate; inversion H; subst; eauto.
      - intros nd m p q a Hn Hm Hrn Hrm. rewrite f1_rem in Hrn. simpl in Hn.
        f1_cases nd; try discriminate.
      - intros nd p a x q Hp Hx Hlt Hedge. simpl in Hp, Hx.
        destruct Hedge as (p0 & q0 & Hp0 & (r & Hr & Hq0) & Hlt0). simpl in Hp0.
        subst q0. rewrite f1_ret in Hr. exfalso.
        f1_cases nd; try discriminate; inversion Hp; subst p a;
          f1_cases x; try discriminate; inversion Hx; subst q; inversion Hp0; subst p0;
          inversion Hr; subst r; unfold pos_lt, ret_pos in Hlt, Hlt0; simpl in Hlt, Hlt0; lia.
      - intros nd m p Hn Hm. simpl in Hn, Hm.
        f1_cases nd; try discriminate; f1_cases m; try discriminate; try reflexivity;
          inversion Hn; inversion Hm; congruence.
      - intros nd m p a b Hn Hm. simpl in Hn, Hm.
        f1_cases nd; try discriminate; f1_cases m; try discriminate; try reflexivity;
          inversion Hn; inversion Hm; congruence.
      - intros nd m p a Hn Hm. simpl in Hn, Hm.
        f1_cases nd; try discriminate; f1_cases m; try discriminate;
          inversion Hn; inversion Hm; congruence.
    Qed.

  End Sanity.

End TryStackLinearization.
