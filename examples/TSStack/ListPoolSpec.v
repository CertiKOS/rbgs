Require Import FMapPositive.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.PArith.PArith.
Require Import Coq.Program.Equality.

Require Import models.EffectSignatures.
Require Import examples.Common.Heap.
Require Import examples.Common.ThreadDomain.
Require Import LinCCAL.
Require Import LTS.
Require Import TPSimulationSet.


(** The interval-sequential DAG specification of the List Pool from
    Appendix A.2 of the paper. *)
Module ListPoolSpec.
  Import LTSSpec.
  Import LinCCALBase.
  Import TPSimulationSet.TPSimulation.

  Definition LPNodeId : Type := (tid * Addr)%type.
  Definition LPNodeSet : Type := LPNodeId -> Prop.
  Definition LPEdges : Type := LPNodeId -> LPNodeId -> Prop.
  Definition LPNodeMap (A : Type) : Type := LPNodeId -> option A.

  Definition node_eq_dec (x y : LPNodeId) : {x = y} + {x <> y}.
  Proof.
    decide equality.
    - apply Nat.eq_dec.
    - apply Pos.eq_dec.
  Defined.

  Definition node_update {A}
      (n : LPNodeId) (v : A) (V : LPNodeMap A) : LPNodeMap A :=
    fun n' => if node_eq_dec n n' then Some v else V n'.

  Definition set_add (n : LPNodeId) (N : LPNodeSet) : LPNodeSet :=
    fun n' => n' = n \/ N n'.

  Definition empty_node_map {A} : LPNodeMap A := fun _ => None.
  Definition empty_node_set : LPNodeSet := fun _ => False.
  Definition empty_edges : LPEdges := fun _ _ => False.

  Section Spec.
    Context {A : Type}.
    Context (D : ThreadDomain.t).

    (** A successful nonempty result contains the value as well as the
        owning SPList and the address local to that SPList. *)
    Variant YResult : Type :=
    | YSuccNode (v : A) (owner : tid) (loc : Addr)
    | YSuccEmpty
    | YFail.
    Arguments YResult : clear implicits.

    Variant EListPool_op :=
    | lpool_push (v : A)
    | lpool_getTop
    | lpool_tryRemove (owner : tid) (loc : Addr).
    Arguments EListPool_op : clear implicits.

    Definition EListPool_ar (op : EListPool_op) : Type :=
      match op with
      | lpool_push _ => unit
      | lpool_getTop => YResult
      | lpool_tryRemove _ _ => bool
      end.

    Canonical Structure EListPool :=
    {|
      Sig.op := EListPool_op;
      Sig.ar := EListPool_ar
    |}.

    (** [lp_vertices] contains removed vertices as well as live ones.
        Edges point from a newer/higher node to an older/lower node. *)
    Record ListPoolState : Type := {
      lp_vertices : LPNodeMap A;
      lp_edges : LPEdges;
      lp_snapshots : TMap.t LPNodeSet;
      lp_pending_pushes : TMap.t Addr;
      lp_garbage : LPNodeSet;
    }.

    Definition is_vertex (s : ListPoolState) (n : LPNodeId) : Prop :=
      lp_vertices s n <> None.

    Definition is_pending (s : ListPoolState) (n : LPNodeId) : Prop :=
      TMap.find (fst n) (lp_pending_pushes s) = Some (snd n).

    Definition is_live (s : ListPoolState) (n : LPNodeId) : Prop :=
      is_vertex s n /\ ~ lp_garbage s n.

    Definition fresh_node (s : ListPoolState) (n : LPNodeId) : Prop :=
      lp_vertices s n = None /\ ~ lp_garbage s n.

    (** Since edges point from higher nodes to lower nodes, a top node has
        no incoming edge from another member of the candidate set. *)
    Definition lp_top (N : LPNodeSet) (E : LPEdges) (n : LPNodeId) : Prop :=
      N n /\ forall n', N n' -> ~ E n' n.

    Definition lp_closed (N : LPNodeSet) (E : LPEdges) : Prop :=
      forall n n', N n -> E n n' -> N n'.

    Definition all_vertices_garbage (s : ListPoolState) : Prop :=
      forall n, is_vertex s n <-> lp_garbage s n.

    Definition start_push
        (actor : tid) (loc : Addr) (v : A)
        (s : ListPoolState) : ListPoolState :=
      let n := (actor, loc) in
      {|
        lp_vertices := node_update n v (lp_vertices s);
        lp_edges :=
          fun n1 n2 =>
            lp_edges s n1 n2 \/
            (n1 = n /\ is_vertex s n2 /\ ~ is_pending s n2);
        lp_snapshots := lp_snapshots s;
        lp_pending_pushes :=
          TMap.add actor loc (lp_pending_pushes s);
        lp_garbage := lp_garbage s
      |}.

    Definition finish_push
        (actor : tid) (s : ListPoolState) : ListPoolState :=
      {|
        lp_vertices := lp_vertices s;
        lp_edges := lp_edges s;
        lp_snapshots := lp_snapshots s;
        lp_pending_pushes := TMap.remove actor (lp_pending_pushes s);
        lp_garbage := lp_garbage s
      |}.

    Definition start_snapshot
        (actor : tid) (s : ListPoolState) : ListPoolState :=
      {|
        lp_vertices := lp_vertices s;
        lp_edges := lp_edges s;
        lp_snapshots :=
          TMap.add actor (fun n => is_vertex s n) (lp_snapshots s);
        lp_pending_pushes := lp_pending_pushes s;
        lp_garbage := lp_garbage s
      |}.

    Definition clear_snapshot
        (actor : tid) (s : ListPoolState) : ListPoolState :=
      {|
        lp_vertices := lp_vertices s;
        lp_edges := lp_edges s;
        lp_snapshots := TMap.remove actor (lp_snapshots s);
        lp_pending_pushes := lp_pending_pushes s;
        lp_garbage := lp_garbage s
      |}.

    Definition mark_garbage
        (n : LPNodeId) (s : ListPoolState) : ListPoolState :=
      {|
        lp_vertices := lp_vertices s;
        lp_edges := lp_edges s;
        lp_snapshots := lp_snapshots s;
        lp_pending_pushes := lp_pending_pushes s;
        lp_garbage := set_add n (lp_garbage s)
      |}.

    Definition empty_list_pool_state : ListPoolState :=
      {|
        lp_vertices := empty_node_map;
        lp_edges := empty_edges;
        lp_snapshots := TMap.empty LPNodeSet;
        lp_pending_pushes := TMap.empty Addr;
        lp_garbage := empty_node_set
      |}.

    (** Atomic operations use the same control-state convention as the
        SPList specification.  Interval-sequential push and getTop steps
        remain in [LPReady], so operations from other threads may interleave. *)
    Variant ListPoolControl : Type :=
    | LPReady (s : ListPoolState)
    | LPAtomicPending
        (s : ListPoolState)
        (actor : tid)
        (op : EListPool_op).

    Variant StepListPool :
      @ThreadEvent EListPool ->
      ListPoolControl ->
      ListPoolControl ->
      Prop :=

    (** Interval-sequential push.  A new push is ordered above every
        already-defined vertex whose push has completed, including removed
        vertices, but not above overlapping pushes.  This is the
        garbage-independent edge rule from Fig. 19 of the paper. *)
    | step_push_inv actor s v loc e :
        TMap.find actor (lp_pending_pushes s) = None ->
        fresh_node s (actor, loc) ->
        e = {| te_tid := actor; te_ev := InvEv (lpool_push v) |} ->
        StepListPool e
          (LPReady s)
          (LPReady (start_push actor loc v s))
    | step_push_res actor s v loc e :
        TMap.find actor (lp_pending_pushes s) = Some loc ->
        e = {| te_tid := actor;
               te_ev := ResEv (lpool_push v) tt |} ->
        StepListPool e
          (LPReady s)
          (LPReady (finish_push actor s))

    (** The interval-sequential getTop path saves the current vertex set.
        Later pushes cannot change that saved set. *)
    | step_getTop_snapshot_inv actor s e :
        TMap.find actor (lp_snapshots s) = None ->
        e = {| te_tid := actor; te_ev := InvEv lpool_getTop |} ->
        StepListPool e
          (LPReady s)
          (LPReady (start_snapshot actor s))
    | step_getTop_top_res actor s N n v e :
        TMap.find actor (lp_snapshots s) = Some N ->
        lp_top
          (fun n' => N n' /\ ~ lp_garbage s n')
          (lp_edges s) n ->
        lp_vertices s n = Some v ->
        e = {| te_tid := actor;
               te_ev := ResEv lpool_getTop
                 (YSuccNode v (fst n) (snd n)) |} ->
        StepListPool e
          (LPReady s)
          (LPReady (clear_snapshot actor s))
    | step_getTop_garbage_res actor s N n v e :
        TMap.find actor (lp_snapshots s) = Some N ->
        lp_garbage s n ->
        lp_vertices s n = Some v ->
        e = {| te_tid := actor;
               te_ev := ResEv lpool_getTop
                 (YSuccNode v (fst n) (snd n)) |} ->
        StepListPool e
          (LPReady s)
          (LPReady (clear_snapshot actor s))

    (** Fail and empty are the atomic alternatives for getTop.  The single
        invocation rule is observationally equivalent to the two atomic
        rules in the paper; the response guard selects the result. *)
    | step_getTop_atomic_inv actor s e :
        e = {| te_tid := actor; te_ev := InvEv lpool_getTop |} ->
        StepListPool e
          (LPReady s)
          (LPAtomicPending s actor lpool_getTop)
    | step_getTop_fail_res actor s e :
        e = {| te_tid := actor;
               te_ev := ResEv lpool_getTop YFail |} ->
        StepListPool e
          (LPAtomicPending s actor lpool_getTop)
          (LPReady s)
    | step_getTop_empty_res actor s e :
        all_vertices_garbage s ->
        e = {| te_tid := actor;
               te_ev := ResEv lpool_getTop YSuccEmpty |} ->
        StepListPool e
          (LPAtomicPending s actor lpool_getTop)
          (LPReady s)

    (** tryRemove is atomic.  Successful and failed removal are deliberately
        disjoint: a live node succeeds and an already removed node fails. *)
    | step_tryRemove_inv actor owner loc s e :
        is_vertex s (owner, loc) \/ lp_garbage s (owner, loc) ->
        e = {| te_tid := actor;
               te_ev := InvEv (lpool_tryRemove owner loc) |} ->
        StepListPool e
          (LPReady s)
          (LPAtomicPending s actor (lpool_tryRemove owner loc))
    | step_tryRemove_succ actor owner loc s e :
        is_live s (owner, loc) ->
        e = {| te_tid := actor;
               te_ev := ResEv (lpool_tryRemove owner loc) true |} ->
        StepListPool e
          (LPAtomicPending s actor (lpool_tryRemove owner loc))
          (LPReady (mark_garbage (owner, loc) s))
    | step_tryRemove_fail actor owner loc s e :
        lp_garbage s (owner, loc) ->
        e = {| te_tid := actor;
               te_ev := ResEv (lpool_tryRemove owner loc) false |} ->
        StepListPool e
          (LPAtomicPending s actor (lpool_tryRemove owner loc))
          (LPReady s).

    Variant ErrorListPool :
      @ThreadEvent EListPool -> ListPoolControl -> Prop :=
    | error_actor_outside actor op s e :
        ~ ThreadDomain.contains D actor ->
        e = {| te_tid := actor; te_ev := InvEv op |} ->
        ErrorListPool e (LPReady s)
    | error_tryRemove_owner_outside actor owner loc s e :
        ~ ThreadDomain.contains D owner ->
        e = {| te_tid := actor;
               te_ev := InvEv (lpool_tryRemove owner loc) |} ->
        ErrorListPool e (LPReady s)
    | error_tryRemove_undefined actor owner loc s e :
        ~ is_vertex s (owner, loc) ->
        e = {| te_tid := actor;
               te_ev := InvEv (lpool_tryRemove owner loc) |} ->
        ErrorListPool e (LPReady s).

    Definition VListPool : @LTS EListPool :=
      {|
        State := ListPoolControl;
        Step := StepListPool;
        Error := ErrorListPool
      |}.

    (** Basic facts used by the later representation invariant. *)
    Lemma node_update_eq (n : LPNodeId) (v : A) (V : LPNodeMap A) :
      node_update n v V n = Some v.
    Proof.
      unfold node_update.
      destruct (node_eq_dec n n); congruence.
    Qed.

    Lemma node_update_neq
        (n n' : LPNodeId) (v : A) (V : LPNodeMap A) :
      n <> n' -> node_update n v V n' = V n'.
    Proof.
      intros Hneq. unfold node_update.
      destruct (node_eq_dec n n'); congruence.
    Qed.

    Lemma empty_state_has_no_vertex n :
      ~ is_vertex empty_list_pool_state n.
    Proof.
      unfold is_vertex, empty_list_pool_state, empty_node_map; simpl.
      intro Hneq. apply Hneq. reflexivity.
    Qed.

    Lemma empty_state_all_vertices_garbage :
      all_vertices_garbage empty_list_pool_state.
    Proof.
      intro n. split.
      - intro H. exfalso. now apply (empty_state_has_no_vertex n).
      - simpl. contradiction.
    Qed.

  End Spec.

  Module ListPoolLayer.
    Section Layer.
      Context {A : Type}.
      Context (D : ThreadDomain.t).

      Definition L : layer_interface :=
      {|
        li_sig := @EListPool A;
        li_lts := @VListPool A D;
        li_init := LPReady (@empty_list_pool_state A)
      |}.
    End Layer.
  End ListPoolLayer.

End ListPoolSpec.
