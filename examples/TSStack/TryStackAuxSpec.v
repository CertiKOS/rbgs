Require Import FMapPositive.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.PArith.PArith.

Require Import models.EffectSignatures.
Require Import examples.Common.Heap.
Require Import examples.Common.ThreadDomain.
Require Import examples.TSStack.ListPoolSpec.
Require Import LinCCAL.
Require Import LTS.
Require Import TPSimulationSet.


(** The auxiliary try-stack specification from Appendix A.3 of the paper.

    This layer has the same graph-shaped abstract data as ListPool, but it
    combines [getTop] and [tryRemove] into one [trypop] operation.  A
    [trypop] may snapshot the current vertices at invocation.  Its response
    either removes a top vertex from that snapshot or reports failure.
    Snapshotting is deliberately permitted even when every vertex is
    garbage, because ListPool may report failure in that state.  The
    separate empty-result branch remains atomic, as required by the paper's
    [trypop-empty] rule. *)
Module TryStackAuxSpec.
  Import LTSSpec.
  Import LinCCALBase.
  Import ListPoolSpec.
  Import TPSimulationSet.TPSimulation.

  Section Spec.
    Context {A : Type}.
    Context (D : ThreadDomain.t).

    Variant TResult : Type :=
    | TSuccNode (v : A) (owner : tid) (loc : Addr)
    | TSuccEmpty
    | TFail.
    Arguments TResult : clear implicits.

    Variant ETryStackAux_op :=
    | tsa_push (v : A)
    | tsa_trypop.
    Arguments ETryStackAux_op : clear implicits.

    Definition ETryStackAux_ar (op : ETryStackAux_op) : Type :=
      match op with
      | tsa_push _ => unit
      | tsa_trypop => TResult
      end.

    Canonical Structure ETryStackAux :=
    {|
      Sig.op := ETryStackAux_op;
      Sig.ar := ETryStackAux_ar
    |}.

    (** The fields correspond to [(V,E,S,P,g)] in Fig. 27.  The state is
        intentionally distinct from [ListPoolState], even though its
        representation is isomorphic; the layer proof relates the two
        copies through its graph invariant. *)
    Record TryStackAuxState : Type := {
      tsa_vertices : LPNodeMap A;
      tsa_edges : LPEdges;
      tsa_snapshots : TMap.t LPNodeSet;
      tsa_pending_pushes : TMap.t Addr;
      tsa_garbage : LPNodeSet;
      (** Ghost timing data.  These fields are deterministic functions of
          the pre-state and the event, never constrain a transition, and
          exist only so that the TryStack layer proof can state a
          state-based invariant about which speculative linearisations
          are still realisable.  [tsa_now] is a logical clock advanced by
          every recorded event; the other fields record at which clock
          value a vertex was created ([tsa_node_inv]) and its push
          completed ([tsa_node_ret]), when each pending snapshot was
          taken ([tsa_snap_time]), and for each removed vertex the
          remover, the remover's snapshot time and the removal time
          ([tsa_removals]). *)
      tsa_now : nat;
      tsa_node_inv : LPNodeMap nat;
      tsa_node_ret : LPNodeMap nat;
      tsa_snap_time : TMap.t nat;
      tsa_removals : LPNodeMap (tid * nat * nat);
    }.

    Definition tsa_is_vertex
        (s : TryStackAuxState) (n : LPNodeId) : Prop :=
      tsa_vertices s n <> None.

    Definition tsa_is_pending
        (s : TryStackAuxState) (n : LPNodeId) : Prop :=
      TMap.find (fst n) (tsa_pending_pushes s) = Some (snd n).

    Definition tsa_is_live
        (s : TryStackAuxState) (n : LPNodeId) : Prop :=
      tsa_is_vertex s n /\ ~ tsa_garbage s n.

    Definition tsa_fresh_node
        (s : TryStackAuxState) (n : LPNodeId) : Prop :=
      tsa_vertices s n = None /\ ~ tsa_garbage s n.

    Definition tsa_all_vertices_garbage
        (s : TryStackAuxState) : Prop :=
      forall n, tsa_is_vertex s n <-> tsa_garbage s n.

    Definition tsa_start_push
        (actor : tid) (loc : Addr) (v : A)
        (s : TryStackAuxState) : TryStackAuxState :=
      let n := (actor, loc) in
      {|
        tsa_vertices := node_update n v (tsa_vertices s);
        tsa_edges :=
          fun n1 n2 =>
            tsa_edges s n1 n2 \/
            (n1 = n /\ tsa_is_vertex s n2 /\ ~ tsa_is_pending s n2);
        tsa_snapshots := tsa_snapshots s;
        tsa_pending_pushes :=
          TMap.add actor loc (tsa_pending_pushes s);
        tsa_garbage := tsa_garbage s;
        tsa_now := S (tsa_now s);
        tsa_node_inv := node_update n (tsa_now s) (tsa_node_inv s);
        tsa_node_ret := tsa_node_ret s;
        tsa_snap_time := tsa_snap_time s;
        tsa_removals := tsa_removals s
      |}.

    Definition tsa_finish_push
        (actor : tid) (s : TryStackAuxState) : TryStackAuxState :=
      {|
        tsa_vertices := tsa_vertices s;
        tsa_edges := tsa_edges s;
        tsa_snapshots := tsa_snapshots s;
        tsa_pending_pushes :=
          TMap.remove actor (tsa_pending_pushes s);
        tsa_garbage := tsa_garbage s;
        tsa_now := S (tsa_now s);
        tsa_node_inv := tsa_node_inv s;
        tsa_node_ret :=
          match TMap.find actor (tsa_pending_pushes s) with
          | Some loc => node_update (actor, loc) (tsa_now s) (tsa_node_ret s)
          | None => tsa_node_ret s
          end;
        tsa_snap_time := tsa_snap_time s;
        tsa_removals := tsa_removals s
      |}.

    Definition tsa_start_snapshot
        (actor : tid) (s : TryStackAuxState) : TryStackAuxState :=
      {|
        tsa_vertices := tsa_vertices s;
        tsa_edges := tsa_edges s;
        tsa_snapshots :=
          TMap.add actor (fun n => tsa_is_vertex s n) (tsa_snapshots s);
        tsa_pending_pushes := tsa_pending_pushes s;
        tsa_garbage := tsa_garbage s;
        tsa_now := S (tsa_now s);
        tsa_node_inv := tsa_node_inv s;
        tsa_node_ret := tsa_node_ret s;
        tsa_snap_time := TMap.add actor (tsa_now s) (tsa_snap_time s);
        tsa_removals := tsa_removals s
      |}.

    Definition tsa_clear_snapshot
        (actor : tid) (s : TryStackAuxState) : TryStackAuxState :=
      {|
        tsa_vertices := tsa_vertices s;
        tsa_edges := tsa_edges s;
        tsa_snapshots := TMap.remove actor (tsa_snapshots s);
        tsa_pending_pushes := tsa_pending_pushes s;
        tsa_garbage := tsa_garbage s;
        tsa_now := S (tsa_now s);
        tsa_node_inv := tsa_node_inv s;
        tsa_node_ret := tsa_node_ret s;
        tsa_snap_time := TMap.remove actor (tsa_snap_time s);
        tsa_removals := tsa_removals s
      |}.

    (** A successful [trypop] is one recorded event: the snapshot is
        cleared, the node becomes garbage, and the removal is logged with
        the remover's snapshot time. *)
    Definition tsa_remove_node
        (actor : tid) (n : LPNodeId) (s : TryStackAuxState) :
        TryStackAuxState :=
      {|
        tsa_vertices := tsa_vertices s;
        tsa_edges := tsa_edges s;
        tsa_snapshots := TMap.remove actor (tsa_snapshots s);
        tsa_pending_pushes := tsa_pending_pushes s;
        tsa_garbage := set_add n (tsa_garbage s);
        tsa_now := S (tsa_now s);
        tsa_node_inv := tsa_node_inv s;
        tsa_node_ret := tsa_node_ret s;
        tsa_snap_time := TMap.remove actor (tsa_snap_time s);
        tsa_removals :=
          match TMap.find actor (tsa_snap_time s) with
          | Some st => node_update n (actor, st, tsa_now s) (tsa_removals s)
          | None => tsa_removals s
          end
      |}.

    Definition empty_try_stack_aux_state : TryStackAuxState :=
      {|
        tsa_vertices := empty_node_map;
        tsa_edges := empty_edges;
        tsa_snapshots := TMap.empty LPNodeSet;
        tsa_pending_pushes := TMap.empty Addr;
        tsa_garbage := empty_node_set;
        tsa_now := 0;
        tsa_node_inv := empty_node_map;
        tsa_node_ret := empty_node_map;
        tsa_snap_time := TMap.empty nat;
        tsa_removals := empty_node_map
      |}.

    (** Empty [trypop] is represented by two adjacent observable events.
        [TSAAtomicPending] prevents an abstract operation from interleaving
        between them.  A snapshot/failure [trypop] remains
        interval-sequential and therefore stays in [TSAReady] while its
        snapshot is pending. *)
    Variant TryStackAuxControl : Type :=
    | TSAReady (s : TryStackAuxState)
    | TSAAtomicPending
        (s : TryStackAuxState)
        (actor : tid)
        (op : ETryStackAux_op).

    Variant StepTryStackAux :
      @ThreadEvent ETryStackAux ->
      TryStackAuxControl ->
      TryStackAuxControl ->
      Prop :=

    (** Push is lifted unchanged from ListPool. *)
    | step_tsa_push_inv actor s v loc e :
        TMap.find actor (tsa_pending_pushes s) = None ->
        tsa_fresh_node s (actor, loc) ->
        e = {| te_tid := actor; te_ev := InvEv (tsa_push v) |} ->
        StepTryStackAux e
          (TSAReady s)
          (TSAReady (tsa_start_push actor loc v s))
    | step_tsa_push_res actor s v loc e :
        TMap.find actor (tsa_pending_pushes s) = Some loc ->
        e = {| te_tid := actor;
               te_ev := ResEv (tsa_push v) tt |} ->
        StepTryStackAux e
          (TSAReady s)
          (TSAReady (tsa_finish_push actor s))

    (** Empty [trypop] linearizes atomically at invocation. *)
    | step_tsa_trypop_empty_inv actor s e :
        TMap.find actor (tsa_snapshots s) = None ->
        tsa_all_vertices_garbage s ->
        e = {| te_tid := actor; te_ev := InvEv tsa_trypop |} ->
        StepTryStackAux e
          (TSAReady s)
          (TSAAtomicPending s actor tsa_trypop)
    | step_tsa_trypop_empty_res actor s e :
        e = {| te_tid := actor;
               te_ev := ResEv tsa_trypop TSuccEmpty |} ->
        StepTryStackAux e
          (TSAAtomicPending s actor tsa_trypop)
          (TSAReady s)

    (** The snapshot branch records [dom(V)].  It intentionally overlaps
        the empty branch: when all vertices are garbage, choosing the empty
        branch commits to [TSuccEmpty], while choosing this branch permits
        the underlay's [YFail] result and commits to [TFail].  A successful
        node response is then impossible because the saved live set is
        empty. *)
    | step_tsa_trypop_snapshot_inv actor s e :
        TMap.find actor (tsa_snapshots s) = None ->
        e = {| te_tid := actor; te_ev := InvEv tsa_trypop |} ->
        StepTryStackAux e
          (TSAReady s)
          (TSAReady (tsa_start_snapshot actor s))

    (** A successful response removes a top member of the saved live set.
        The owner/address pair is retained in the result for the next layer. *)
    | step_tsa_trypop_succ actor s N n v e :
        TMap.find actor (tsa_snapshots s) = Some N ->
        lp_top
          (fun n' => N n' /\ ~ tsa_garbage s n')
          (tsa_edges s) n ->
        tsa_vertices s n = Some v ->
        e = {| te_tid := actor;
               te_ev := ResEv tsa_trypop
                 (TSuccNode v (fst n) (snd n)) |} ->
        StepTryStackAux e
          (TSAReady s)
          (TSAReady (tsa_remove_node actor n s))
    | step_tsa_trypop_fail actor s N e :
        TMap.find actor (tsa_snapshots s) = Some N ->
        e = {| te_tid := actor;
               te_ev := ResEv tsa_trypop TFail |} ->
        StepTryStackAux e
          (TSAReady s)
          (TSAReady (tsa_clear_snapshot actor s)).

    Variant ErrorTryStackAux :
      @ThreadEvent ETryStackAux -> TryStackAuxControl -> Prop :=
    | error_tsa_actor_outside actor op s e :
        ~ ThreadDomain.contains D actor ->
        e = {| te_tid := actor; te_ev := InvEv op |} ->
        ErrorTryStackAux e (TSAReady s).

    Definition VTryStackAux : @LTS ETryStackAux :=
      {|
        State := TryStackAuxControl;
        Step := StepTryStackAux;
        Error := ErrorTryStackAux
      |}.

    Lemma empty_tsa_state_has_no_vertex n :
      ~ tsa_is_vertex empty_try_stack_aux_state n.
    Proof.
      unfold tsa_is_vertex, empty_try_stack_aux_state, empty_node_map; simpl.
      intro Hneq. apply Hneq. reflexivity.
    Qed.

    Lemma empty_tsa_state_all_vertices_garbage :
      tsa_all_vertices_garbage empty_try_stack_aux_state.
    Proof.
      intro n. split.
      - intro H. exfalso. now apply (empty_tsa_state_has_no_vertex n).
      - simpl. contradiction.
    Qed.

  End Spec.

  Module TryStackAuxLayer.
    Section Layer.
      Context {A : Type}.
      Context (D : ThreadDomain.t).

      Definition L : layer_interface :=
      {|
        li_sig := @ETryStackAux A;
        li_lts := @VTryStackAux A D;
        li_init := TSAReady (@empty_try_stack_aux_state A)
      |}.
    End Layer.
  End TryStackAuxLayer.

End TryStackAuxSpec.
