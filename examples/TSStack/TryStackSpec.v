Require Import FMapPositive.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.PArith.PArith.

Require Import models.EffectSignatures.
Require Import examples.Common.Heap.
Require Import examples.Common.ThreadDomain.
Require Import examples.TSStack.ListPoolSpec.
Require Import examples.TSStack.TryStackAuxSpec.
Require Import LinCCAL.
Require Import LTS.
Require Import TPSimulationSet.


(** The atomic try-stack specification from Appendix A.4 of the paper.

    As in the ListPool and TryStackAux specifications, the abstract stack is
    represented by a DAG.  Push remains interval sequential: concurrent
    pushes need not be ordered by an edge.  Try-pop, however, is atomic and
    may remove any top live vertex, report the graph empty when every vertex
    has been removed, or fail without changing the graph. *)
Module TryStackSpec.
  Import LTSSpec.
  Import LinCCALBase.
  Import ListPoolSpec.
  Import TryStackAuxSpec.
  Import TPSimulationSet.TPSimulation.

  Section Spec.
    Context {A : Type}.
    Context (D : ThreadDomain.t).

    Variant ETryStack_op :=
    | ts_push (v : A)
    | ts_trypop.
    Arguments ETryStack_op : clear implicits.

    Definition ETryStack_ar (op : ETryStack_op) : Type :=
      match op with
      | ts_push _ => unit
      | ts_trypop => @TResult A
      end.

    Canonical Structure ETryStack :=
    {|
      Sig.op := ETryStack_op;
      Sig.ar := ETryStack_ar
    |}.

    (** The fields correspond to [(V,E,P,g)] in Fig. 30.  Removed vertices
        remain in [ts_vertices]; [ts_garbage] distinguishes them from the
        live vertices that may be popped. *)
    Record TryStackState : Type := {
      ts_vertices : LPNodeMap A;
      ts_edges : LPEdges;
      ts_pending_pushes : TMap.t Addr;
      ts_garbage : LPNodeSet;
    }.

    Definition ts_is_vertex
        (s : TryStackState) (n : LPNodeId) : Prop :=
      ts_vertices s n <> None.

    Definition ts_is_pending
        (s : TryStackState) (n : LPNodeId) : Prop :=
      TMap.find (fst n) (ts_pending_pushes s) = Some (snd n).

    Definition ts_is_live
        (s : TryStackState) (n : LPNodeId) : Prop :=
      ts_is_vertex s n /\ ~ ts_garbage s n.

    Definition ts_fresh_node
        (s : TryStackState) (n : LPNodeId) : Prop :=
      ts_vertices s n = None /\ ~ ts_garbage s n.

    Definition ts_all_vertices_garbage
        (s : TryStackState) : Prop :=
      forall n, ts_is_vertex s n <-> ts_garbage s n.

    Definition ts_start_push
        (actor : tid) (loc : Addr) (v : A)
        (s : TryStackState) : TryStackState :=
      let n := (actor, loc) in
      {|
        ts_vertices := node_update n v (ts_vertices s);
        ts_edges :=
          fun n1 n2 =>
            ts_edges s n1 n2 \/
            (n1 = n /\ ts_is_vertex s n2 /\ ~ ts_is_pending s n2);
        ts_pending_pushes :=
          TMap.add actor loc (ts_pending_pushes s);
        ts_garbage := ts_garbage s
      |}.

    Definition ts_finish_push
        (actor : tid) (s : TryStackState) : TryStackState :=
      {|
        ts_vertices := ts_vertices s;
        ts_edges := ts_edges s;
        ts_pending_pushes := TMap.remove actor (ts_pending_pushes s);
        ts_garbage := ts_garbage s
      |}.

    Definition ts_mark_garbage
        (n : LPNodeId) (s : TryStackState) : TryStackState :=
      {|
        ts_vertices := ts_vertices s;
        ts_edges := ts_edges s;
        ts_pending_pushes := ts_pending_pushes s;
        ts_garbage := set_add n (ts_garbage s)
      |}.

    Definition empty_try_stack_state : TryStackState :=
      {|
        ts_vertices := empty_node_map;
        ts_edges := empty_edges;
        ts_pending_pushes := TMap.empty Addr;
        ts_garbage := empty_node_set
      |}.

    (** A control state represents each atomic try-pop by two adjacent
        observable events.  The saved state cannot be modified between its
        invocation and response.  Push stays in [TSReady], permitting the
        interval overlap required by the specification. *)
    Variant TryStackControl : Type :=
    | TSReady (s : TryStackState)
    | TSAtomicPending
        (s : TryStackState)
        (actor : tid)
        (op : ETryStack_op).

    Variant StepTryStack :
      @ThreadEvent ETryStack ->
      TryStackControl ->
      TryStackControl ->
      Prop :=

    | step_ts_push_inv actor s v loc e :
        TMap.find actor (ts_pending_pushes s) = None ->
        ts_fresh_node s (actor, loc) ->
        e = {| te_tid := actor; te_ev := InvEv (ts_push v) |} ->
        StepTryStack e
          (TSReady s)
          (TSReady (ts_start_push actor loc v s))
    | step_ts_push_res actor s v loc e :
        TMap.find actor (ts_pending_pushes s) = Some loc ->
        e = {| te_tid := actor;
               te_ev := ResEv (ts_push v) tt |} ->
        StepTryStack e
          (TSReady s)
          (TSReady (ts_finish_push actor s))

    | step_ts_trypop_inv actor s e :
        e = {| te_tid := actor; te_ev := InvEv ts_trypop |} ->
        StepTryStack e
          (TSReady s)
          (TSAtomicPending s actor ts_trypop)
    | step_ts_trypop_succ actor s n v e :
        lp_top (fun n' => ts_is_live s n') (ts_edges s) n ->
        ts_vertices s n = Some v ->
        e = {| te_tid := actor;
               te_ev := ResEv ts_trypop
                 (TSuccNode v (fst n) (snd n)) |} ->
        StepTryStack e
          (TSAtomicPending s actor ts_trypop)
          (TSReady (ts_mark_garbage n s))
    | step_ts_trypop_empty actor s e :
        ts_all_vertices_garbage s ->
        e = {| te_tid := actor;
               te_ev := ResEv ts_trypop TSuccEmpty |} ->
        StepTryStack e
          (TSAtomicPending s actor ts_trypop)
          (TSReady s)
    | step_ts_trypop_fail actor s e :
        e = {| te_tid := actor;
               te_ev := ResEv ts_trypop TFail |} ->
        StepTryStack e
          (TSAtomicPending s actor ts_trypop)
          (TSReady s).

    Variant ErrorTryStack :
      @ThreadEvent ETryStack -> TryStackControl -> Prop :=
    | error_ts_actor_outside actor op s e :
        ~ ThreadDomain.contains D actor ->
        e = {| te_tid := actor; te_ev := InvEv op |} ->
        ErrorTryStack e (TSReady s).

    Definition VTryStack : @LTS ETryStack :=
      {|
        State := TryStackControl;
        Step := StepTryStack;
        Error := ErrorTryStack
      |}.

    Lemma empty_ts_state_has_no_vertex n :
      ~ ts_is_vertex empty_try_stack_state n.
    Proof.
      unfold ts_is_vertex, empty_try_stack_state, empty_node_map; simpl.
      intro Hneq. apply Hneq. reflexivity.
    Qed.

    Lemma empty_ts_state_all_vertices_garbage :
      ts_all_vertices_garbage empty_try_stack_state.
    Proof.
      intro n. split.
      - intro H. exfalso. now apply (empty_ts_state_has_no_vertex n).
      - simpl. contradiction.
    Qed.

  End Spec.

  Module TryStackLayer.
    Section Layer.
      Context {A : Type}.
      Context (D : ThreadDomain.t).

      Definition L : layer_interface :=
      {|
        li_sig := @ETryStack A;
        li_lts := @VTryStack A D;
        li_init := TSReady (@empty_try_stack_state A)
      |}.
    End Layer.
  End TryStackLayer.

End TryStackSpec.
