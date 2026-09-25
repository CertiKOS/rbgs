Require Import FMapPositive.
Require Import Relation_Operators Operators_Properties.
Require Import Coq.PArith.PArith.
Require Import Coq.Program.Equality.
Require Import PeanoNat.

Require Import coqrel.LogicalRelations.
Require Import models.EffectSignatures.
Require Import examples.Common.Heap.
Require Import examples.Common.AtomicLTS.
Require Import LinCCAL.
Require Import LTS.
Require Import TPSimulationSet.


(** A heap of initialised cells that remembers which thread allocated each
    cell.

    [omalloc v] returns a fresh address holding [v]; [oread], [owrite] and
    [ocas] are the usual load, plain store and compare-and-swap.  The store
    is racy exactly as in [MemSpec.WriteRacyMem]: a store invoked while
    another thread's store to the same address is pending is an error.

    The owner map [om_owner] is ghost state: it never influences a step or
    an error, so the observable behaviour is that of a plain memory.  It
    exists so that a client proof can tell a cell it has just allocated from
    the cells other threads are allocating at the same time; [PlainMem] is
    the same memory without it, and [OwnerMemProof] shows the ghost layer
    linearizable from it.  Without the owner, such cells are
    indistinguishable in the proof state, and no rely/guarantee can prevent
    another thread from claiming or racing on a fresh cell (compare
    [OwnedMemSpec], which records the allocator until the first store). *)
Module OwnerMemSpec.
  Import LTSSpec.
  Import LinCCALBase.
  Import AtomicLTS.
  Import TPSimulationSet.TPSimulation.

  Variant EOMem_op {A} :=
  | omalloc (v : A)
  | oread (addr : Addr)
  | owrite (addr : Addr) (v : A)
  | ocas (addr : Addr) (v w : A).
  Arguments EOMem_op : clear implicits.

  Definition EOMem_ar {A} (m : EOMem_op A) : Type :=
    match m with
    | omalloc _ => Addr
    | oread _ => A
    | owrite _ _ => unit
    | ocas _ _ _ => bool
    end.

  Canonical Structure EOMem A :=
  {|
    Sig.op := EOMem_op A;
    Sig.ar := EOMem_ar
  |}.

  Module OwnerMem.
    Record OMemState {A} := {
      om_heap : @Heap A;
      om_owner : @Heap tid;
    }.
    Arguments OMemState : clear implicits.
    Arguments om_heap {A} _.
    Arguments om_owner {A} _.

    Definition empty_omem {A} : OMemState A :=
      {| om_heap := empty_heap; om_owner := empty_heap |}.

    Definition om_alloc {A} (t : tid) (l : Addr) (v : A) (s : OMemState A) :=
      {| om_heap := heap_update l v (om_heap s);
         om_owner := heap_update l t (om_owner s) |}.

    Definition om_write {A} (l : Addr) (v : A) (s : OMemState A) :=
      {| om_heap := heap_update l v (om_heap s);
         om_owner := om_owner s |}.

    Variant StepOMem {A} :
      @ThreadEvent (EOMem A) -> OMemState A -> OMemState A -> Prop :=
    (* alloc steps *)
    | step_alloc_inv t s v e :
      e = {| te_tid := t; te_ev := InvEv (omalloc v) |} ->
      StepOMem e s s
    | step_alloc_res t s l v e :
      e = {| te_tid := t; te_ev := ResEv (omalloc v) l |} ->
      om_heap s l = None ->
      StepOMem e s (om_alloc t l v s)
    (* read steps *)
    | step_read_inv t s l e :
      e = {| te_tid := t; te_ev := InvEv (oread l) |} ->
      om_heap s l <> None ->
      StepOMem e s s
    | step_read_res t s l v e :
      e = {| te_tid := t; te_ev := ResEv (oread l) v |} ->
      om_heap s l = Some v ->
      StepOMem e s s
    (* write steps *)
    | step_write_inv t s l v e :
      e = {| te_tid := t; te_ev := InvEv (owrite l v) |} ->
      om_heap s l <> None ->
      StepOMem e s s
    | step_write_res t s l v e :
      e = {| te_tid := t; te_ev := ResEv (owrite l v) tt |} ->
      om_heap s l <> None ->
      StepOMem e s (om_write l v s)
    (* cas steps *)
    | step_cas_inv t s l v w e :
      e = {| te_tid := t; te_ev := InvEv (ocas l v w) |} ->
      om_heap s l <> None ->
      StepOMem e s s
    | step_cas_res_succ t s l v w e :
      e = {| te_tid := t; te_ev := ResEv (ocas l v w) true |} ->
      om_heap s l = Some v ->
      StepOMem e s (om_write l w s)
    | step_cas_res_fail t s l u v w e :
      e = {| te_tid := t; te_ev := ResEv (ocas l v w) false |} ->
      om_heap s l = Some u ->
      u <> v ->
      StepOMem e s s.

    Variant ErrorOMem {A} :
      @ThreadEvent (EOMem A) -> (@AState (EOMem A) (OMemState A)) -> Prop :=
    | error_read_undefined t s l e :
      e = {| te_tid := t; te_ev := InvEv (oread l) |} ->
      om_heap s l = None ->
      ErrorOMem e (Idle s)
    | error_write_undefined t s l v e :
      e = {| te_tid := t; te_ev := InvEv (owrite l v) |} ->
      om_heap s l = None ->
      ErrorOMem e (Idle s)
    | error_cas_undefined t s l v w e :
      e = {| te_tid := t; te_ev := InvEv (ocas l v w) |} ->
      om_heap s l = None ->
      ErrorOMem e (Idle s)
    | error_write_racy t t' s l l' v v' e :
      t <> t' ->
      l = l' ->
      e = {| te_tid := t; te_ev := InvEv (owrite l v) |} ->
      ErrorOMem e (Pending s t' (owrite l' v')).

    Definition VOMem {A} : @LTS (EOMem A) := VAE StepOMem ErrorOMem.
  End OwnerMem.

  (** The concrete memory: the same operations with the owner map removed.
      [OwnerMemProof.MOwnerMem] shows [OwnerMem] linearizable from it with
      the identity implementation. *)
  Module PlainMem.
    Variant StepPlain {A} :
      @ThreadEvent (EOMem A) -> @Heap A -> @Heap A -> Prop :=
    | pstep_alloc_inv t h v e :
      e = {| te_tid := t; te_ev := InvEv (omalloc v) |} ->
      StepPlain e h h
    | pstep_alloc_res t h l v e :
      e = {| te_tid := t; te_ev := ResEv (omalloc v) l |} ->
      h l = None ->
      StepPlain e h (heap_update l v h)
    | pstep_read_inv t h l e :
      e = {| te_tid := t; te_ev := InvEv (oread l) |} ->
      h l <> None ->
      StepPlain e h h
    | pstep_read_res t h l v e :
      e = {| te_tid := t; te_ev := ResEv (oread l) v |} ->
      h l = Some v ->
      StepPlain e h h
    | pstep_write_inv t h l v e :
      e = {| te_tid := t; te_ev := InvEv (owrite l v) |} ->
      h l <> None ->
      StepPlain e h h
    | pstep_write_res t h l v e :
      e = {| te_tid := t; te_ev := ResEv (owrite l v) tt |} ->
      h l <> None ->
      StepPlain e h (heap_update l v h)
    | pstep_cas_inv t h l v w e :
      e = {| te_tid := t; te_ev := InvEv (ocas l v w) |} ->
      h l <> None ->
      StepPlain e h h
    | pstep_cas_res_succ t h l v w e :
      e = {| te_tid := t; te_ev := ResEv (ocas l v w) true |} ->
      h l = Some v ->
      StepPlain e h (heap_update l w h)
    | pstep_cas_res_fail t h l u v w e :
      e = {| te_tid := t; te_ev := ResEv (ocas l v w) false |} ->
      h l = Some u ->
      u <> v ->
      StepPlain e h h.

    Variant ErrorPlain {A} :
      @ThreadEvent (EOMem A) -> (@AState (EOMem A) (@Heap A)) -> Prop :=
    | perror_read_undefined t h l e :
      e = {| te_tid := t; te_ev := InvEv (oread l) |} ->
      h l = None ->
      ErrorPlain e (Idle h)
    | perror_write_undefined t h l v e :
      e = {| te_tid := t; te_ev := InvEv (owrite l v) |} ->
      h l = None ->
      ErrorPlain e (Idle h)
    | perror_cas_undefined t h l v w e :
      e = {| te_tid := t; te_ev := InvEv (ocas l v w) |} ->
      h l = None ->
      ErrorPlain e (Idle h)
    | perror_write_racy t t' h l l' v v' e :
      t <> t' ->
      l = l' ->
      e = {| te_tid := t; te_ev := InvEv (owrite l v) |} ->
      ErrorPlain e (Pending h t' (owrite l' v')).

    Definition VPlain {A} : @LTS (EOMem A) := VAE StepPlain ErrorPlain.
  End PlainMem.

  Module PlainMemLayer.
    Section Impl.
      Context {A : Type}.

      Definition L : layer_interface :=
      {|
        li_sig := EOMem A;
        li_lts := PlainMem.VPlain;
        li_init := Idle empty_heap;
      |}.
    End Impl.
  End PlainMemLayer.

  Module OwnerMemLayer.
    Section Impl.
      Context {A : Type}.

      Definition L : layer_interface :=
      {|
        li_sig := EOMem A;
        li_lts := OwnerMem.VOMem;
        li_init := Idle OwnerMem.empty_omem;
      |}.
    End Impl.
  End OwnerMemLayer.

End OwnerMemSpec.
