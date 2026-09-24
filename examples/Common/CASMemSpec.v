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


(** A heap of CAS registers: the address-indexed counterpart of
    [CASRegSpec.ECASReg].  It mirrors [MemSpec.WriteRacyMem], except that
    cells are only ever updated with [ccas], so there is no write race and
    no racy error.  [cmalloc] takes the initial value of the fresh cell. *)
Module CASMemSpec.
  Import LTSSpec.
  Import LinCCALBase.
  Import AtomicLTS.
  Import TPSimulationSet.TPSimulation.

  Variant ECASMem_op {A} :=
  | cmalloc (v : A)
  | cget (addr : Addr)
  | ccas (addr : Addr) (v w : A).
  Arguments ECASMem_op : clear implicits.

  Definition ECASMem_ar {A} (m : ECASMem_op A) : Type :=
    match m with
    | cmalloc _ => Addr
    | cget _ => A
    | ccas _ _ _ => bool
    end.

  Canonical Structure ECASMem A :=
  {|
    Sig.op := ECASMem_op A;
    Sig.ar := ECASMem_ar
  |}.

  Module CASMem.
    Definition CASMemState {A} := @Heap A.

    Variant StepCASMem {A} :
      @ThreadEvent (ECASMem A) -> CASMemState -> CASMemState -> Prop :=
    (* alloc steps *)
    | step_alloc_inv t h v e :
      e = {| te_tid := t; te_ev := InvEv (cmalloc v) |} ->
      StepCASMem e h h
    | step_alloc_res t h l v e :
      e = {| te_tid := t; te_ev := ResEv (cmalloc v) l |} ->
      h l = None ->
      StepCASMem e h (heap_update l v h)
    (* read steps *)
    | step_get_inv t l h e :
      e = {| te_tid := t; te_ev := InvEv (cget l) |} ->
      h l <> None ->
      StepCASMem e h h
    | step_get_res t l h v e :
      e = {| te_tid := t; te_ev := ResEv (cget l) v |} ->
      h l = Some v ->
      StepCASMem e h h
    (* cas steps *)
    | step_cas_inv t l v w h e :
      e = {| te_tid := t; te_ev := InvEv (ccas l v w) |} ->
      h l <> None ->
      StepCASMem e h h
    | step_cas_res_succ t l v w h e :
      e = {| te_tid := t; te_ev := ResEv (ccas l v w) true |} ->
      h l = Some v ->
      StepCASMem e h (heap_update l w h)
    | step_cas_res_fail t l u v w h e :
      e = {| te_tid := t; te_ev := ResEv (ccas l v w) false |} ->
      h l = Some u ->
      u <> v ->
      StepCASMem e h h.

    Variant ErrorCASMem {A} :
      @ThreadEvent (ECASMem A) -> (@AState (ECASMem A) (@CASMemState A)) -> Prop :=
    | error_get_undefined t h l e :
      e = {| te_tid := t; te_ev := InvEv (cget l) |} ->
      h l = None ->
      ErrorCASMem e (Idle h)
    | error_cas_undefined t h l v w e :
      e = {| te_tid := t; te_ev := InvEv (ccas l v w) |} ->
      h l = None ->
      ErrorCASMem e (Idle h).

    Definition VCASMem {A} : @LTS (ECASMem A) := VAE StepCASMem ErrorCASMem.
  End CASMem.

  Module CASMemLayer.
    Section Impl.
      Context {A : Type}.

      Definition L : layer_interface :=
      {|
        li_sig := ECASMem A;
        li_lts := CASMem.VCASMem;
        li_init := Idle empty_heap;
      |}.
    End Impl.
  End CASMemLayer.

End CASMemSpec.
