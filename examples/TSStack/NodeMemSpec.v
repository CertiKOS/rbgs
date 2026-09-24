Require Import FMapPositive.
Require Import Relation_Operators Operators_Properties.
Require Import Coq.PArith.PArith.
Require Import Coq.Program.Equality.
Require Import PeanoNat.

Require Import coqrel.LogicalRelations.
Require Import models.EffectSignatures.
Require Import examples.Common.Heap.
Require Import examples.Common.AtomicLTS.
Require Import examples.TSStack.TimestampSpec.
Require Import LinCCAL.
Require Import LTS.
Require Import TPSimulationSet.


Module NodeMemSpec.
  Import LTSSpec.
  Import LinCCALBase.
  Import AtomicLTS.
  Import TPSimulationSet.TPSimulation.
  Import TimestampSpec.

  Section Spec.
    Context {A : Type}.

  Definition Node : Type := A * TS * bool * Ptr.

  Variant ENodeMem_op :=
  | nmalloc (v : A) (next : Ptr)
  | nmsetTS (l : Addr) (t : TS)
  | nmgetValue (l : Addr)
  | nmgetTS (l : Addr)
  | nmgetTaken (l : Addr)
  | nmgetNext (l : Addr)
  | nmtryTake (l : Addr).
  Arguments ENodeMem_op : clear implicits.

  Definition ENodeMem_ar (m : ENodeMem_op) : Type :=
    match m with
    | nmalloc _ _ => Addr
    | nmsetTS _ _ => unit
    | nmgetValue _ => A
    | nmgetTS _ => TS
    | nmgetTaken _ => bool
    | nmgetNext _ => Ptr
    | nmtryTake _ => bool
    end.

  Canonical Structure ENodeMem :=
  {|
    Sig.op := ENodeMem_op;
    Sig.ar := ENodeMem_ar
  |}.

  Definition NodeMemState := @Heap Node.

  Section Semantics.
    Variant StepNodeMem :
      @ThreadEvent ENodeMem -> NodeMemState -> NodeMemState -> Prop :=
    (* allocation *)
    | step_malloc_inv t h v next e :
        e = {| te_tid := t; te_ev := InvEv (nmalloc v next) |} ->
        StepNodeMem e h h
    | step_malloc_res t h l v next e :
        e = {| te_tid := t; te_ev := ResEv (nmalloc v next) l |} ->
        h l = None ->
        StepNodeMem e h
          (heap_update l (v, TSTop, false, next) h)

    (* timestamp update *)
    | step_setTS_inv t h l ts e :
        e = {| te_tid := t; te_ev := InvEv (nmsetTS l ts) |} ->
        h l <> None ->
        StepNodeMem e h h
    | step_setTS_res t h l v old_ts taken next ts e :
        e = {| te_tid := t; te_ev := ResEv (nmsetTS l ts) tt |} ->
        h l = Some (v, old_ts, taken, next) ->
        StepNodeMem e h (heap_update l (v, match old_ts with TSTop => ts | _ => old_ts end, taken, next) h)

    (* per-field reads.  Each field is read on its own; a client that
       needs a consistent view of several fields must argue from the
       monotonicity of [ts] (set once from [TSTop]) and [taken]
       (flipped once from [false]). *)
    | step_getValue_inv t h l e :
        e = {| te_tid := t; te_ev := InvEv (nmgetValue l) |} ->
        h l <> None ->
        StepNodeMem e h h
    | step_getValue_res t h l v ts taken next e :
        e = {| te_tid := t; te_ev := ResEv (nmgetValue l) v |} ->
        h l = Some (v, ts, taken, next) ->
        StepNodeMem e h h
    | step_getTS_inv t h l e :
        e = {| te_tid := t; te_ev := InvEv (nmgetTS l) |} ->
        h l <> None ->
        StepNodeMem e h h
    | step_getTS_res t h l v ts taken next e :
        e = {| te_tid := t; te_ev := ResEv (nmgetTS l) ts |} ->
        h l = Some (v, ts, taken, next) ->
        StepNodeMem e h h
    | step_getTaken_inv t h l e :
        e = {| te_tid := t; te_ev := InvEv (nmgetTaken l) |} ->
        h l <> None ->
        StepNodeMem e h h
    | step_getTaken_res t h l v ts taken next e :
        e = {| te_tid := t; te_ev := ResEv (nmgetTaken l) taken |} ->
        h l = Some (v, ts, taken, next) ->
        StepNodeMem e h h
    | step_getNext_inv t h l e :
        e = {| te_tid := t; te_ev := InvEv (nmgetNext l) |} ->
        h l <> None ->
        StepNodeMem e h h
    | step_getNext_res t h l v ts taken next e :
        e = {| te_tid := t; te_ev := ResEv (nmgetNext l) next |} ->
        h l = Some (v, ts, taken, next) ->
        StepNodeMem e h h

    (* atomic test-and-take *)
    | step_tryTake_inv t h l e :
        e = {| te_tid := t; te_ev := InvEv (nmtryTake l) |} ->
        h l <> None ->
        StepNodeMem e h h
    | step_tryTake_res_succ t h l v ts next e :
        e = {| te_tid := t; te_ev := ResEv (nmtryTake l) true |} ->
        h l = Some (v, ts, false, next) ->
        StepNodeMem e h (heap_update l (v, ts, true, next) h)
    | step_tryTake_res_fail t h l v ts next e :
        e = {| te_tid := t; te_ev := ResEv (nmtryTake l) false |} ->
        h l = Some (v, ts, true, next) ->
        StepNodeMem e h h.

    Variant ErrorNodeMem :
      @ThreadEvent ENodeMem -> (@AState ENodeMem NodeMemState) -> Prop :=
    | error_setTS_undefined t h l ts e :
        e = {| te_tid := t; te_ev := InvEv (nmsetTS l ts) |} ->
        h l = None ->
        ErrorNodeMem e (Idle h)
    | error_getValue_undefined t h l e :
        e = {| te_tid := t; te_ev := InvEv (nmgetValue l) |} ->
        h l = None ->
        ErrorNodeMem e (Idle h)
    | error_getTS_undefined t h l e :
        e = {| te_tid := t; te_ev := InvEv (nmgetTS l) |} ->
        h l = None ->
        ErrorNodeMem e (Idle h)
    | error_getTaken_undefined t h l e :
        e = {| te_tid := t; te_ev := InvEv (nmgetTaken l) |} ->
        h l = None ->
        ErrorNodeMem e (Idle h)
    | error_getNext_undefined t h l e :
        e = {| te_tid := t; te_ev := InvEv (nmgetNext l) |} ->
        h l = None ->
        ErrorNodeMem e (Idle h)
    | error_tryTake_undefined t h l e :
        e = {| te_tid := t; te_ev := InvEv (nmtryTake l) |} ->
        h l = None ->
        ErrorNodeMem e (Idle h)
    | error_setTS_racy t t' h l l' ts ts' e :
        t <> t' ->
        l = l' ->
        e = {| te_tid := t; te_ev := InvEv (nmsetTS l ts) |} ->
        ErrorNodeMem e (Pending h t' (nmsetTS l' ts')).

    Definition VNodeMem : @LTS ENodeMem :=
      VAE (StepNodeMem) ErrorNodeMem.
  End Semantics.

  End Spec.

  Module NodeMemLayer.
    Section Impl.
      Context {A : Type}.

      Definition L : layer_interface :=
      {|
        li_sig := @ENodeMem A;
        li_lts := @VNodeMem A;
        li_init := Idle empty_heap;
      |}.
    End Impl.
  End NodeMemLayer.

End NodeMemSpec.
