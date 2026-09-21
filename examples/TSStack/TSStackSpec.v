Require Import Coq.Lists.List.

Require Import models.EffectSignatures.
Require Import LinCCAL.
Require Import LTS.
Require Import TPSimulationSet.

Require Import examples.Common.ThreadDomain.
Require Import examples.Common.AtomicLTS.
Require Import examples.Stacks.StackSpec.


(** The atomic stack specification used as the top layer of the TS stack
    development (Appendix A.4, "Stack").

    The signature [EStack A] and the transition relation [StepStack] are
    the ones of [examples/Stacks/StackSpec.v].  Only the error rule is
    new: like every lower TSStack layer, an operation invoked by a thread
    outside the thread domain [D] is an error.  The underlay [TryStackSpec]
    raises the same error, and the thread-pool semantics only tolerates an
    underlay error when some abstract possibility is itself erroneous, so
    the error-free [StackSpec.VStack] cannot serve as this overlay. *)
Module TSStackSpec.
  Import LTSSpec.
  Import LinCCALBase.
  Import AtomicLTS.
  Import StackSpec.
  Import TPSimulationSet.TPSimulation.

  Section Spec.
    Context {A : Type}.
    Context (D : ThreadDomain.t).

    Variant ErrorTSStack :
      @ThreadEvent (EStack A) -> @AState (EStack A) (list A) -> Prop :=
    | error_stack_actor_outside actor op stk e :
        ~ ThreadDomain.contains D actor ->
        e = {| te_tid := actor; te_ev := InvEv op |} ->
        ErrorTSStack e (Idle stk).

    Definition VTSStack : @LTS (EStack A) :=
      VAE StepStack ErrorTSStack.
  End Spec.

  Module TSStackLayer.
    Section Layer.
      Context {A : Type}.
      Context (D : ThreadDomain.t).

      Definition L : layer_interface :=
      {|
        li_sig := EStack A;
        li_lts := @VTSStack A D;
        li_init := Idle nil
      |}.
    End Layer.
  End TSStackLayer.

End TSStackSpec.
