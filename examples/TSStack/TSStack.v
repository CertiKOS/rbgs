Require Import models.EffectSignatures.
Require Import LinCCAL.
Require Import LTS.
Require Import Lang.
Require Import TPSimulationSet.

Require Import examples.Common.ThreadDomain.
Require Import examples.Stacks.StackSpec.
Require Import examples.TSStack.TryStackAuxSpec.
Require Import examples.TSStack.TryStackSpec.
Require Import examples.TSStack.TSStackSpec.


(** Implementation of the TSStack layer from Fig. 12 and Appendix A.4.

    [push] forwards to the TryStack push.  [pop] retries [trypop] until it
    returns a node or reports the stack empty. *)
Module TSStackImpl.
  Import LinCCALBase.
  Import LTSSpec.
  Import Lang.
  Import TPSimulationSet.TPSimulation.
  Import TryStackAuxSpec.
  Import TryStackSpec.
  Import TSStackSpec.
  Import (coercions, canonicals, notations) Sig.

  Open Scope prog_scope.

  Section Impl.
    Context {A : Type}.
    Context (D : ThreadDomain.t).

    Definition E : layer_interface :=
      @TryStackLayer.L A D.

    Definition F : layer_interface :=
      @TSStackLayer.L A D.

    Definition push_impl
        (v : A) (_actor : tid) : Prog (li_sig E) unit :=
      ts_push v >= _ =>
      Ret tt.

    Definition pop_impl
        (_actor : tid) : Prog (li_sig E) (option A) :=
      Do {
        ts_trypop >= result =>
        Ret (match result with
             | TSuccNode v _ _ => inr (Some v)
             | TSuccEmpty => inr None
             | TFail => inl tt
             end)
      } Loop.

    Definition ts_stack_impl :
        ModuleImpl (li_sig E) (li_sig F) :=
      fun op =>
        match op with
        | StackSpec.push v => push_impl v
        | StackSpec.pop => pop_impl
        end.

  End Impl.

End TSStackImpl.
