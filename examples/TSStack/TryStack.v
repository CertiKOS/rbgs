Require Import models.EffectSignatures.
Require Import LinCCAL.
Require Import LTS.
Require Import Lang.
Require Import TPSimulationSet.

Require Import examples.Common.ThreadDomain.
Require Import examples.TSStack.TryStackAuxSpec.
Require Import examples.TSStack.TryStackSpec.


(** Implementation of the TryStack layer from Appendix A.4.

    The code preserves push and forwards try-pop to TryStackAux.  This
    apparently small adapter is the layer boundary at which the graph-based,
    interval-sequential TryStackAux operation is exposed as the atomic
    try-pop specified by [TryStackSpec]. *)
Module TryStackImpl.
  Import LinCCALBase.
  Import LTSSpec.
  Import Lang.
  Import TPSimulationSet.TPSimulation.
  Import TryStackAuxSpec.
  Import TryStackSpec.
  Import (coercions, canonicals, notations) Sig.

  Open Scope prog_scope.

  Section Impl.
    Context {A : Type}.
    Context (D : ThreadDomain.t).

    Definition E : layer_interface :=
      @TryStackAuxLayer.L A D.

    Definition F : layer_interface :=
      @TryStackLayer.L A D.

    Definition push_impl
        (v : A) (_actor : tid) : Prog (li_sig E) unit :=
      tsa_push v >= _ =>
      Ret tt.

    Definition trypop_impl
        (_actor : tid) : Prog (li_sig E) (@TResult A) :=
      tsa_trypop >= result =>
      Ret result.

    Definition try_stack_impl :
        ModuleImpl (li_sig E) (li_sig F) :=
      fun op =>
        match op with
        | ts_push v => push_impl v
        | ts_trypop => trypop_impl
        end.

  End Impl.

End TryStackImpl.
