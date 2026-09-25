Require Import LinCCAL.
Require Import TPSimulationSet.
Require Import CompLinLayer.

Require Import examples.Common.ThreadDomain.
Require Import examples.Common.IndexedFamilySpec.
Require Import examples.Common.IndexedFamily.
Require Import examples.Common.IndexedFamilyProof.
Require Import examples.Common.OwnerMemSpec.
Require Import examples.Common.OwnerMemProof.
Require Import examples.TSStack.Timestamp.
Require Import examples.TSStack.TimestampProof.
Require Import examples.TSStack.NodeMemProof.
Require Import examples.TSStack.SPListProof.
Require Import examples.TSStack.SPListFamilySpec.
Require Import examples.TSStack.SPListFamily.
Require Import examples.TSStack.SPListArraySpec.
Require Import examples.TSStack.SPListArrayProof.
Require Import examples.TSStack.ListPoolProof.
Require Import examples.TSStack.TSStackProof.

(** Top-level result for the verified timestamped stack.

    Every layer of the development is composed here, down to concrete
    memories and CAS registers:

      TSStack ◁ TryStack ◁ TryStackAux ◁ ListPool
              ◁ (SPListArray ◁ SPListFamily ◁ per-owner SPList
                   ◁ (NodeMem ◁ five plain memories) ⊗ head CAS register)
                ⊗ (Timestamp ◁ counter CAS register)

    The chain from ListPool up to TSStack is [TSStackProof.MListPoolTSStack];
    the family of per-owner SPLists is packaged by the indexed-family
    adapter, instantiated here with the concrete per-owner underlay. *)
Module TSStackTopLevel.
  Import LinCCALBase.
  Import TPSimulationSet.TPSimulation.
  Import CompLinLayer.
  Import IndexedFamilySpec.
  Import IndexedFamilyImpl.
  Import SPListFamilySpec.

  Section ComposedTSStack.
    Context {A : Type} (D : ThreadDomain.t).

    (** ** One SPList: five plain memories and the head register *)

    Definition SPList_underlay : layer_interface :=
      @NodeMemProof.EPlain A ⊗ₗ SPListProof.ECASLayer.

    (** NodeMem over the plain memories, the head register untouched. *)
    Definition MSPList_underlay :
        layer_implementation_linearizability SPList_underlay (@SPListProof.E A) :=
      @NodeMemProof.MNodeMemOverPlain A ⊗ LIId SPListProof.ECASLayer.

    Definition MSPList_component (owner : tid) :
        layer_implementation_linearizability SPList_underlay
          (SetComponentLayer (@SPListIndexedObject A) owner) :=
      MSPList_underlay ▶ @SPListFamilyImpl.splist_component_correct A owner.

    (** ** The family of SPLists, one per thread of [D] *)

    Definition SPListFamily_underlay : layer_interface :=
      TensorUnderlay (fun _ : tid => SPList_underlay) D.

    Definition MSPListFamily :
        layer_implementation_linearizability SPListFamily_underlay
          (@SPListFamilyLayer.L A D) :=
      IndexedFamilyProof.compose_verified_indexed_family D
        (@SPListIndexedObject A) (fun _ => SPList_underlay) MSPList_component.

    Definition MSPListArray :
        layer_implementation_linearizability SPListFamily_underlay
          (@SPListArraySpec.SPListArrayLayer.L A D) :=
      MSPListFamily ▶ @SPListArrayProof.MSPListArrayLinearizable A D.

    (** ** ListPool's underlay: the array of lists and the timestamp *)

    Definition TSStack_underlay : layer_interface :=
      SPListFamily_underlay ⊗ₗ TimestampImpl.E.

    Definition MListPool_underlay :
        layer_implementation_linearizability TSStack_underlay
          (@ListPoolProof.E A D) :=
      MSPListArray ⊗ TimestampProof.MTimestampLinearizable.

    (** ** The stack *)

    Definition TSStack_spec : layer_interface := @TSStackProof.F A D.

    Definition MTSStack_linearizable :
        layer_implementation_linearizability TSStack_underlay TSStack_spec :=
      MListPool_underlay ▶ @TSStackProof.MListPoolTSStack A D.

    Print Assumptions MTSStack_linearizable.
  End ComposedTSStack.
End TSStackTopLevel.

Export TSStackTopLevel.
