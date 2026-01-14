Require Import FMapPositive.
Require Import Relation_Operators Operators_Properties.
Require Import Coq.PArith.PArith.
Require Import Coq.Program.Equality.
Require Import Lia.
Require Import PeanoNat.

Require Import coqrel.LogicalRelations.
Require Import models.EffectSignatures.
Require Import LinCCAL.
Require Import LTS.
Require Import Lang.
Require Import Semantics.
Require Import Assertion.
Require Import TPSimulationSet.
Require Import RGILogicSet.
Require Import Specs.


Module OneShotLazyCoinImpl.
  Import LinCCALBase.
  Import LTSSpec.
  Import Lang.
  Import AssertionsSet.
  Import RGILogic.
  Import TPSimulation.
  Import AtomicLTS CoinSpec.
  Import (coercions, canonicals, notations) Sig.
  Import (notations) LinCCAL.
  Import (canonicals) Sig.Plus.
  Open Scope prog_scope.

  Definition E : layer_interface :=
  {|
    li_sig := ECoin;
    li_lts := VCoin;
    li_init := Idle None;
  |}.
  
  Definition F : layer_interface :=
  {|
    li_sig := ECoin;
    li_lts := VCoin;
    li_init := Idle None;
  |}.

  Definition flip_impl : Prog (li_sig E) unit := Ret tt.

  Definition read_impl : Prog (li_sig E) bool :=
    flip >= _ =>
    read >= b =>
    Ret b.

  Definition assertion := @Assertion _ _ (li_lts E) (li_lts F).
  Definition rg_relation := @RGRelation _ _ (li_lts E) (li_lts F).

  Definition I : assertion :=
    fun s =>
        forall ρ π, Δ s ρ π ->
          state (σ s) = state ρ \/ state (σ s) = None.

  Definition G t : rg_relation := 
      fun s1 s2 => forall t', t <> t' ->
        forall ρ1 π1 ρ2 π2, Δ s1 ρ1 π1 -> Δ s2 ρ2 π2 -> TMap.find t' π1 = TMap.find t' π2.
          (* /\  (TicketOwnedBy t' s1 -> TicketOwnedBy t' s2 /\ state (snd (σ s1)) = state (snd (σ s2))). *)

  Definition R t : rg_relation :=
    fun s1 s2 =>
      forall ρ1 π1 ρ2 π2, Δ s1 ρ1 π1 -> Δ s2 ρ2 π2 -> TMap.find t π1 = TMap.find t π2.
      (* (TicketOwnedBy t s1 -> TicketOwnedBy t s2 /\ state (snd (σ s1)) = state (snd (σ s2))) /\
      (TMap.find t (π s1) = TMap.find t (π s2)). *)

  Lemma Istable {t} : Stable (R t) I I.
  Proof. unfold Stable. apply ConjRightImpl, ImplRefl. Qed.

  Program Definition Mcoin : layer_implementation E F := {|
    li_impl m :=
      match m with
      | flip => flip_impl
      | read => read_impl
      end
  |}.
End OneShotLazyCoinImpl.