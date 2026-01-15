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
  Import AtomicLTS CoinSpec CASRegSpec.
  Import (coercions, canonicals, notations) Sig.
  Import (notations) LinCCAL.
  Import (canonicals) Sig.Plus.
  Open Scope prog_scope.

  Definition E : layer_interface :=
  {|
    li_sig := ECASReg (option bool);
    li_lts := VCASReg;
    li_init := Idle (Some false);
  |}.
  
  Definition F : layer_interface :=
  {|
    li_sig := ECoin;
    li_lts := VCoin;
    li_init := Idle false;
  |}.

  Parameter rand : bool.

  Definition flip_impl : Prog (li_sig E) unit :=
    set None >= _ => Ret tt.

  Definition read_impl : Prog (li_sig E) bool :=
    Do {
      get >= c =>
      match c with
      | Some b => Ret (inr b)
      | None =>
          let b := rand in
          cas None (Some b) >= succ =>
          Ret (if succ then inr b else inl tt)
      end
    } Loop.

  Definition assertion := @Assertion _ _ (li_lts E) (li_lts F).
  Definition rg_relation := @RGRelation _ _ (li_lts E) (li_lts F).

  Definition I : assertion :=
    fun s =>
            (* state correspondence *)
            ((state (σ s) = None /\ forall b, exists ρ π, Δ s ρ π /\ state ρ = b) \/
            (exists b, state (σ s) = Some b /\ exists ρ π, Δ s ρ π /\ state ρ = b))
            (* racy set implies racy flip *)
        /\  (forall v t w, σ s = Pending v t (set w) ->
              exists ρ π, Δ s ρ π /\ exists b, ρ = Pending b t flip)
        /\  (exists ρ π, Δ s ρ π).

  Definition G t : rg_relation := 
      fun s1 s2 => forall t', t <> t' ->
        forall ρ1 π1 ρ2 π2, Δ s1 ρ1 π1 -> Δ s2 ρ2 π2 -> TMap.find t' π1 = TMap.find t' π2.

  Definition R t : rg_relation :=
    fun s1 s2 =>
      forall ρ1 π1 ρ2 π2, Δ s1 ρ1 π1 -> Δ s2 ρ2 π2 -> TMap.find t π1 = TMap.find t π2.

  Lemma Istable {t} : Stable (R t) I I.
  Proof. unfold Stable. apply ConjRightImpl, ImplRefl. Qed.

  Lemma ALinstable {t ls}: Stable (R t) I (ALin t ls).
  Proof.
    unfold Stable, ALin, R.
    intros ? [[? [? ?]] ?] ? ? ?.
    rewrite <- H1. auto.
  Qed.

  Program Definition Mcoin : layer_implementation E F := {|
    li_impl m :=
      match m with
      | flip => flip_impl
      | read => read_impl
      end
  |}.
End OneShotLazyCoinImpl.