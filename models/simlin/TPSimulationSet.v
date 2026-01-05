Require Import FMapPositive.
Require Import Coq.PArith.PArith.
Require Import Coq.Program.Equality.
Require Import Coq.Classes.RelationClasses.
Require Import Relation_Operators Operators_Properties.

Require Import coqrel.LogicalRelations.
Require Import models.EffectSignatures.
Require Import LinCCAL.
Require Import LTS.
Require Import Lang.
Require Import Semantics.

Import Reg.
Import LinCCALBase.
Import LTSSpec.
Import Semantics.

Section AbstractConfig.
  Context {F : Op.t} {VF : @LTS F}.
  Definition AbstractConfig : Type := State VF -> tmap (@LinState F) -> Prop.

  Definition ac_equiv (Δ1 Δ2 : AbstractConfig) : Prop :=
    forall ρ π, Δ1 ρ π <-> Δ2 ρ π.

  Program Instance Equivalence_ACEquiv : Equivalence ac_equiv.
  Next Obligation. constructor; auto. Defined.
  Next Obligation. constructor; apply H. Defined.
  Next Obligation.
    constructor.
    - unfold ac_equiv in *. intros. apply H0, H. auto.
    - unfold ac_equiv in *. intros. apply H, H0. auto.
  Defined.

  Definition ac_subset (Δ1 Δ2 : AbstractConfig) : Prop :=
    forall ρ π, Δ1 ρ π -> Δ2 ρ π.

  Variant ac_singleton ρ π : AbstractConfig :=
  | ACSingle : ac_singleton ρ π ρ π.    

  Variant ac_union (Δ1 Δ2 : AbstractConfig) : AbstractConfig :=
  | ACUnionLeft ρ π: Δ1 ρ π -> ac_union Δ1 Δ2 ρ π
  | ACUnionRight ρ π: Δ2 ρ π -> ac_union Δ1 Δ2 ρ π.

  Variant ac_intersect (Δ1 Δ2 : AbstractConfig) : AbstractConfig :=
  | ACIntersect ρ π: Δ1 ρ π -> Δ2 ρ π -> ac_intersect Δ1 Δ2 ρ π.

End AbstractConfig.
Arguments AbstractConfig {F} VF.

#[global] Existing Instance Equivalence_ACEquiv.

Delimit Scope ac_scope with AbstractConfig.
Bind Scope ac_scope with AbstractConfig.

Notation "[( ρ , π )]" := (ac_singleton ρ π) (at level 10) : ac_scope.
Notation "Δ1 ⊆ Δ2" := (ac_subset Δ1 Δ2) (at level 70) : ac_scope.
Notation "Δ1 ≡ Δ2" := (ac_equiv Δ1 Δ2) (at level 70) : ac_scope.
Notation "Δ1 ∪ Δ2" := (ac_union Δ1 Δ2) (at level 50) : ac_scope.
Notation "Δ1 ∩ Δ2" := (ac_intersect Δ1 Δ2) (at level 40) : ac_scope.


(* threadpool simulation *)
Module TPSimulation.
  Import Lang.

  Section Simulation.
    Context {E : Op.t}.
    Context {F : Op.t}.
    Context {VE : @LTS E}.
    Context {VF : @LTS F}.
    Context (M : ModuleImpl E F).

    (* Definition AbstractConfig : Type := (@Poss F VF%type) -> Prop. *)
    (* Definition AbstractConfig : Type := State VF -> tmap (@LinState F) -> Prop. *)

    Variant ac_inv (Δ : AbstractConfig VF) t f : AbstractConfig VF :=
    | ACInv ρ π (Hposs : Δ ρ π) :
        ac_inv Δ t f ρ (TMap.add t (ls_inv f) π).

    Variant ac_res (Δ : AbstractConfig VF) t : AbstractConfig VF :=
    | ACRes ρ π (Hposs : Δ ρ π):
        ac_res Δ t ρ (TMap.remove t π).
    
    Variant ac_steps (Δ : AbstractConfig VF) : AbstractConfig VF :=
    | ACSteps ρ π ρ' π' (Hposs : Δ ρ π)
        (Hpstep : poss_steps (PossOk ρ π) (PossOk ρ' π')):
        ac_steps Δ ρ' π'.

    CoInductive TPSimulation (σ : State VE) (c : @ThreadPoolState E F) (Δ : AbstractConfig VF) : Prop :=
    | TPSim_Error ρ π
        (Hposs : Δ ρ π)
        (Herror : poss_steps (PossOk ρ π) (PossError)) :
        TPSimulation σ c Δ
    | TPSim_Continue
        (tpsim_invstep :
          forall t f c' (Hstep : invstep M t f c c'),
          TPSimulation σ c' (ac_inv Δ t f))
        (tpsim_retstep :
          forall t f ret c' (Hstep : retstep t f ret c c'),
          (forall ρ π, Δ ρ π -> TMap.find t π = Some (ls_linr f ret)) /\
          TPSimulation σ c' (ac_res Δ t))
        (tpsim_ustep :
          forall ev σ' c' (Hstep : ustep ev σ c σ' c'),
          exists (Δ' : AbstractConfig VF),
            (Δ' ⊆ ac_steps Δ)%AbstractConfig /\
            TPSimulation σ' c' Δ')
        (tpsim_linstep :
          exists Δ', (Δ' ⊆ ac_steps Δ)%AbstractConfig /\
          TPSimulation σ c Δ')
        (tpsim_taustep :
          forall t c' (Hstep : taustep t c c'),
          TPSimulation σ c' Δ)
        (tpsim_noerror : forall ev, ~ uerror ev σ c)
        (tpsim_nonemp : exists ρ π, Δ ρ π) :
        TPSimulation σ c Δ.

    Definition ac_init (ρ0 : State VF) := [(ρ0, (TMap.empty _))]%AbstractConfig.

    Definition cal (σ0 : State VE) (ρ0 : State VF) : Prop :=
      TPSimulation σ0 (TMap.empty _) (ac_init ρ0).

    Open Scope ac_scope.

    Lemma ac_steps_refl : forall Δ, Δ ⊆ ac_steps Δ.
    Proof.
      intros. intros ? ? ?.
      econstructor; eauto.
      apply rt_refl.
    Qed.

    (* TODO: soundness: linearizability *)
  End Simulation.


  Record layer_interface :=
  {
    li_sig : Op.t;
    li_lts : @LTS li_sig;
    li_init : State li_lts;
  }.

  Record layer_implementation {L L' : layer_interface} :=
  {
    li_impl : ModuleImpl (li_sig L) (li_sig L');
    li_correct : cal li_impl (li_init L) (li_init L');
  }.
  Arguments layer_implementation : clear implicits.
End TPSimulation.
