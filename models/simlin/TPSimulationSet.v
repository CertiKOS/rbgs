Require Import FMapPositive.
Require Import Coq.PArith.PArith.
Require Import Coq.Program.Equality.
Require Import Coq.Classes.RelationClasses.
Require Import Relation_Operators Operators_Properties.
Require Import Coq.Program.Program.

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

(* threadpool simulation *)
Module TPSimulation.
  Import Lang.

  Section Simulation.
    Context {E : Op.t}.
    Context {F : Op.t}.
    Context {VE : @LTS E}.
    Context {VF : @LTS F}.
    Context (M : ModuleImpl E F).

    CoInductive TPSimulation (σ : State VE) (c : @ThreadPoolState E F) (Δ : AbstractConfig VF) : Prop :=
    | TPSim_Error (ρ : State VF) (π : LinCCALBase.tmap (@LinState F))
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
        (tpsim_noerror : forall ev, ~ uerror ev σ c) :
        TPSimulation σ c Δ.

    Definition ac_init (ρ0 : State VF) := [(ρ0, (TMap.empty _))]%AbstractConfig.

    Definition cal (σ0 : State VE) (ρ0 : State VF) : Prop :=
      TPSimulation σ0 (TMap.empty _) (ac_init ρ0).

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
