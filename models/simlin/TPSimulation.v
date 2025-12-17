Require Import FMapPositive.
Require Import Coq.PArith.PArith.
Require Import Coq.Program.Equality.

Require Import coqrel.LogicalRelations.
Require Import models.EffectSignatures.
Require Import LinCCAL.
Require Import LTS.
Require Import Lang.
Require Import Semantics.

(* threadpool simulation *)
Module TPSimulation.
  Import Reg.
  Import LinCCALBase.
  Import LTSSpec.
  Import Lang.
  Import Semantics.

  Section Simulation.
    Context {E : Op.t}.
    Context {F : Op.t}.
    Context {VE : @LTS E}.
    Context {VF : @LTS F}.
    Context (M : ModuleImpl E F).

    Definition ConcreteConfig : Type := (State VE * @ThreadPoolState E F)%type.
    Definition AbstractConfig : Type := @Poss F VF%type.

    CoInductive TPSimulation (σ : State VE) c (ρ : State VF) π : Prop :=
    | TPSim_Error
        (Herror : poss_steps (PossOk ρ π) (PossError)) :
        TPSimulation σ c ρ π
    | TPSim_Continue
        (tpsim_invstep :
          forall t f c' (Hstep : invstep M t f c c'),
          TPSimulation σ c' ρ (TMap.add t (ls_inv f) π))
        (tpsim_retstep :
          forall t f ret c' (Hstep : retstep t f ret c c'),
          TMap.find t π = Some (ls_linr f ret) /\
          TPSimulation σ c' ρ (TMap.remove t π))
        (tpsim_ustep :
          forall ev σ' c' (Hstep : ustep ev σ c σ' c'),
          exists ρ' π',
            poss_steps (PossOk ρ π) (PossOk ρ' π') /\
            TPSimulation σ' c' ρ' π')
        (tpsim_linstep :
          exists ρ' π',
          poss_steps (PossOk ρ π) (PossOk ρ' π') /\
          TPSimulation σ c ρ' π')
        (tpsim_taustep :
          forall t c' (Hstep : taustep t c c'),
          TPSimulation σ c' ρ π)
        (tpsim_noerror :
          forall ev, ~ uerror ev σ c) :
        TPSimulation σ c ρ π.

    Definition cal (σ0 : State VE) (ρ0 : State VF) : Prop :=
      TPSimulation σ0 (TMap.empty _) ρ0 (TMap.empty _).

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
