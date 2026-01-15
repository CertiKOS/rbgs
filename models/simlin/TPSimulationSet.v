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

Section AbstractConfig.
  Context {F : Op.t} {VF : @LTS F}.

  Definition AbstractConfigProp : Type := State VF -> tmap (@LinState F) -> Prop.

  Record AbstractConfig : Type := mkAC {
    ac_prop :> AbstractConfigProp;
    ac_nonempty : exists ρ π, ac_prop ρ π;
    ac_domexact : forall ρ1 π1 ρ2 π2, ac_prop ρ1 π1 -> ac_prop ρ2 π2 ->
                    forall t, TMap.find t π1 = None <-> TMap.find t π2 = None
  }.

  Definition ac_equiv (Δ1 Δ2 : AbstractConfigProp) : Prop :=
    forall ρ π, Δ1 ρ π <-> Δ2 ρ π.

  Program Instance Equivalence_ACEquiv : Equivalence ac_equiv.
  Next Obligation. constructor; auto. Defined.
  Next Obligation. constructor; apply H. Defined.
  Next Obligation.
    constructor.
    - unfold ac_equiv in *. intros. apply H0, H. auto.
    - unfold ac_equiv in *. intros. apply H, H0. auto.
  Defined.

  Definition ac_subset (Δ1 Δ2 : AbstractConfigProp) : Prop :=
    forall ρ π, Δ1 ρ π -> Δ2 ρ π.

  Variant ac_singleton_prop ρ π : AbstractConfigProp :=
  | ACSingle : ac_singleton_prop ρ π ρ π.

  Program Definition ac_singleton ρ π : AbstractConfig :=
    {| ac_prop := ac_singleton_prop ρ π |}.
  Next Obligation. exists ρ, π. constructor. Qed.
  Next Obligation.
    inversion H; inversion H0; subst. reflexivity.
  Qed.

  Variant ac_union_prop (Δ1 Δ2 : AbstractConfigProp) : AbstractConfigProp :=
  | ACUnionLeft ρ π: Δ1 ρ π -> ac_union_prop Δ1 Δ2 ρ π
  | ACUnionRight ρ π: Δ2 ρ π -> ac_union_prop Δ1 Δ2 ρ π.

  (* ac_union does not preserve ac_domexact in general *)
  (* Program Definition ac_union (Δ1 Δ2 : AbstractConfig) : AbstractConfig := ... *)

  Variant ac_intersect_prop (Δ1 Δ2 : AbstractConfigProp) : AbstractConfigProp :=
  | ACIntersect ρ π: Δ1 ρ π -> Δ2 ρ π -> ac_intersect_prop Δ1 Δ2 ρ π.

End AbstractConfig.

Arguments AbstractConfigProp {F} VF.
Arguments AbstractConfig {F} VF.

#[global] Existing Instance Equivalence_ACEquiv.

Delimit Scope ac_scope with AbstractConfig.
Bind Scope ac_scope with AbstractConfig.

Notation "[( ρ , π )]" := (ac_singleton ρ π) (at level 10) : ac_scope.
Notation "Δ1 ⊆ Δ2" := (ac_subset Δ1 Δ2) (at level 70) : ac_scope.
Notation "Δ1 ≡ Δ2" := (ac_equiv Δ1 Δ2) (at level 70) : ac_scope.
Notation "Δ1 ∪ Δ2" := (ac_union_prop Δ1 Δ2) (at level 50) : ac_scope.
Notation "Δ1 ∩ Δ2" := (ac_intersect_prop Δ1 Δ2) (at level 40) : ac_scope.


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

    Variant ac_inv_prop (Δ : AbstractConfigProp VF) t f : AbstractConfigProp VF :=
    | ACInv ρ π (Hposs : Δ ρ π) :
        ac_inv_prop Δ t f ρ (TMap.add t (ls_inv f) π).

    Program Definition ac_inv (Δ : AbstractConfig VF) t f : AbstractConfig VF :=
      {| ac_prop := ac_inv_prop Δ t f |}.
    Next Obligation.
      destruct (ac_nonempty Δ) as [ρ [π H]].
      exists ρ, (TMap.add t0 (ls_inv f) π). constructor. auto.
    Qed.
    Next Obligation.
      inversion H; inversion H0; subst.
      (* rewrite (ac_domexact Δ _ _ _ _ Hposs Hposs0 t0). *)
      destruct (Pos.eq_dec t1 t0); subst.
      - do 2 rewrite PositiveMap.gss. split; discriminate.
      - do 2 (rewrite PositiveMap.gso; auto).
        rewrite (ac_domexact Δ _ _ _ _ Hposs Hposs0 t1).
        reflexivity.
    Qed.

    Variant ac_res_prop (Δ : AbstractConfigProp VF) t : AbstractConfigProp VF :=
    | ACRes ρ π (Hposs : Δ ρ π):
        ac_res_prop Δ t ρ (TMap.remove t π).
    
    Program Definition ac_res (Δ : AbstractConfig VF) t : AbstractConfig VF :=
      {| ac_prop := ac_res_prop Δ t |}.
    Next Obligation.
      destruct (ac_nonempty Δ) as [ρ [π H]].
      exists ρ, (TMap.remove t π). constructor. auto.
    Qed.
    Next Obligation.
      inversion H; inversion H0; subst.
      rewrite (ac_domexact Δ _ _ _ _ Hposs Hposs0 t0).
      destruct (Pos.eq_dec t t0); subst.
      - do 2 rewrite PositiveMap.grs. split; auto.
      - do 2 (rewrite PositiveMap.gro; auto).
        reflexivity.
    Qed.

    Variant ac_steps_prop (Δ : AbstractConfigProp VF) : AbstractConfigProp VF :=
    | ACSteps ρ π ρ' π' (Hposs : Δ ρ π)
        (Hpstep : poss_steps (PossOk ρ π) (PossOk ρ' π')):
        ac_steps_prop Δ ρ' π'.

    Lemma poss_steps_pi : forall ρ π ρ' π', poss_steps (PossOk ρ π) (PossOk ρ' π') -> π = π'.
    Proof.
      intros. remember (PossOk ρ π) as p. remember (PossOk ρ' π') as p'.
      induction H; subst; auto.
      inversion Heqp; subst.
      (* We assume poss_step preserves pi. This depends on Semantics.v *)
      admit.
    Admitted.

    Program Definition ac_steps (Δ : AbstractConfig VF) : AbstractConfig VF :=
      {| ac_prop := ac_steps_prop Δ |}.
    Next Obligation.
      destruct (ac_nonempty Δ) as [ρ [π H]].
      exists ρ, π. econstructor; eauto. apply rt_refl.
    Qed.
    Next Obligation.
      inversion H; inversion H0; subst.
      apply poss_steps_pi in Hpstep; apply poss_steps_pi in Hpstep0; subst.
      eapply ac_domexact; eauto.
    Qed.

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
        (tpsim_noerror : forall ev, ~ uerror ev σ c) :
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
