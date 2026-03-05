Require Import FMapPositive.
Require Import Relation_Operators Operators_Properties.
Require Import Coq.PArith.PArith.
Require Import Coq.Program.Equality.

Require Import coqrel.LogicalRelations.
Require Import models.EffectSignatures.
Require Import LinCCAL.
Require Import LTS.
Require Import Lang.
Require Import Semantics.
Require Import TPSimulationSet.
Require Import Logics.
Require Import SeparationAlgebra.

Module Type ProofState.
  Import Reg LinCCALBase LTSSpec Semantics.

  Parameter ProofState :
    forall {E : Op.t} {F : Op.t} {VE : @LTS E} {VF : @LTS F}, Type.

  Parameter σ :
    forall {E F VE VF}, ProofState (E:=E) (F:=F) (VE:=VE) (VF:=VF) -> State VE.

End ProofState.

Module Assertions (PS : ProofState).
  Import Reg.
  Import LinCCALBase.
  Import LTSSpec.
  Import Semantics.
  Import PS.

  Section AssertionDef.
    Context {E : Op.t}.
    Context {F : Op.t}.
    Context {VE : @LTS E}.
    Context {VF : @LTS F}.

    Definition RGRelation : Type := relation (@ProofState E F VE VF).

    Definition Subset (r1 r2 : RGRelation) : Prop :=
      forall x y, r1 x y -> r2 x y.
    
    Definition Union (r1 r2 : RGRelation) : RGRelation :=
      fun x y => r1 x y \/ r2 x y.
    
    Definition Inter (r1 r2 : RGRelation) : RGRelation :=
      fun x y => r1 x y /\ r2 x y.

    Definition ComposeA (P : Assertion) (R : RGRelation) : Assertion :=
      fun s => exists s', P s' /\ R s' s.
    
    Definition ComposeR (R S : RGRelation) : RGRelation :=
      fun s s' => exists s'', R s s'' /\ S s'' s'.

    Definition ComposeR' (P : Assertion) (R : RGRelation) : RGRelation :=
      fun s s' => R s s' /\ P s.

    Definition GId : RGRelation := fun x y => x = y.

    Definition ANoError (ev : ThreadEvent) : @Assertion (@ProofState E F VE VF) :=
      fun s => ~ Error VE ev (σ s).
  End AssertionDef.
  

  Delimit Scope rg_relation_scope with RGRelation.
  Bind Scope rg_relation_scope with RGRelation.
  
  Notation "R ⊆ S" := (Subset R S) (at level 70) : rg_relation_scope.
  Notation "R ∪ S" := (Union R S) (at level 50) : rg_relation_scope.
  Notation "R ∩ S" := (Inter R S) (at level 40) : rg_relation_scope.
  Notation "R ○ S" := (ComposeR S R) (at level 30) : rg_relation_scope.
  Notation "R ⊚ P" := (ComposeA P R) (at level 30) : rg_relation_scope.
  Notation "P ⊓ R" := (ComposeR' P R) (at level 30) : rg_relation_scope.

  Section AssertionLemmas.
    Context {E : Op.t}.
    Context {F : Op.t}.
    Context {VE : @LTS E}.
    Context {VF : @LTS F}.

    Open Scope rg_relation_scope.
    Open Scope assertion_scope.

    Lemma RGSubsetUnion : forall (R1 R2 R3 : @RGRelation _ _ VE VF),
      R1 ⊆ R2 \/ R1 ⊆ R3 ->
      R1 ⊆ R2 ∪ R3.
    Proof.
      intros. destruct H; intros ? ? ?.
      - left. auto.
      - right. auto.
    Qed.

    Lemma ImplRefl {P:@Assertion (@ProofState E F VE VF)}: ⊨ P ==>> P.
    Proof. intros. intros ?. auto. Qed.

    Lemma ImplTauto {P Q : @Assertion (@ProofState E F VE VF)} : (⊨ Q) -> ⊨ P ==>> Q.
    Proof. intros. intros ?. auto. Qed.

    Lemma ImplTrans {P Q R : @Assertion (@ProofState E F VE VF)} : (⊨ P ==>> Q) -> (⊨ Q ==>> R) -> ⊨ P ==>> R.
    Proof. intros. intros ?. apply H0, H; auto. Qed.


    Lemma ConjLeftImpl {P1 P2 P3: @Assertion (@ProofState E F VE VF)}:
      (⊨ P1 ==>> P3) ->
      ⊨ P1 //\\ P2 ==>> P3.
    Proof. intros ? ? [? ?]; apply H; auto. Qed.

    Lemma ConjRightImpl {P1 P2 P3 : @Assertion (@ProofState E F VE VF)}:
      (⊨ P2 ==>> P3) ->
      ⊨ P1 //\\ P2 ==>> P3.
    Proof. intros ? ? [? ?]; apply H; auto. Qed.

    Lemma ImplConj {P1 P2 P3 : @Assertion (@ProofState E F VE VF)}:
      (⊨ P1 ==>> P2) ->
      (⊨ P1 ==>> P3) ->
      (⊨ P1 ==>> P2 //\\ P3).
    Proof.
      intros. intros ?.
      pose proof H1.
      apply H in H1. apply H0 in H2.
      split; auto.
    Qed.

    Definition Stable (R : @RGRelation _ _ VE VF) I P := ⊨ (R ⊚ P) //\\ I ==>> P.

    Lemma StableForall {A} : forall R I P,
      (forall x : A, Stable R I (P x)) ->
      Stable R I (∀ x, P x).
    Proof.
      intros. intros ? [[? [? ?]] ?] ?.
      apply H; split; auto.
      eexists. eauto.
    Qed.

    Lemma StableExists {A} : forall R I P,
      (forall x : A, Stable R I (P x)) ->
      Stable R I (∃ x, P x).
    Proof.
      intros. intros ? [[s' [[? ?] ?]] ?].
      exists x. apply H; split; eauto.
      eexists; eauto.
    Qed.

    Lemma StableWeaken : forall R I P1 P2 P3,
      Stable R I P3 ->
      ⊨ P1 ==>> P3 ->
      ⊨ P3 ==>> P2 ->
      ⊨ (R ⊚ P1) //\\ I ==>> P2.
    Proof.
      intros. intros [[? [? ?]] ?].
      apply H1.
      apply H0 in H2.
      apply H.
      split; auto.
      eexists; split; eauto.
    Qed.
    
    Lemma ConjStable {R I P Q}:
      Stable R I P -> Stable R I Q -> Stable R I (P //\\ Q).
    Proof.
      intros. intros ? [[? [[? ?] ?]] ?].
      split.
      - apply H. do 2 (eexists; eauto).
      - apply H0. do 2 (eexists; eauto).
    Qed.

    Lemma ConjStableWeaken {R I P Q}:
      ⊨ (R ⊚ (P //\\ Q)) //\\ I ==>> P ->
      ⊨ (R ⊚ (P //\\ Q)) //\\ I ==>> Q ->
      Stable R I (P //\\ Q).
    Proof.
      intros. intros ? ?.
      split; try apply H; try apply H0; auto.
    Qed.

    Lemma StableExtractPure {R I} {P:Prop} {Q}:
      (P -> Stable R I Q) ->
      Stable R I (⌜P⌝ //\\ Q).
    Proof.
      intros.
      intros ? [[s' [[? ?] ?]] ?].
      split; auto.
      apply H; auto.
      do 2 (eexists; eauto).
    Qed.

    Lemma EquivStable {R I}: forall P Q,
      (⊨ P <<==>> Q) -> Stable R I P -> Stable R I Q.
    Proof.
      intros. intros ? [[? [? ?]] ?].
      destruct (H s).
      destruct (H x).
      apply H4.
      apply H0.
      split; eauto.
      eexists. split; eauto.
    Qed.

    Lemma DisjStable {R I P Q}:
      Stable R I P ->
      Stable R I Q ->
      Stable R I (P \\// Q).
    Proof.
      intros. intros ? [[? [? ?]] ?].
      destruct H1.
      - left. apply H; split; auto. eexists; eauto.
      - right. apply H0; split; auto. eexists; eauto.
    Qed.

    Lemma APureStable {R I P}:
      Stable R I (⌜P⌝).
    Proof.
      intros. intros ? [[? [? ?]] ?].
      unfold APure in *. auto.
    Qed.

    Lemma ImplDisjFrame {P1 P3: @Assertion (@ProofState E F VE VF)} : forall P2,
      (⊨ P1 ==>> P2) ->
      ⊨ P1 \\// P3 ==>> P2 \\// P3.
    Proof.
      intros. intros ?.
      destruct H0.
      - left; apply H; auto.
      - right; auto.
    Qed.

    Lemma ImplDisjLeft {P1 P2 P3: @Assertion (@ProofState E F VE VF)}:
      (⊨ P1 ==>> P2) ->
      ⊨ P1 ==>> P2 \\// P3.
    Proof. intros ? ? ?. left; apply H; auto. Qed.

    Lemma ImplDisjRight {P1 P2 P3: @Assertion (@ProofState E F VE VF)}:
      (⊨ P1 ==>> P3) ->
      ⊨ P1 ==>> P2 \\// P3.
    Proof. intros ? ? ?. right; apply H; auto. Qed.
  
  End AssertionLemmas.


    Open Scope rg_relation_scope.
    Open Scope assertion_scope.

    Ltac inversion_step :=
      repeat match goal with
      (* Case with 5 arguments *)
      | H : Step ?x1 ?x2 ?x3 ?x4 ?x5 |- _ =>
          first [
            match type of x1 with ThreadEvent => inversion H; subst; clear H end |
            match type of x2 with ThreadEvent => inversion H; subst; clear H end |
            match type of x3 with ThreadEvent => inversion H; subst; clear H end |
            match type of x4 with ThreadEvent => inversion H; subst; clear H end |
            match type of x5 with ThreadEvent => inversion H; subst; clear H end
          ]
      (* Case with 4 arguments (common in Assertion.v) *)
      | H : Step ?x1 ?x2 ?x3 ?x4 |- _ =>
          first [
            match type of x1 with ThreadEvent => inversion H; subst; clear H end |
            match type of x2 with ThreadEvent => inversion H; subst; clear H end |
            match type of x3 with ThreadEvent => inversion H; subst; clear H end |
            match type of x4 with ThreadEvent => inversion H; subst; clear H end
          ]
      end.
    
    Ltac solve_conj_impl :=
      try exact ImplRefl;
      match goal with
      | |- _ -> ?P => intro; solve_conj_impl
      | |- forall x:?T, ?P => intro; solve_conj_impl
      (* | |- ⊨ ?P ==>> ?P => exact ImplRefl *)
      | |- ⊨ ?P1 //\\ ?P2 ==>> ?Q =>
        solve [ eapply ConjLeftImpl; solve_conj_impl ] ||
        solve [ eapply ConjRightImpl; solve_conj_impl ] ||
        solve [
          match Q with
          | ?Q1 //\\ ?Q2 => eapply ImplConj; solve_conj_impl
          | _ => fail
          end
        ]
      | _ => fail
      end.

    Ltac solve_conj_stable hint_db :=
      intros;
      match goal with
      | |- Stable _ _ ?P =>
        solve [ eauto with hint_db ] ||
        match P with
        | ?P1 //\\ ?P2 => apply ConjStable; solve_conj_stable hint_db
        | _ => fail
        end
      end.

    Ltac solve_stable hint_db :=
      intros;
      match goal with
      | |- Stable _ _ ?P =>
        solve [ eauto with hint_db ] ||
        match P with
        | ⌜?P⌝ => apply APureStable
        | ?P1 \\// ?P2 =>
            apply DisjStable; solve_stable hint_db
        | ?P1 //\\ ?P2 =>
            match P1 with
            | ⌜?P1⌝ =>
              apply StableExtractPure; intros; subst;
              solve_stable hint_db
            | _ =>
              first [
                apply ConjStable; solve_stable hint_db |
                apply ConjStableWeaken;
                (eapply StableWeaken;
                  [ typeclasses eauto with hint_db
                    | solve_conj_impl
                    | solve_conj_impl ])
              ]
            end
        | _ => fail
        end
      end.

    Ltac solve_no_error:=
      apply ImplTauto; intros ? H; destruct σ;
      inversion H; subst; inversion Herror.
  
End Assertions.



Module SinglePossState <: ProofState.
  Import Reg LinCCALBase LTSSpec Semantics.

  Record ProofStateSingle {E : Op.t} {F : Op.t} {VE : @LTS E} {VF : @LTS F} : Type :=
  {
    σ : State VE;
    ρ : State VF;
    π : tmap (@LinState F);
  }.

  Notation "( σ , ρ , π )" := (Build_ProofStateSingle _ _ _ _ σ ρ π).

  Definition ProofState {E F VE VF} : Type := @ProofStateSingle E F VE VF.

End SinglePossState.

Module AssertionsSingle.
  Module A := Assertions (SinglePossState).
  Export A.
  Export SinglePossState.

  Import Reg.
  Import LinCCALBase.
  Import LTSSpec.
  Import Semantics.

  Section AssertionDef.
    Context {E : Op.t}.
    Context {F : Op.t}.
    Context {VE : @LTS E}.
    Context {VF : @LTS F}.

    Definition LiftRelation_σ (Rσ : relation (State VE)) : @RGRelation _ _ VE VF :=
      fun x y => Rσ (σ x) (σ y) /\ ρ x = ρ y /\ π x = π y.
    
    Definition LiftRelation_ρ (Rρ : relation (State VF)) : @RGRelation _ _ VE VF :=
      fun x y => σ x = σ y /\ Rρ (ρ x) (ρ y) /\ π x = π y.
    
    Definition LiftRelation_π (Rπ : relation (tmap (@LinState F))) : @RGRelation _ _ VE VF :=
      fun x y => σ x = σ y /\ ρ x = ρ y /\ Rπ (π x) (π y).

    Definition Ginv t f : @RGRelation _ _ VE VF :=
      LiftRelation_π (fun π1 π2 => 
        TMap.find t π1 = None /\
        π2 = TMap.add t (ls_inv f) π1).

    Definition GINV t : @RGRelation _ _ VE VF :=
      fun x y => exists f, Ginv t f x y.

    Definition Gret t f ret : @RGRelation _ _ VE VF :=
      LiftRelation_π (fun π1 π2 => 
        TMap.find t π1 = Some (ls_linr f ret) /\
        π2 = TMap.remove t π1).

    Definition GRET t : @RGRelation _ _ VE VF :=
      fun x y => exists f ret, Gret t f ret x y.
    
    Definition APError : @Assertion (@ProofState _ _ VE VF) :=
      fun s => poss_steps (ρ s, π s) PossError.

    Definition PUpdate (G : @RGRelation _ _ VE VF) (ev : ThreadEvent) (P Q : Assertion) : Prop :=
      forall σ ρ π, P (σ, ρ, π) ->
      forall σ', Step VE ev σ σ' ->
      exists ρ' π', poss_steps (ρ, π) (ρ', π') /\ Q (σ', ρ', π')
        /\ G (σ, ρ, π) (σ', ρ', π').

    Definition PUpdateId (G : @RGRelation _ _ VE VF) (P Q : Assertion) : Prop :=
      forall σ ρ π, P (σ, ρ, π) ->
      exists ρ' π', poss_steps (ρ, π) (ρ', π') /\ Q (σ, ρ', π')
        /\ G (σ, ρ, π) (σ, ρ', π').
    
    Definition ALin (t : tid) (ls : LinState) : @Assertion (@ProofState _ _ VE VF) :=
      fun s => TMap.find t (π s) = Some ls.

  End AssertionDef.

  Notation "G ⊨ P [ ev ]⭆ Q" := (PUpdate G ev P Q) (at level 100) : assertion_scope.
  Notation "G ⊨ P ⭆ Q" := (PUpdateId G P Q) (at level 100) : assertion_scope.

  
  Section AssertionLemmas.
    Context {E : Op.t}.
    Context {F : Op.t}.
    Context {VE : @LTS E}.
    Context {VF : @LTS F}.

    Lemma PUpdateConseq {P Q P' Q' : @Assertion (@ProofState _ _ VE VF)} {ev} {G} :
      (⊨ P' ==>> P) ->
      (⊨ Q ==>> Q') ->
      (G ⊨ P [ ev ]⭆ Q) ->
      G ⊨ P' [ ev ]⭆ Q'.
    Proof.
      intros. intros ?; intros.
      apply H in H2.
      apply H1 in H2.
      apply H2 in H3 as (? & ?& ? & ? & ?).
      apply H0 in H4.
      eauto.
    Qed.
  End AssertionLemmas.

  Ltac pupdate_intros_atomic :=
    intros;
    intros σ1 ρ1 π1 Hpre σ2 Hstep;
    try destruct σ1, σ2;
    try inversion_step;
    (* this is the step taken by the encapsulated LTS *)
    (* do not clear it because information from the pre-condition
       could help reducing it to extract more conditions *)
    (* TODO: handle cases where this hypothesis is not named Hstep *)
    try (inversion Hstep; subst);
    try inversion_thread_event_eq;
    repeat match goal with
    | H : existT _ _ _ = existT _ _ _ |- _ =>
      dependent destruction H
    end.
  
  Ltac pupdate_start := do 2 eexists; split.

  Ltac try_pupdate_start tac :=
    first [
      pupdate_start; [idtac tac|] |
      idtac tac
    ].

  Ltac pupdate_finish :=
    first [
      pupdate_start; [apply rt_refl|] |
      apply rt_refl
    ].

  Ltac pupdate_forward t ev :=
    (* try_pupdate_start *)
    eapply rt_trans; [
      constructor;
      match ev with
      | InvEv ?op => eapply (Semantics.ps_inv t op); eauto
      | ResEv ?op ?ret => eapply (Semantics.ps_ret t op ret); eauto;
            try (rewrite PositiveMap.gss; auto)
      | _ => fail "Cannot recognize the event."
      end;
      try solve [ do 2 constructor; eauto ];
      try solve [ do 2 econstructor; eauto ]
    |].

End AssertionsSingle.


Module SetPossState <: ProofState.
  Import Reg LinCCALBase LTSSpec Semantics.

  Record ProofStateSet {E : Op.t} {F : Op.t} {VE : @LTS E} {VF : @LTS F} : Type :=
  {
    σ : State VE;
    Δ : AbstractConfig VF;
  }.

  Notation "( σ , ρ , π )" := (Build_ProofStateSet  _ _ _ _ σ (ac_singleton ρ π)).
  Notation "( σ , Δ )" := (Build_ProofStateSet  _ _ _ _ σ Δ).

  Definition ProofState {E F VE VF} : Type := @ProofStateSet E F VE VF.

  Section ProofStateSA.
    Context {E : Op.t} {F : Op.t} {VE : @LTS E} {VF : @LTS F}.
    Context {EJ : Join (State VE)} {ESA: @SeparationAlgebra _ EJ} {Eunit: @SeparationAlgebraUnit _ _ ESA}.
    Context {FJ : Join (State VF)} {FSA: @SeparationAlgebra _ FJ} {Funit: @SeparationAlgebraUnit _ _ FSA}.

    #[global] Instance PSS_Join : Join (@ProofState _ _ VE VF) :=
      fun s1 s2 s3 => join (σ s1) (σ s2) (σ s3) /\ join (Δ s1) (Δ s2) (Δ s3).
    Program Instance PSS_SA : SeparationAlgebra (@ProofState _ _ VE VF).
    Next Obligation.
      inversion H; subst.
      constructor; eauto.
      apply join_comm; auto.
    Qed.
    Next Obligation.
      inversion H; inversion H0; subst.
      pose proof join_assoc _ _ _ _ _ H1 H3 as [? [? ?]].
      pose proof join_assoc _ _ _ _ _ H2 H4 as [? [? ?]].
      exists (x, x0).
      split; constructor; auto.
    Defined.
    Program Instance PSS_unit : SeparationAlgebraUnit (@ProofState _ _ VE VF) PSS_SA := {| ue := (ue, ue) |}.
    Next Obligation.
      constructor; simpl; auto.
      apply ac_unit_join.
    Qed.
    Next Obligation.
      intros ? ? ?.
      inversion H; simpl in *.
      apply unit_spec in H0.
      apply (@unit_spec _ _ _ ac_unit) in H1.
      destruct n, n'. simpl in *. subst; auto.
    Defined.
  End ProofStateSA.
  
  Variant spec_union {E : Op.t} {F : Op.t} {VE : @LTS E} {VF : @LTS F}
   : @ProofState _ _ VE VF -> @ProofState _ _ VE VF -> @ProofState _ _ VE VF -> Prop :=
  | SpecUnion : forall σ (Δ1 Δ2 : AbstractConfig VF) (Hdomexact: Δ_domexact Δ1 Δ2),
      spec_union (σ, Δ1) (σ, Δ2) (σ, ac_union Δ1 Δ2 (Hdomexact := Hdomexact)).
  
End SetPossState.


Module AssertionsSet.
  Module A := Assertions (SetPossState).
  Export A.
  Export SetPossState.

  Import Reg.
  Import LinCCALBase.
  Import LTSSpec.
  Import Semantics.
  Import TPSimulation.

  Open Scope ac_scope.

  Section AssertionDef.
    Context {E : Op.t}.
    Context {F : Op.t}.
    Context {VE : @LTS E}.
    Context {VF : @LTS F}.

    Definition SpecUnion (P Q : Assertion) : @Assertion (@ProofState _ _ VE VF) :=
      fun s => exists s1 s2, P s1 /\ Q s2 /\ spec_union s1 s2 s.

    Definition LiftRelation_σ (Rσ : relation (State VE)) : @RGRelation _ _ VE VF :=
      fun x y => Rσ (σ x) (σ y) /\ Δ x = Δ y.

    Definition LiftRelation_Δ (RΔ : relation (AbstractConfig VF)) : @RGRelation _ _ VE VF :=
      fun x y => σ x = σ y /\ RΔ (Δ x) (Δ y).

    Definition Ginv t f : @RGRelation _ _ VE VF :=
      LiftRelation_Δ (fun Δ1 Δ2 => 
        (forall ρ π, Δ1 ρ π -> TMap.find t π = None) /\
        Δ2 ≡ (ac_inv Δ1 t f)).

    Definition GINV t : @RGRelation _ _ VE VF :=
      fun x y => exists f, Ginv t f x y.

    Definition Gret t f ret : @RGRelation _ _ VE VF :=
      LiftRelation_Δ (fun Δ1 Δ2 => 
        (forall ρ π, Δ1 ρ π -> TMap.find t π = Some (ls_linr f ret)) /\
        Δ2 ≡ (ac_res Δ1 t)).

    Definition GRET t : @RGRelation _ _ VE VF :=
      fun x y => exists f ret, Gret t f ret x y.
    
    Variant APError : @Assertion (@ProofState _ _ VE VF) :=
    | APErrorSome s ρ π : Δ s ρ π -> poss_steps (ρ, π) PossError -> APError s.

    Definition PUpdate (G : @RGRelation _ _ VE VF) (ev : ThreadEvent) (P Q : Assertion) : Prop :=
      forall σ Δ, P (σ, Δ) ->
      forall σ', Step VE ev σ σ' ->
      exists Δ', (Δ' ⊆ ac_steps Δ)%AbstractConfig
        /\ Q (σ', Δ') /\ G (σ, Δ) (σ', Δ').

    Definition PUpdateId (G : @RGRelation _ _ VE VF) (P Q : Assertion) : Prop :=
      forall σ Δ, P (σ, Δ) ->
      exists Δ', (Δ' ⊆ ac_steps Δ)%AbstractConfig
        /\ Q (σ, Δ') /\ G (σ, Δ) (σ, Δ').
    
    Definition ALin (t : tid) (ls : LinState) : @Assertion (@ProofState _ _ VE VF) :=
      fun s => forall ρ π, Δ s ρ π -> TMap.find t π = Some ls.
  
    Definition ALin' t ls : @Assertion (@ProofState _ _ VE VF) :=
      fun s => exists ρ, ac_equiv (Δ s) (ac_singleton ρ (LinCCAL.TMap.add t ls (LinCCAL.TMap.Leaf _))).

    Definition Aρ ρ : @Assertion (@ProofState _ _ VE VF) :=
      fun s => ac_equiv (Δ s) (ac_singleton ρ (LinCCAL.TMap.Leaf _)).

    Lemma ALin_equiv : forall s1 s2 t ls,
      ac_equiv (Δ s1) (Δ s2) ->
      ALin t ls s1 -> ALin t ls s2.
    Proof.
      intros. intros ? ? ?.
      apply H in H1; eauto.
    Qed.

  End AssertionDef.

  Notation "G ⊨ P [ ev ]⭆ Q" := (PUpdate G ev P Q) (at level 100) : assertion_scope.
  Notation "G ⊨ P ⭆ Q" := (PUpdateId G P Q) (at level 100) : assertion_scope.
  Notation "P ⨁ Q" := (SpecUnion P Q) (at level 30) : assertion_scope.
  
  Section AssertionLemmas.
    Context {E : Op.t}.
    Context {F : Op.t}.
    Context {VE : @LTS E}.
    Context {VF : @LTS F}.

    Lemma PUpdateConseq {P Q P' Q' : @Assertion (@ProofState _ _ VE VF)} {ev} {G} :
      (⊨ P' ==>> P) ->
      (⊨ Q ==>> Q') ->
      (G ⊨ P [ ev ]⭆ Q) ->
      G ⊨ P' [ ev ]⭆ Q'.
    Proof.
      intros. intros ?; intros.
      apply H in H2.
      apply H1 in H2.
      apply H2 in H3 as (? & ?& ? & ?).
      apply H0 in H4.
      eauto.
    Qed.
  End AssertionLemmas.


  Ltac pupdate_intros_atomic :=
    intros;
    intros σ1 Δ1 Hpre σ2 Hstep;
    try destruct σ1, σ2;
    try inversion_step;
    (* this is the step taken by the encapsulated LTS *)
    (* do not clear it because information from the pre-condition
      could help reducing it to extract more conditions *)
    (* TODO: handle cases where this hypothesis is not named Hstep *)
    try (inversion Hstep; subst);
    try inversion_thread_event_eq;
    repeat match goal with
    | H : existT _ _ _ = existT _ _ _ |- _ =>
      dependent destruction H
    end.
  
  Ltac pupdate_start := eexists; split.

  Ltac try_pupdate_start tac :=
    first [
      pupdate_start; [idtac tac|] |
      idtac tac
    ].

  Ltac pupdate_finish :=
    first [
      pupdate_start; [apply rt_refl|] |
      apply rt_refl
    ].

  Ltac pupdate_forward t ev :=
    (* try_pupdate_start *)
    eapply rt_trans; [
      constructor;
      match ev with
      | InvEv ?op => eapply (Semantics.ps_inv t op); eauto
      | ResEv ?op ?ret => eapply (Semantics.ps_ret t op ret); eauto;
            try (rewrite PositiveMap.gss; auto)
      | _ => fail "Cannot recognize the event."
      end;
      try solve [ do 2 constructor; eauto ];
      try solve [ do 2 econstructor; eauto ]
    |].
    
  Ltac pupdate_trylin_from Hposs :=
    unshelve eapply (ac_trylin_subset_steps _ _ _ _ _ Hposs);
    match goal with |- ?G => 
      match type of G with
      | Prop => idtac
      | _ => shelve end
    end.

End AssertionsSet.