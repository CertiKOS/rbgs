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

    (* Definition ProofState : Type := State VE * State VF * tmap (@LinState F). *)

    Definition Assertion : Type := @ProofState E F VE VF -> Prop.
        
    Definition Conj (P Q : Assertion) : Assertion := fun s => P s /\ Q s.
    Definition Disj (P Q : Assertion) : Assertion := fun s => P s \/ Q s.
    Definition Imply (P Q : Assertion) : Assertion := fun s => P s -> Q s.
    Definition Neg P : Assertion := fun s => ~P s.

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

    Definition GId : RGRelation := fun x y => x = y.

    Definition ANoError (ev : ThreadEvent) : Assertion :=
      fun s => ~ Error VE ev (σ s).

    Definition APure (P : Prop) : Assertion :=
      fun _ => P.
  End AssertionDef.
  

  Delimit Scope rg_relation_scope with RGRelation.
  Bind Scope rg_relation_scope with RGRelation.
  
  Notation "R ⊆ S" := (Subset R S) (at level 70) : rg_relation_scope.
  Notation "R ∪ S" := (Union R S) (at level 50) : rg_relation_scope.
  Notation "R ∩ S" := (Inter R S) (at level 40) : rg_relation_scope.


  Delimit Scope assertion_scope with Assertion.
  Bind Scope assertion_scope with Assertion.
  
  Notation "P //\\ Q" := (Conj P Q) (at level 40) : assertion_scope.
  Notation "P \\// Q" := (Disj P Q) (at level 50) : assertion_scope.
  Notation "P ==>> Q" := (Imply P Q) (at level 70) : assertion_scope.
  Notation "P <<==>> Q" := (Imply P Q //\\ Imply Q P)%Assertion (at level 80) : assertion_scope.
  Notation "R ⊚ P" := (ComposeA P R) (at level 30) : assertion_scope.
  Notation "R ○ S" := (ComposeR S R) (at level 30) : assertion_scope.
  Notation "⊨ P" := (forall s, P s) (at level 100) : assertion_scope.
  (* \ulcorner \urcorner *)
  Notation "⌜ P ⌝" := (APure P) (at level 1, format "⌜ P ⌝") : assertion_scope.
  Notation "!! P" := (Neg P) (at level 1) : assertion_scope.
  

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

    Lemma ImplRefl {P:@Assertion _ _ VE VF}: ⊨ P ==>> P.
    Proof. intros. intros ?. auto. Qed.

    Lemma ImplTauto {P Q : @Assertion _ _ VE VF} : (⊨ Q) -> ⊨ P ==>> Q.
    Proof. intros. intros ?. auto. Qed.

    Lemma ImplTrans {P Q R : @Assertion _ _ VE VF} : (⊨ P ==>> Q) -> (⊨ Q ==>> R) -> ⊨ P ==>> R.
    Proof. intros. intros ?. apply H0, H; auto. Qed.


    Lemma ConjLeftImpl {P1 P2 P3: @Assertion _ _ VE VF}:
      (⊨ P1 ==>> P3) ->
      ⊨ P1 //\\ P2 ==>> P3.
    Proof. intros ? ? [? ?]; apply H; auto. Qed.

    Lemma ConjRightImpl {P1 P2 P3 : @Assertion _ _ VE VF}:
      (⊨ P2 ==>> P3) ->
      ⊨ P1 //\\ P2 ==>> P3.
    Proof. intros ? ? [? ?]; apply H; auto. Qed.

    Definition Stable (R : @RGRelation _ _ VE VF) I P := ⊨ (R ⊚ P) //\\ I ==>> P.

    Lemma ConjStable {R I P Q}:
      Stable R I P -> Stable R I Q -> Stable R I (P //\\ Q).
    Proof.
      intros. intros ? [[? [[? ?] ?]] ?].
      split.
      - apply H. do 2 (eexists; eauto).
      - apply H0. do 2 (eexists; eauto).
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

    Lemma ImplDisjFrame {P1 P3: @Assertion _ _ VE VF} : forall P2,
      (⊨ P1 ==>> P2) ->
      ⊨ P1 \\// P3 ==>> P2 \\// P3.
    Proof.
      intros. intros ?.
      destruct H0.
      - left; apply H; auto.
      - right; auto.
    Qed.

    Lemma ImplDisjLeft {P1 P2 P3: @Assertion _ _ VE VF}:
      (⊨ P1 ==>> P2) ->
      ⊨ P1 ==>> P2 \\// P3.
    Proof. intros ? ? ?. left; apply H; auto. Qed.

    Lemma ImplDisjRight {P1 P2 P3: @Assertion _ _ VE VF}:
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
      match goal with
      | |- _ -> ?P => intro; solve_conj_impl
      | |- forall x:?T, ?P => intro; solve_conj_impl
      | |- ⊨ ?P ==>> ?P => exact ImplRefl
      | |- ⊨ ?P1 //\\ ?P2 ==>> ?Q =>
        solve [ apply ConjLeftImpl; solve_conj_impl ] ||
        solve [ apply ConjRightImpl; solve_conj_impl ]
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
    
    Definition APError : @Assertion _ _ VE VF :=
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
    
    Definition ALin (t : tid) (ls : LinState) : @Assertion _ _ VE VF :=
      fun s => TMap.find t (π s) = Some ls.
  
  End AssertionDef.

  Notation "G ⊨ P [ ev ]⭆ Q" := (PUpdate G ev P Q) (at level 100) : assertion_scope.
  Notation "G ⊨ P ⭆ Q" := (PUpdateId G P Q) (at level 100) : assertion_scope.

  
  Section AssertionLemmas.
    Context {E : Op.t}.
    Context {F : Op.t}.
    Context {VE : @LTS E}.
    Context {VF : @LTS F}.

    Lemma PUpdateConseq {P Q P' Q' : @Assertion _ _ VE VF} {ev} {G} :
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
    
    Variant APError : @Assertion _ _ VE VF :=
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
    
    Definition ALin (t : tid) (ls : LinState) : @Assertion _ _ VE VF :=
      fun s => forall ρ π, Δ s ρ π -> TMap.find t π = Some ls.
  
  End AssertionDef.

  Notation "G ⊨ P [ ev ]⭆ Q" := (PUpdate G ev P Q) (at level 100) : assertion_scope.
  Notation "G ⊨ P ⭆ Q" := (PUpdateId G P Q) (at level 100) : assertion_scope.

  
  Section AssertionLemmas.
    Context {E : Op.t}.
    Context {F : Op.t}.
    Context {VE : @LTS E}.
    Context {VF : @LTS F}.

    Lemma PUpdateConseq {P Q P' Q' : @Assertion _ _ VE VF} {ev} {G} :
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