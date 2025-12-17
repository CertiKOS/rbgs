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
Require Import TPSimulation.
Require Import RGILogic.
Require Import Specs.


Module TreiberStackImpl.
  Import LinCCALBase.
  Import LTSSpec.
  Import Lang.
  Import AssertionsSingle.
  Import RGILogic.
  Import TPSimulation.
  Import AtomicLTS TryStackSpec StackSpec.
  Import (coercions, canonicals, notations) Sig.
  Import (notations) LinCCAL.
  Import (canonicals) Sig.Plus.

  Open Scope prog_scope.

  Context {A : Type}.

  Definition E : layer_interface :=
  {|
    li_sig := ETryStack A;
    li_lts := VTryStack;
    li_init := Idle nil;
  |}.
  
  Definition F : layer_interface :=
  {|
    li_sig := EStack A;
    li_lts := VStack;
    li_init := Idle nil
  |}.
  
  Definition push_impl (v : A) : Prog (li_sig E) unit :=
    Do {
      TryStackSpec.push v >= succ => Ret (match succ with | FAIL => inl tt | _ => inr tt end)
    } Loop.

  Definition pop_impl : Prog (li_sig E) (option A) :=
    Do {
      TryStackSpec.pop >= succ => Ret (match succ with | FAIL => inl tt | OK v => inr v end)
    } Loop.

  Definition assertion := @Assertion _ _ (li_lts E) (li_lts F).
  Definition rg_relation := @RGRelation _ _ (li_lts E) (li_lts F).

  Open Scope rg_relation_scope.
  Open Scope assertion_scope.

  Definition I : assertion := fun s =>
    ρ s = Idle (state (σ s)).

  Definition G t : rg_relation := 
      (* (G_lock t ∪ G_unlock t ∪ G_id t) ∩ *)
        fun s1 s2 => forall t', t <> t'
          -> TMap.find t' (π s1) = TMap.find t' (π s2).

  Definition R t : rg_relation :=
    fun s1 s2 =>
      (* (OwnedBy t s1 -> OwnedBy t s2 /\ snd (σ s1) = snd (σ s2)) /\ *)
      (TMap.find t (π s1) = TMap.find t (π s2)).

  Lemma Istable {t} : Stable (R t) I I.
  Proof. unfold Stable. apply ConjRightImpl, ImplRefl. Qed.
  
  Lemma ALinstable {t ls}: Stable (R t) I (ALin t ls).
  Proof.
    unfold Stable, ALin, R.
    intros ? [[? [? ?]] ?].
    rewrite <- H0. auto.
  Qed.

  Create HintDb stableDB.
  Hint Resolve
    Istable
    ALinstable
  : stableDB.

  Lemma IGinv : forall t f, ⊨ Ginv t f ⊚ I ==>> I //\\ ALin t (Semantics.ls_inv f).
  Proof.
    unfold I, ALin.
    intros ? ? [? ?] [[? ?] [? [? [? [? ?]]]]]; simpl in *; subst.
    split; auto; simpl in *.
    rewrite PositiveMap.gss; auto.
  Qed.

  Lemma IGret : forall t f ret,
    ⊨ Gret t f ret ⊚ (I //\\ ALin t (Semantics.ls_linr f ret)) ==>> I.
  Proof.
    unfold I, ALin, Gret, LiftRelation_π.
    intros. intros [? [[? ?] ?]].
    destruct H1 as [? [? [? ?]]].
    destruct s, x; simpl in *; subst. auto.
  Qed.

  Program Definition Mtreiber_stack : layer_implementation E F := {|
    li_impl m :=
      match m with
      | push v => push_impl v
      | pop => pop_impl
      end
  |}.
  Next Obligation.
    eapply RGILogic.soundness with (R:=R) (G:=G) (I:=I).
    (* valid RG *)
    {
      constructor.
      unfold R. intros.
      rewrite H. tauto.
    }
    (* G ⊆ R *)
    {
      unfold G, R.
      intros. intros ? ? ?.
      destruct H0; eauto.
      unfold GINV, Ginv, GRET, Gret, GId, LiftRelation_π in H0;
      destruct H0 as [[? | ?] | ?]; eauto.
      - destruct H0 as (? & ? & ? & ? & ?).
        rewrite H3.
        rewrite PositiveMap.gso; try tauto; auto.
      - destruct H0 as (? & ? & ? & ? & ? & ?).
        rewrite H3.
        rewrite PositiveMap.gro; try tauto; auto.
      - subst; auto.
    }
    intros t; destruct f.
    (* push *)
    {
      (* pre-condition *)
      exists (I //\\ ALin t (Semantics.ls_inv (push v))).
      (* post-condition *)
      exists (fun ret => I //\\ ALin t (Semantics.ls_linr (push v) ret)).
      constructor;
      try solve_conj_impl;
      try solve_conj_stable stableDB;
      try apply IGinv; try apply IGret.
      {
        unfold ALin. intros.
        destruct H; auto.
      }
      simpl. unfold push_impl.
      (* loop *)
      apply provable_doloop;
      try solve_conj_impl;
      try solve_conj_stable stableDB.
      (* loop body *)
      eapply provable_vis_safe with
        (P':=I //\\ ALin t (Semantics.ls_inv (push v)))
        (Q':=fun ret => I //\\ match ret with
                        | OK _ => ALin t (Semantics.ls_linr (push v) tt)
                        | FAIL => ALin t (Semantics.ls_inv (push v))
                        end);
      try solve_conj_impl;
      try solve_conj_stable stableDB;
      [solve_no_error| destruct a; solve_conj_stable stableDB | | | ].
      (* inv *)
      {
        intros; intros σ1 ρ1 π1 Hpre σ2 Hstep;
        try destruct σ1, σ2; inversion Hstep; subst.
        inversion Hstep0; subst; try inversion H3.
        do 2 eexists. split; [apply rt_refl|]. split.
        - destruct Hpre. unfold I in *; simpl in *; subst; split; auto.
        - unfold G; intros; simpl; auto.
      }
      (* res *)
      {
        intros; intros σ1 ρ1 π1 Hpre σ2 Hstep;
        inversion Hstep; subst; clear Hstep;
        dependent destruction H2.
        inversion Hstep0; subst; try inversion H3.
        - dependent destruction H1.
          destruct Hpre. unfold I in H. simpl in *; subst.
          exists (Idle (v0 :: s1)%list).
          exists (TMap.add t (Semantics.ls_linr (push v0) tt) (TMap.add t (Semantics.ls_lini (push v0)) π1)).
          do 2 try split.
          + eapply rt_trans; constructor.
            * eapply Semantics.ps_inv; eauto.
              do 2 constructor.
            * eapply Semantics.ps_ret; eauto;
              [| rewrite PositiveMap.gss; auto].
              do 2 constructor.
          + split; unfold I, ALin; simpl; auto.
            rewrite PositiveMap.gss; auto.
          + unfold G. simpl. intros.
            do 2 (rewrite PositiveMap.gso; auto).
        - dependent destruction H1.
          do 2 eexists; split; [apply rt_refl|].
          split.
          + destruct Hpre; unfold ALin, I in *; simpl in *; split; auto.
          + unfold G. simpl. auto.
      }
      (* return *)
      intros.
      eapply provable_ret_safe; destruct ret;
      try solve_conj_impl;
      try solve_conj_stable stableDB;
      try apply ImplRefl.
    }
    (* pop *)
    {
      (* pre-condition *)
      exists (I //\\ ALin t (Semantics.ls_inv pop)).
      (* post-condition *)
      exists (fun ret => I //\\ ALin t (Semantics.ls_linr pop ret)).
      constructor;
      try solve_conj_impl;
      try solve_conj_stable stableDB;
      try apply IGinv; try apply IGret.
      {
        unfold ALin. intros.
        destruct H; auto.
      }
      simpl. unfold pop_impl.
      (* loop *)
      apply provable_doloop;
      try solve_conj_impl;
      try solve_conj_stable stableDB.
      (* loop body *)
      eapply provable_vis_safe with
        (P':=I //\\ ALin t (Semantics.ls_inv pop))
        (Q':=fun ret => I //\\ match ret with
                        | OK v => ALin t (Semantics.ls_linr pop v)
                        | FAIL => ALin t (Semantics.ls_inv pop)
                        end);
      try solve_conj_impl;
      try solve_conj_stable stableDB;
      [solve_no_error| destruct a; solve_conj_stable stableDB | | | ].
      (* inv *)
      {
        intros; intros σ1 ρ1 π1 Hpre σ2 Hstep;
        try destruct σ1, σ2; inversion Hstep; subst.
        inversion Hstep0; subst; try inversion H3.
        do 2 eexists. split; [apply rt_refl|]. split.
        - destruct Hpre. unfold I in *; simpl in *; subst; split; auto.
        - unfold G; intros; simpl; auto.
      }
      (* res *)
      {
        intros; intros σ1 ρ1 π1 Hpre σ2 Hstep;
        inversion Hstep; subst; clear Hstep;
        dependent destruction H2.
        inversion Hstep0; subst; try inversion H3.
        - dependent destruction H0.
          destruct Hpre. unfold I in H. simpl in *; subst.
          exists (Idle nil).
          exists (TMap.add t (Semantics.ls_linr pop None) (TMap.add t (Semantics.ls_lini pop) π1)).
          do 2 try split.
          + eapply rt_trans; constructor.
            * eapply Semantics.ps_inv; eauto.
              do 2 constructor.
            * eapply Semantics.ps_ret; eauto;
              [| rewrite PositiveMap.gss; auto].
              do 2 constructor.
          + split; unfold I, ALin; simpl; auto.
            rewrite PositiveMap.gss; auto.
          + unfold G. simpl. intros.
            do 2 (rewrite PositiveMap.gso; auto).
        - dependent destruction H0.
          destruct Hpre. unfold I in H. simpl in *; subst.
          exists (Idle s2).
          exists (TMap.add t (Semantics.ls_linr pop (Some v)) (TMap.add t (Semantics.ls_lini pop) π1)).
          do 2 try split.
          + eapply rt_trans; constructor.
            * eapply Semantics.ps_inv; eauto.
              do 2 constructor.
            * eapply Semantics.ps_ret; eauto;
              [| rewrite PositiveMap.gss; auto].
              do 2 constructor.
          + split; unfold I, ALin; simpl; auto.
            rewrite PositiveMap.gss; auto.
          + unfold G. simpl. intros.
            do 2 (rewrite PositiveMap.gso; auto).
        - dependent destruction H0.
          do 2 eexists; split; [apply rt_refl|].
          split.
          + destruct Hpre; unfold ALin, I in *; simpl in *; split; auto.
          + unfold G. simpl. auto.
      }
      (* return *)
      intros.
      eapply provable_ret_safe; destruct ret;
      try solve_conj_impl;
      try solve_conj_stable stableDB;
      try apply ImplRefl.
    }
    (* initial *)
    { unfold I. auto. }
  Defined.

  Print Assumptions Mtreiber_stack.
End TreiberStackImpl.