Require Import FMapPositive.
Require Import Relation_Operators Operators_Properties.
Require Import Coq.PArith.PArith.
Require Import Coq.Program.Equality.
Require Import Lia.

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


Module FAIImpl.
  Import LinCCALBase.
  Import LTSSpec.
  Import Lang.
  Import AssertionsSingle.
  Import RGILogic.
  Import TPSimulation.
  Import AtomicLTS FAISpec LockSpec RegSpec.
  Import (coercions, canonicals, notations) Sig.
  Import (notations) LinCCAL.
  Import (canonicals) Sig.Plus.
  Open Scope prog_scope.

  Definition E : layer_interface :=
  {|
    li_sig := Sig.Plus.omap ELock (EReg nat);
    li_lts := tens_lts VLock VReg;
    li_init := (Idle Unlocked, Idle O);
  |}.
  
  Definition F : layer_interface :=
  {|
    li_sig := EFAI;
    li_lts := VFAI;
    li_init := Idle O
  |}.

  Definition fai_impl : Prog (li_sig E) nat :=
    inl acq >= _ =>
    inr get >= c =>
    inr (set (S c)) >= _ =>
    inl rel >= _ =>
    Ret c.

  Definition assertion := @Assertion _ _ (li_lts E) (li_lts F).
  Definition rg_relation := @RGRelation _ _ (li_lts E) (li_lts F).

  Open Scope rg_relation_scope.
  Open Scope assertion_scope.

  Definition I : assertion :=
    fun s => forall l r, σ s = (l, r) -> ρ s = Idle (state r).

  Definition NotOwned : assertion :=
    fun s => state (fst (σ s)) = Unlocked.
  
  Definition OwnedBy t : assertion :=
    fun s => state (fst (σ s)) = Locked t.
  
  Definition NotOwnedBy t : assertion :=
    fun s => state (fst (σ s)) <> Locked t.

  Lemma OwnedByExclude : forall t1 t2 s,
    t1 <> t2 -> OwnedBy t2 s -> NotOwnedBy t1 s.
  Proof.
    unfold OwnedBy, NotOwnedBy.
    intros. intros ?. congruence.
  Qed.

  Lemma OwnedByIsOwned t : forall s, OwnedBy t s -> NotOwned s -> False.
  Proof.
    unfold OwnedBy, NotOwned.
    intros. congruence.
  Qed.

  Definition RegVal v : assertion :=
    fun s => snd (σ s) = v.
  
  Definition G_lock t : rg_relation := 
    fun s1 s2 => NotOwned s1 /\ OwnedBy t s2 /\ snd (σ s1) = snd (σ s2).
  
  Definition G_unlock t : rg_relation :=
    fun s1 s2 => OwnedBy t s1 /\ NotOwned s2 /\ snd (σ s1) = snd (σ s2).
  
  (* Definition G_inc t : rg_relation :=
    fun s1 s2 => OwnedBy t s1 /\ exists v, RegVal v s1 /\ RegVal (S v) s2. *)

  Definition G_id t : rg_relation :=
    fun s1 s2 => state (fst (σ s1)) = state (fst (σ s2))
                  /\ (NotOwnedBy t s1 -> snd (σ s1) = snd (σ s2)).
  
  Definition G t : rg_relation := (G_lock t ∪ G_unlock t ∪ G_id t)
                              ∩ fun s1 s2 => forall t', t <> t'
                                  -> TMap.find t' (π s1) = TMap.find t' (π s2).

  Definition R t : rg_relation :=
    fun s1 s2 => (OwnedBy t s1 -> OwnedBy t s2 /\ snd (σ s1) = snd (σ s2))
                  /\ (TMap.find t (π s1) = TMap.find t (π s2)).

  Lemma Istable {t} : Stable (R t) I I.
  Proof. unfold Stable. apply ConjRightImpl. apply ImplRefl. Qed.
  
  Lemma OwnedBystable {t} : Stable (R t) I (OwnedBy t).
  Proof.
    unfold Stable.
    intros ? [[? [? ?]] ?].
    unfold R in *. tauto.
  Qed.

  Lemma ALinstable {t ls}: Stable (R t) I (ALin t ls).
  Proof.
    unfold Stable, ALin, R.
    intros ? [[? [? [? ?]]] ?].
    rewrite <- H1. auto.
  Qed.

  Lemma OwnedRegStable {t v} : Stable (R t) I (OwnedBy t //\\ RegVal v).
  Proof.
    unfold Stable, RegVal, R.
    intros ? [[? [[? ?] [? ?]]] ?].
    apply H1 in H as [? ?].
    split; auto. rewrite <- H4; auto.
  Qed.

  Create HintDb stableDB.
  Hint Resolve Istable OwnedBystable ALinstable OwnedRegStable : stableDB.
  
  Program Definition Mfai : layer_implementation E F :=
  {| li_impl fai := fai_impl |}.
  Next Obligation.
    eapply RGILogic.soundness with (R:=R) (G:=G) (I:=I).
    (* valid RG *)
    {
      constructor.
      unfold R. intros.
      destruct H. rewrite H1. tauto.
    }
    (* G ⊆ R *)
    {
      unfold G, R.
      intros. intros ? ? ?.
      do 2 destruct H0.
      - split; auto.
        do 2 destruct H0; try tauto.
        + destruct H0. intros. exfalso. eapply OwnedByIsOwned; eauto.
        + destruct H0. intros. eapply OwnedByExclude in H3; eauto. congruence.
        + intros. 
          pose proof H3 as H3'.
          eapply OwnedByExclude in H3; eauto.
          unfold OwnedBy in *. rewrite H0 in *. tauto.
      - destruct H0.
        + unfold GINV, Ginv, LiftRelation_π in *.
          destruct H0 as (? & ? & ? & ? & ?). unfold OwnedBy.
          rewrite H0, H3. split; auto.
          rewrite PositiveMap.gso; try tauto; auto.
        + unfold Gret, LiftRelation_π in *.
          destruct H0 as (? & ? & ? & ? & ? & ?). unfold OwnedBy.
          rewrite H0, H3. split; auto.
          rewrite PositiveMap.gro; try tauto; auto.
      - destruct H0; subst. auto.
    }
    (* method provable *)
    {
      intros t.
      destruct f.
      (* pre-condition *)
      exists (I //\\ ALin t (Semantics.ls_inv fai)).
      (* post-condition *)
      exists (fun ret => I //\\ ALin t (Semantics.ls_linr fai ret)).
      constructor;
      try solve_conj_impl;
      try solve_conj_stable stableDB.
      {
        unfold I, ALin;
        intros ? [? [? [? [? [? ?]]]]].
        split; auto.
        - rewrite H0, H1 in *; intros; eauto.
        - destruct s; simpl in *; rewrite H3.
          apply PositiveMap.gss.
      }
      {
        unfold I, ALin, Gret, LiftRelation_π.
        intros. intros [? [[? ?] ?]].
        destruct H1 as [? [? [? ?]]].
        destruct s, x; simpl in *; subst. auto.
      }
      {
        unfold ALin. intros.
        destruct H; auto.
      }
      (* hoare triple *)
      unfold fai_impl.
      (* acq *)
      eapply provable_vis_safe with
        (P' := I //\\ ALin t (Semantics.ls_inv fai))
        (Q' := fun _ => I //\\ ALin t (Semantics.ls_inv fai) //\\ OwnedBy t);
        try solve_conj_impl;
        try solve_conj_stable stableDB;
        [solve_no_error| | |intros _].
      (* inv *)
      {
        pupdate_intros.
        do 2 eexists. split; [apply rt_refl|].
        split.
        - unfold I, ALin in *.
          destruct Hpre.
          split; simpl in *; auto.
          inversion 1; subst.
          eapply H; eauto.
        - split; simpl; auto.
          right. unfold G_id. simpl; auto.
      }
      (* res *)
      {
        pupdate_intros.
        do 2 eexists. split; [apply rt_refl|].
        split.
        - unfold I, ALin, OwnedBy in *.
          destruct Hpre.
          split; simpl in *; auto.
          split; simpl in *; auto.
          inversion 1; subst.
          eapply H; eauto.
        - split; simpl; auto.
          left; left.
          unfold G_lock, NotOwned, OwnedBy; simpl; auto.
      }

      (* get *)
      eapply provable_vis_safe with
        (P' := I //\\ ALin t (Semantics.ls_inv fai) //\\ OwnedBy t)
        (Q' := fun c => I //\\ ALin t (Semantics.ls_inv fai) //\\ (OwnedBy t //\\ RegVal (Idle c)));
        try solve_conj_impl;
        try solve_conj_stable stableDB;
        [solve_no_error| | |intros c].
      (* inv *)
      {
        pupdate_intros.
        do 2 eexists. split; [apply rt_refl|].
        split.
        - destruct Hpre as [[? ?] ?].
          split; auto.
          split; auto.
          unfold I in *. simpl in *.
          inversion 1; intros; subst; simpl.
          apply (H _ _ eq_refl).
        - split; auto.
          right. split; auto. 
          destruct Hpre. congruence.
      }
      (* res *)
      {
        pupdate_intros.
        do 2 eexists. split; [apply rt_refl|].
        split.
        - destruct Hpre as [[? ?] ?].
          split.
          + split; auto.
            unfold I in *; simpl in *.
            inversion 1; intros; subst; simpl.
            apply (H _ _ eq_refl).
          + split; auto.
            unfold RegVal; simpl; auto.
        - split; auto.
          right. split; auto.
          destruct Hpre; congruence.
      }

      eapply provable_vis_safe with
        (P' := (I //\\ ALin t (Semantics.ls_inv fai)) //\\ (OwnedBy t //\\ RegVal (Pending c t (set (S c)))))
        (Q' := fun _ => (I //\\ ALin t (Semantics.ls_linr fai c)) //\\ OwnedBy t);
        try solve_conj_impl;
        try solve_conj_stable stableDB;
        [| | |intros _].
      (* safe *)
      {
        do 2 apply ConjRightImpl.
        intros ? ? ?.
        inversion H; subst.
        destruct σ.
        inversion H0; subst.
        simpl in *; congruence.
      }
      (* inv *)
      {
        pupdate_intros.
        do 2 eexists. split; [apply rt_refl|].
        split.
        - destruct Hpre as [[? ?] [? ?]].
          do 2 (split; auto).
          + unfold I in *; simpl in *.
            inversion 1; intros; subst.
            apply (H _ _ eq_refl).
          + inversion H2; subst.
            unfold RegVal in *; simpl in *; auto.
        - split; auto.
          right. split; auto. 
          destruct Hpre as [? [? ?]]. congruence.
      }
      (* res *)
      {
        pupdate_intros.
        exists (Idle (S c)), (TMap.add t (Semantics.ls_linr fai c) (TMap.add t (Semantics.ls_lini fai) π1)).
        destruct Hpre as [[? ?] [? ?]].
        inversion H2; subst.
        specialize (H _ _ eq_refl).
        simpl in H; subst.
        inversion H0; subst.
        do 2 try split.
        - eapply rt_trans; constructor.
          + eapply Semantics.ps_inv; eauto.
            do 2 constructor.
          + eapply Semantics.ps_ret; eauto;
            [| rewrite PositiveMap.gss; auto].
            do 2 constructor.
        - unfold I, ALin, RegVal.
          split; auto. split.
          + simpl; inversion 1; subst. auto.
          + simpl. rewrite PositiveMap.gss. auto.
        - split.
          + right. split; auto. congruence.
          + simpl; intros.
            do 2 (rewrite PositiveMap.gso; auto).
      }

      eapply provable_vis_safe with
        (P' := (I //\\ ALin t (Semantics.ls_linr fai c)) //\\ OwnedBy t)
        (Q' := fun _ => I //\\ ALin t (Semantics.ls_linr fai c));
        try solve_conj_impl;
        try solve_conj_stable stableDB;
        [| | |intros _].
      (* safe *)
      {
        apply ConjRightImpl.
        intros ? ? ?.
        inversion H; subst.
        destruct σ.
        inversion H0; subst.
        inversion Herror; subst.
        - simpl in *; congruence.
        - inversion H2; congruence.
      }
      (* inv *)
      {
        pupdate_intros.
        do 2 eexists. split; [apply rt_refl|].
        split.
        - destruct Hpre as [[? ?] ?].
          do 2 (split; auto).
          unfold I in *; simpl in *.
          inversion 1; intros; subst.
          apply (H _ _ eq_refl).
        - split; auto.
          right. split; auto.
      }
      (* res *)
      {
        pupdate_intros.
        do 2 eexists. split; [apply rt_refl|].
        destruct Hpre as [[? ?] ?].
        split.
        - split; auto.
          unfold I in *; simpl in *.
          inversion 1; intros; subst.
          apply (H _ _ eq_refl).
        - split; auto.
          left; right.
          do 2 (split; auto).
          unfold NotOwned. auto.
      }

      apply provable_ret_safe;
      try solve_conj_impl;
      try solve_conj_stable stableDB.
    }
    (* initial *)
    {
      unfold I. simpl; inversion 1; subst.
      intros; subst; auto.
    }
  Defined.

  Print Assumptions Mfai.
End FAIImpl.

