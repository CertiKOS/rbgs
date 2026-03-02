Require Import FMapPositive.
Require Import Relation_Operators Operators_Properties.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.PArith.PArith.
Require Import Coq.Program.Equality.
Require Import Lia.
Require Import PeanoNat.
Require Import Classical.

Require Import coqrel.LogicalRelations.
Require Import models.EffectSignatures.
Require Import LinCCAL.
Require Import LTS.
Require Import Lang.
Require Import Semantics.
Require Import Logics.
Require Import Assertion.
Require Import TPSimulationSet.
Require Import RGILogicSet.
Require Import Specs.
Require Import SeparationAlgebra.


  Ltac split_right :=
    try (split; [| split_right]).

  Ltac extract n H :=
    (* let Hneed := fresh "H" in *)
    lazymatch n with
      | O => idtac
      | S ?n' =>
          destruct H as [_ H];
          extract n' H
    end;
    simpl in H;
    match H with
    | exists _, _ => idtac
    | _ => try destruct H as [H _]
    end.

  Open Scope nat_scope.

Class HasBeq (t : Type) := {
  beq : t -> t -> bool;
  beq_refl : forall x, beq x x = true;
  beq_true : forall x y, beq x y = true -> x = y;
  beq_false : forall x y, beq x y = false -> x <> y;
}.

(* TODO: change IsExpired to owner *)
(* Module CASTaskImpl.
  Import LinCCALBase.
  Import LTSSpec.
  Import Lang.
  Import Semantics.
  Import AssertionsSet.
  Import RGILogic.
  Import TPSimulation.
  Import AtomicLTS CAS'Spec FAISpec CASTaskSpec.
  Import (coercions, canonicals, notations) Sig.
  Import (notations) LinCCAL.
  Import (canonicals) Sig.Plus.
  Open Scope prog_scope.
  Open Scope rg_relation_scope.

  Context (Val : Type).
  Context (vInit : Val).

  Definition E : layer_interface :=
  {|
    li_sig := Sig.Plus.omap (ECAS' ((CASTask Val) + Val)) EFAI;
    li_lts := tens_lts VCAS' VFAI;
    li_init := pair (Idle (inr vInit)) (Idle O);
  |}.
  
  Definition F : layer_interface :=
  {|
    li_sig := ECASTask Val;
    li_lts := VCASTask;
    li_init := Idle (cts (inr vInit) O nil);
  |}.

  Definition allocTask_impl (_ : tid) : Prog (li_sig E) nat :=
    inr fai >= i => Ret i.
  
  Definition tryPlaceTask_impl o n i (cid : tid) : Prog (li_sig E) ((CASTask Val) + Val) :=
    inl (cas (inr o) (inl (CTask cid o n i))) >= r => Ret r.
  
  Definition tryResolveTask_impl tsk v (_ : tid) : Prog (li_sig E) unit :=
    inl (cas (inl tsk) (inr v)) >= _ => Ret tt.
End CASTaskImpl. *)


Module CCASImpl.
  Import LinCCALBase.
  Import LTSSpec.
  Import Lang.
  Import Semantics.
  Import AssertionsSet.
  Import RGILogic.
  Import TPSimulation.
  Import AtomicLTS Reg'Spec CASTaskSpec CCASSpec.
  Import (coercions, canonicals, notations) Sig.
  Import (notations) LinCCAL.
  Import (canonicals) Sig.Plus.
  Open Scope prog_scope.
  Open Scope rg_relation_scope.

  Context (Val : Type).
  Context (vInit : Val).
  Context `{HasBeq Val}.

  Definition E : layer_interface :=
  {|
    li_sig := Sig.Plus.omap (ECASTask Val) (EReg bool);
    li_lts := tens_lts VCASTask VReg;
    li_init := pair (Idle (cts (inr vInit) O (fun _ => Inactive))) (Idle true);
  |}.
  
  Definition F : layer_interface :=
  {|
    li_sig := ECCAS Val;
    li_lts := VCCAS;
    li_init := Idle (pair vInit false);
  |}.

  Definition assertion := @Assertion (@ProofState _ _ (li_lts E) (li_lts F)).
  Definition rg_relation := @RGRelation _ _ (li_lts E) (li_lts F).

  Open Scope rg_relation_scope.
  Open Scope assertion_scope.

  Definition ALinEx t ls : assertion := fun s => exists ρ π, Δ s ρ π /\ TMap.find t π = ls.
  Definition ALinIdle t : assertion := ALinEx t None.

  Definition Flag b : assertion := fun s => state (snd (σ s)) = b.
  Definition IsInactive i : assertion := fun s => owner (state (fst (σ s))) i = Inactive.
  Definition OwnedBy i t : assertion := fun s => owner (state (fst (σ s))) i = Owned t.
  Definition IsExpired i : assertion  := fun s => owner (state (fst (σ s))) i = Expired.
  Definition CurrentTask task : assertion := fun s => (current (state (fst (σ s)))) = inl task.
  Definition CurrentVal v : assertion := fun s => (current (state (fst (σ s)))) = inr v.
  Definition NotPlacedBy i t : assertion :=
    OwnedBy i t //\\ (∀ o n, !! CurrentTask (CTask t o n i)).
  
  Lemma OwnedByNotIsExpired : forall i t,
    ⊨ OwnedBy i t ==>> !! IsExpired i.
  Proof.
    intros. intros ? ?.
    unfold OwnedBy, IsExpired in *.
    congruence.
  Qed.

  Lemma CurrentTaskCongruence : forall task1 task2 s,
    CurrentTask task1 s -> CurrentTask task2 s -> task1 = task2.
  Proof.
    unfold CurrentTask. intros.
    rewrite H0 in H1. congruence.
  Qed.

  Lemma TaskValConflict : forall task v s,
    CurrentTask task s -> CurrentVal v s -> False.
  Proof.
    unfold CurrentTask, CurrentVal. intros.
    rewrite H0 in H1. congruence.
  Qed.

  Definition castask_val (c : @CASTaskState Val) : Val :=
    match (current c) with
    | inl (CTask _ o _ _) => o
    | inr v => v
    end.

  Definition I_val : assertion :=
    fun s => 
      forall v, CurrentVal v s ->
      forall ρ π, Δ s ρ π -> fst (state ρ) = v.

  Definition NotDone t o n : assertion :=
    fun s =>
      exists ρ π, Δ s ρ π /\
      TMap.find t π = Some (ls_inv (cas o n)) /\
      fst (state ρ) = o.

  Definition I_cur_task : assertion :=
    ∀ t o n i , CurrentTask (CTask t o n i) ==>>
      (
        OwnedBy i t //\\
        !! ALinIdle t //\\
        NotDone t o n
      ).

  Definition I_not_cur_task : assertion :=
    ∀ t, (∀ o n i, !! CurrentTask (CTask t o n i)) ==>>
      (fun s => exists ls, forall ρ π, Δ s ρ π -> TMap.find t π = ls).
  
  Definition I_flag : assertion :=
    fun s => forall ρ π, Δ s ρ π ->
      snd (state ρ) = state (snd (σ s)).

  Definition I_ρ_atomic : assertion :=
    fun s => forall ρ π, Δ s ρ π ->
      exists s, ρ = Idle s.

  Definition ticket_not_owned : assertion :=
    fun s => forall i, (ticket (state (fst (σ s)))) <= i ->
      IsInactive i s.
      (* forall t o n i, ~ CurrentTask (CTask t o n i) s. *)

  Definition I : assertion :=
    I_ρ_atomic //\\ I_flag //\\
    I_val //\\ I_cur_task //\\ I_not_cur_task //\\
    ticket_not_owned.

  Definition G_trylin : rg_relation :=
    fun s1 s2 =>
      (Δ s1 ⊆ Δ s2)%AbstractConfig /\
      (exists t o n i, CurrentTask (CTask t o n i) s1) /\
      forall cts1 cts2,
        cts1 = state (fst (σ s1)) ->
        cts2 = state (fst (σ s2)) ->
        current cts1 = current cts2 /\
        ticket cts1 = ticket cts2 /\
        owner cts1 = owner cts2.
    (* fun s1 s2 => exists t o n i,
      CurrentTask (CTask t o n i) s1 /\
      CurrentTask (CTask t o n i) s2 /\
      (* non-decr when there is task *)
      (Δ s1 ⊆ Δ s2)%AbstractConfig. *)

  Definition G_resolve : rg_relation :=
    fun s1 s2 =>
      (exists v, CurrentVal v s2) /\
      exists t o n i, CurrentTask (CTask t o n i) s1 /\
        (exists ρ π,
          (Δ s2 ≡ [( ρ, π )])%AbstractConfig /\
          ([( ρ, π )] ⊆ Δ s1)%AbstractConfig /\
          TMap.find t π = Some (ls_linr (cas o n) o)) /\
      forall cts1 cts2,
        cts1 = state (fst (σ s1)) ->
        cts2 = state (fst (σ s2)) ->
        ticket cts1 = ticket cts2 /\
        owner cts1 i = Owned t /\
        forall i', owner cts2 i' = owner_upd (owner cts1) i Expired i'.
    (* fun s1 s2 => exists t o n i,
      CurrentTask (CTask t o n i) s1 /\
      (exists v, CurrentVal v s2) /\
      IsExpired i s2 /\
      (* resolve to single poss with linr *)
      exists ρ π,
        (Δ s2 ≡ [( ρ, π )])%AbstractConfig /\
        ([( ρ, π )] ⊆ Δ s1)%AbstractConfig /\
        TMap.find t π = Some (ls_linr (cas o n) o). *)

  (* Definition G_id : rg_relation :=
    fun s1 s2 =>
      state (fst (σ s1)) = state (fst (σ s2)) /\
      state (snd (σ s1)) = state (snd (σ s2)) /\
      Δ s1 ≡ Δ s2. *)

  Definition G_alloc t : rg_relation :=
    fun s1 s2 =>
      Δ s1 ≡ Δ s2 /\
      forall cts1 cts2,
        cts1 = state (fst (σ s1)) ->
        cts2 = state (fst (σ s2)) ->
        current cts1 = current cts2 /\
        S (ticket cts1) = ticket cts2 /\
        owner cts1 (ticket cts1) = Inactive /\
        forall i, owner cts2 i = owner_upd (owner cts1) (ticket cts1) (Owned t) i.

  Definition G_place_task t : rg_relation :=
    fun s1 s2 =>
      (exists o n i, CurrentVal o s1 /\
        CurrentTask (CTask t o n i) s2) /\
      Δ s1 ≡ Δ s2 /\
      forall cts1 cts2,
        cts1 = state (fst (σ s1)) ->
        cts2 = state (fst (σ s2)) ->
        ticket cts1 = ticket cts2 /\
        owner cts1 = owner cts2.
    (* fun s1 s2 => exists o n i,
      CurrentVal o s1 /\
      CurrentTask (CTask t o n i) s2 /\
      Δ s1 ≡ Δ s2 /\
      OwnedBy i t s1. *)

  Definition G t : rg_relation :=
    G_alloc t ∪ G_place_task t ∪ G_trylin ∪ G_resolve.

  (* only the owner can place the task *)
  Definition R_task t : rg_relation :=
    fun s1 s2 => forall o n i,
      ~ CurrentTask (CTask t o n i) s1 -> ~ CurrentTask (CTask t o n i) s2.

  Definition R_IsExpired : rg_relation :=
    fun s1 s2 => forall i, IsExpired i s1 -> IsExpired i s2.

  Definition R_notplaced t : rg_relation :=
    fun s1 s2 => forall i, NotPlacedBy i t s1 -> NotPlacedBy i t s2.

  (* need this to ensure domexact *)
  Definition R_id t : rg_relation :=
    fun s1 s2 => 
      forall ls, ALinEx t ls s1 <-> ALinEx t ls s2.

  Definition R t : rg_relation :=
    R_IsExpired ∩ R_notplaced t ∩
    ((R_task t ∩ R_id t) ∪ G_trylin ∪ G_resolve).

  Lemma RG_compatible : forall t1 t2, t1 <> t2 -> (G t1 ⊆ R t2).
  Proof.
    intros. intros s1 s2 ?.
    destruct H1 as [[[? | ?] | ?] | ?].
    - destruct H1 as [? ?].
      specialize (H2 _ _ eq_refl eq_refl) as [? [? [? ?]]].
      split;[split|].
      + unfold R_IsExpired. unfold IsExpired; intros.
        rewrite H5. unfold owner_upd. 
        destruct (Nat.eqb_spec (ticket (state (fst (σ s1)))) i); auto.
        subst. congruence.
      + unfold R_notplaced, NotPlacedBy, OwnedBy, CurrentTask, Forall, Neg.
        intros ? [? ?]. rewrite H2 in *.
        split; auto.
        rewrite H5. unfold owner_upd.
        destruct (Nat.eqb_spec (ticket (state (fst (σ s1)))) i); auto.
        subst. congruence.
      + do 2 left. split.
        * unfold R_task, CurrentTask, Forall.
          rewrite H2. auto.
        * unfold R_id, ALinEx.
          split; intros [? [? [HΔ ?]]];
          apply H1 in HΔ; do 2 eexists; eauto.
    - destruct H1 as [[? [? [? [? ?]]]] [? ?]].
      specialize (H4 _ _ eq_refl eq_refl) as [? ?].
      split;[split|].
      + unfold R_IsExpired, IsExpired; intros.
        rewrite <- H5. auto.
      + unfold R_notplaced, NotPlacedBy, OwnedBy. intros ? [? ?].
        rewrite H5 in H6. split; auto.
        intros ? ? ?.
        eapply CurrentTaskCongruence in H2; eauto.
        congruence.
      + do 2 left. split.
        * unfold R_task.
          intros ? ? ? _ ?.
          eapply CurrentTaskCongruence in H2; eauto. congruence.
        * unfold R_id, ALinEx.
          split; intros [? [? [HΔ ?]]];
          apply H3 in HΔ; do 2 eexists; eauto.
    - split; [|left; right; auto].
      destruct H1 as [? [[? [? [? [? ?]]]] ?]].
      specialize (H3 _ _ eq_refl eq_refl) as [? [? ?]].
      split.
      + unfold R_IsExpired, IsExpired.
        rewrite H5. auto.
      + unfold R_notplaced, NotPlacedBy, OwnedBy, CurrentTask, Forall, Neg.
        intros ? [? ?]. rewrite H3 in *. rewrite H5 in *.
        split; auto.
    - split; [| right; auto].
      destruct H1 as [[? ?] [? [? [? [? [? [? ?]]]]]]].
      specialize (H4 _ _ eq_refl eq_refl) as [? [? ?]].
      split.
      + unfold R_IsExpired, IsExpired.
        intros. rewrite H6.
        unfold owner_upd. destruct (x3 =? i); auto.
      + unfold R_notplaced, NotPlacedBy, OwnedBy, CurrentTask, Forall, Neg.
        intros ? [? ?].
        split.
        * rewrite H6.
          unfold owner_upd. destruct (Nat.eqb_spec x3 i); auto; subst.
          rewrite H2 in H8. congruence.
        * rewrite H1. congruence.
  Qed.

  Lemma R_domexact : forall t0 s1 s2, R t0 s1 s2 -> I s2 ->
    (forall (ρ1 : State (li_lts F)) (π1 : tmap LinState), Δ s1 ρ1 π1 -> TMap.find t0 π1 = None) <->
    (forall (ρ2 : State (li_lts F)) (π2 : tmap LinState), Δ s2 ρ2 π2 -> TMap.find t0 π2 = None).
  Proof.
    destruct 1 as [[HR_expire HR_notplaced] [[? | ?] | ?]]; intros.
    - destruct H0 as [R_task ?]. unfold R_id in H0.
      split; intros.
      + pose proof ac_nonempty (Δ s1) as [ρ1 [π1 ?]].
        specialize (H2 _ _ H4).
        assert (ALinEx t0 None s1); unfold ALinEx; eauto.
        apply H0 in H5 as [? [? [? ?]]].
        eapply ac_domexact; eauto.
      + pose proof ac_nonempty (Δ s2) as [ρ2 [π2 ?]].
        specialize (H2 _ _ H4).
        assert (ALinEx t0 None s2); unfold ALinEx; eauto.
        apply H0 in H5 as [? [? [? ?]]].
        eapply ac_domexact; eauto.
    (* - destruct H0 as (t & o & n & i & [_ [_ [_ ?]]]).
      split; intros; apply H0 in H3; eapply H2; eauto. *)
    - destruct H0 as [HΔ [[t [o [n [i ?]]]] ?]].
      specialize (H2 _ _ eq_refl eq_refl) as [? [? ?]].
      split; intros.
      + epose proof ac_nonempty (Δ s1) as [ρ1 [π1 ?]].
        pose proof (HΔ _ _ H7).
        apply H5 in H7.
        eapply ac_domexact; eauto.
      + apply HΔ in H6.
        eapply H5; eauto.
    - destruct H0 as [_ [t [o [n [i [_ [[? [? [? [? ?]]]] _]]]]]]].
      split; intros.
      + epose proof ACSingle.
        apply H2, H4 in H6.
        apply H0 in H5.
        inversion H5; subst; auto.
      + do 2 epose proof ACSingle.
        apply H2 in H6.
        apply H0, H4 in H7.
        eapply ac_domexact; eauto.
  Qed.
  
  (*
  
  I :=
      (* current ticket not IsExpired *)
      ~ In ticket IsExpired //\\
      (* current task not IsExpired *)
      (* so that we can easily deduce that the complete method always fail if the task is IsExpired *)
      forall i, In i expire -> current <> CTask _ _ _ i

      //\\

      (* idle thread should not have pending task *)
      ALinIdle t -> current <> CTask t _ _ _

  *)
  

  (* 
    G_trylin  : current' = CTask t _ _ _ /\ forall π ∈ Δ, π ∈ Δ'
    G_resolve : current = CTask t o _ i /\ IsExpired'(i)
  *)

  Lemma Ginv_I : forall t f, ⊨ Ginv t f ⊚ I ==>> I.
  Proof.
    intros. intros [s' [HI [Hσ [? HΔ]]]].
    unfold I in *.
    split_right.
    - extract 0%nat HI. unfold I_ρ_atomic in *.
      intros.
      apply HΔ in H1. inversion H1; subst.
      eapply HI; eauto.
    - extract 1%nat HI. unfold I_flag in *.
      intros.
      apply HΔ in H1. inversion H1; subst.
      rewrite Hσ in *.
      eapply HI; eauto.
    - extract 2%nat HI. unfold I_val, CurrentVal in *.
      intros.
      apply HΔ in H2. inversion H2; subst.
      rewrite Hσ in *.
      eapply HI; eauto.
    - extract 3 HI. unfold I_cur_task, CurrentTask in *.
      intros ? ? ? ? ?.
      rewrite <- Hσ in *. apply HI in H1.
      split_right; unfold IsExpired, ALinIdle, NotDone in *.
      + extract 0%nat H1. unfold OwnedBy in *. rewrite <- Hσ in *. auto.
      + extract 1%nat H1. intros [? [? [? ?]]]. apply H1.
        apply HΔ in H2. inversion H2; subst.
        do 2 eexists; split; eauto.
        rewrite TMap.gso in H3; auto.
        intros ?; subst.
        rewrite TMap.gss in H3. congruence.
      + destruct H1 as [_ [_ [? [? [? [? ?]]]]]].
        exists x, (TMap.add t0 (ls_inv f) x0); split_right; auto.
        * apply HΔ. constructor; auto.
        * rewrite TMap.gso; auto.
          intros ?; subst.
          apply H0 in H1; congruence.
    - extract 4 HI. unfold I_not_cur_task, CurrentTask in *.
      intros ? ?. unfold Forall, Neg in H1. rewrite <- Hσ in H1.
      apply HI in H1 as [? ?].
      destruct (Pos.eq_dec v t0); subst.
      + exists (Some (ls_inv f)); intros.
        apply HΔ in H2; inversion H2; subst.
        rewrite TMap.gss; auto.
      + exists x; intros.
        apply HΔ in H2; inversion H2; subst.
        rewrite TMap.gso; eauto.
    - extract 5 HI. unfold ticket_not_owned, IsInactive in *.
      rewrite Hσ in *. apply HI.
  Qed.

  Lemma Gret_I : forall t f ret,
    ⊨ Gret t f ret ⊚ (I //\\ ALin t (ls_linr f ret)) ==>> I.
  Proof.
    intros. intros [s' [[HI HALin] [Hσ [? HΔ]]]].
    unfold I in *.
    split_right.
    - extract 0%nat HI. unfold I_ρ_atomic in *.
      intros.
      apply HΔ in H1. inversion H1; subst.
      eapply HI; eauto.
    - extract 1%nat HI. unfold I_flag in *.
      intros.
      apply HΔ in H1. inversion H1; subst.
      rewrite Hσ in *.
      eapply HI; eauto.
    - extract 2 HI. unfold I_val, CurrentVal in *.
      intros.
      apply HΔ in H2. inversion H2; subst.
      rewrite Hσ in *.
      eapply HI; eauto.
    - extract 3 HI. unfold I_cur_task, CurrentTask in *.
      intros ? ? ? ? ?.
      rewrite <- Hσ in *. apply HI in H1.
      split_right; unfold IsExpired, ALinIdle, NotDone in *.
      + extract 0%nat H1. unfold OwnedBy in *. rewrite <- Hσ in *. auto.
      + pose proof H1. extract 1%nat H1. destruct H2 as [_ [_ ?]].
        intros [? [? [? ?]]]. apply H1.
        apply HΔ in H3. inversion H3; subst.
        do 2 eexists; split; eauto.
        rewrite TMap.gro in H4; auto.
        intros ?; subst.
        destruct H2 as [? [? [? [? ?]]]].
        apply H0 in H2. congruence.
      + destruct H1 as [_ [_ [? [? [? [? ?]]]]]].
        exists x, (TMap.remove t0 x0); split_right; auto.
        * apply HΔ. constructor; auto.
        * rewrite TMap.gro; auto.
          intros ?; subst.
          apply H0 in H1; congruence.
    - extract 4 HI. unfold I_not_cur_task, CurrentTask in *.
      intros ? ?. unfold Forall, Neg in H1. rewrite <- Hσ in H1.
      apply HI in H1 as [? ?].
      destruct (Pos.eq_dec v t0); subst.
      + exists None; intros.
        apply HΔ in H2; inversion H2; subst.
        rewrite TMap.grs; auto.
      + exists x; intros.
        apply HΔ in H2; inversion H2; subst.
        rewrite TMap.gro; eauto.
    - extract 5 HI. unfold ticket_not_owned, IsInactive in *.
      rewrite Hσ in *. eauto.
  Qed.



  Lemma Istable {t} : Stable (R t) I I.
  Proof. unfold Stable. apply ConjRightImpl, ImplRefl. Qed.

  Lemma ALinALinEx : forall t ls, ⊨ ALin t ls ==>> ALinEx t (Some ls).
  Proof.
    intros. intros ?.
    pose proof ac_nonempty (Δ s) as [? [? ?]].
    pose proof H1.
    apply H0 in H2. do 2 eexists; eauto.
  Qed.

  Lemma ALinExCongruence : forall t ls1 ls2,
    ⊨ ALin t ls1 ==>> ALinEx t ls2 ==>> ⌜Some ls1 = ls2⌝.
  Proof.
    intros. intros ? [? [? [? ?]]].
    apply H0 in H1. congruence.
  Qed.


  Lemma stable_not_cur_task : forall t o n i,
    Stable (R t) I (!! CurrentTask (CTask t o n i)).
  Proof.
    unfold Stable, R.
    intros. intros [[s0 [? [? ?]]] ?].
    destruct H2 as [[? | ?] | ?].
    - apply H1, H0.
    - destruct H2 as [? [? [? [? [? [? ?]]]]]].
      intros ?.
      pose proof CurrentTaskCongruence _ _ _ H4 H6.
      inversion H7; subst. congruence.
    - destruct H2 as (? & ? & ? & ? & [? [[? ?] [? ?]]]).
      intros ?.
      eapply TaskValConflict in H4; eauto.
  Qed.

  Lemma stable_not_cur_task_oni : forall t,
    Stable (R t) I (∀ o n i, !! CurrentTask (CTask t o n i)).
  Proof.
    intros.
    do 3 (apply StableForall; intros).
    apply stable_not_cur_task.
  Qed.

  Lemma stable_not_cur_task_on : forall t i,
    Stable (R t) I (∀ o n, !! CurrentTask (CTask t o n i)).
  Proof.
    intros.
    do 2 (apply StableForall; intros).
    apply stable_not_cur_task.
  Qed.

  Lemma stable_ccas_l0: forall t o n,
    Stable (R t) I
      (ALin t (ls_inv (cas o n)) //\\ ∀ o n i, !! CurrentTask (CTask t o n i)).
  Proof.
    unfold Stable, R.
    intros. intros ?.
    assert ((∀ (o0 n0 : Val) (i : nat), !! CurrentTask (CTask t0 o0 n0 i)) s);
    [eapply StableWeaken; eauto;[apply stable_not_cur_task_oni| |]; solve_conj_impl |].
    split; auto.
    destruct H0 as [[s0 [[? ?] [? ?]]] ?].
    destruct H4 as [[? | ?] | ?].
    - unfold R_id in H4.
      intros ? ? ?.
      assert (TMap.find t0 π = Some (ls_inv (cas o n)) \/ TMap.find t0 π <> Some (ls_inv (cas o n))) as [? | ?] by apply classic; auto.
      assert (ALinEx t0 (TMap.find t0 π) s); [do 2 eexists; eauto|].
      apply H4 in H8.
      eapply ALinExCongruence in H8; eauto.
    - destruct H4 as [? [? [? [? [? [? ?]]]]]].
      apply H5 in H1 as [? ?].
      pose proof ac_nonempty (Δ s0) as [? [? ?]].
      pose proof H8.
      apply H7 in H8.
      apply H0 in H9.
      intros ? ? ?.
      apply H1 in H10, H8.
      change (li_sig F) with (ECCAS Val) in H8.
      rewrite H8 in H9; subst.
      rewrite H9 in H10; auto.
    - destruct H4 as (? & ? & ? & ? & [? [[? ?] [? ?]]]).
      destruct H8 as [ρ [π [? [? ?]]]].
      intros ? ? ?.
      apply H8, H9, H0 in H11; auto.
  Qed.

  Lemma stable_ccas_l1: forall t i,
    Stable (R t) I
      (!! IsExpired i //\\ ∀ o n, !! CurrentTask (CTask t o n i)).
  Proof.
    unfold Stable, R.
    intros. intros ?.
    assert ((∀ (o0 n0 : Val) (i : nat), !! CurrentTask (CTask t0 o0 n0 i)) s);
    [eapply StableWeaken; eauto;[apply stable_not_cur_task_oni| |]; solve_conj_impl |].
    split; auto.
    destruct H0 as [[s0 [[? ?] [? ?]]] ?].
    destruct H4 as [[? | ?] | ?].
    - unfold R_id in H4.
      intros ? ? ?.
      assert (TMap.find t0 π = Some (ls_inv (cas o n)) \/ TMap.find t0 π <> Some (ls_inv (cas o n))) as [? | ?] by apply classic; auto.
      assert (ALinEx t0 (TMap.find t0 π) s); [do 2 eexists; eauto|].
      apply H4 in H8.
      eapply ALinExCongruence in H8; eauto.
    - destruct H4 as [? [? [? [? [? [? ?]]]]]].
      apply H5 in H1 as [? ?].
      pose proof ac_nonempty (Δ s0) as [? [? ?]].
      pose proof H8.
      apply H7 in H8.
      apply H0 in H9.
      intros ? ? ?.
      apply H1 in H10, H8.
      change (li_sig F) with (ECCAS Val) in H8.
      rewrite H8 in H9; subst.
      rewrite H9 in H10; auto.
    - destruct H4 as (? & ? & ? & ? & [? [[? ?] [? ?]]]).
      destruct H8 as [ρ [π [? [? ?]]]].
      intros ? ? ?.
      apply H8, H9, H0 in H11; auto.
  Qed.

    Open Scope nat.


            

  (* cid_not_idle := (cid = t //\\ ~ ALinIdle t) \\// cid <> t *)
  (* task_placed t o n i :=
      cid_not_idle //\\
      ((IsExpired i //\\ (ALinIdle t \\// ALin t linr o)) \\//
      (current = CTask t o n i //\\ NotDone t o n i))
  *)

  Definition complete t o n i : Prog (li_sig E) unit :=
    (*
      cid_not_idle //\\
      task_placed t o n i
    *)
    inr Reg'Spec.get >= b =>
    (*
      cid_not_idle //\\
      ((IsExpired i //\\ (ALinIdle t \\// ALin t linr o)) \\//
        (current = CTask t o n i //\\ ALinEx t linr o))
    *)
    inl (tryResolveTask (CTask t o n i)
                        (match b with
                          | true => n
                          | false => o end)) >= _ =>
    (* (cid = t //\\ ALin t linr o) \\// cid <> t *)
    Ret tt.

  Definition ccas_impl o n (cid : tid) : Prog (li_sig E) Val :=
    (* I:= ... //\\ ALin t None -> current <> CTask t _ _ _ //\\ ... *)
    (* 
      ALin t inv //\\ current <> CTask t _ _ _
    *)
    inl (allocTask o n) >= i =>
    (* ILoop :=
      ALin t inv //\\ current <> CTask t _ _ _ //\\
      OwnedBy i t //\\ current <> CTask _ _ _ i
    *)
    Do {
      inl (tryPlaceTask o n i) >= r =>
      (* 
        (* other task *)
        (ILoop //\\
          r <> o //\\ r = task t' o' n' i' //\\ task_placed t' o' n' i' //\\ t' <> t)
        (* the following cases will break the loop *)
        (* failed *)
        (r <> o //\\ isVal r //\\ ALin t (linr ccas r))
        (* my task *)
        (r = o //\\ task_placed t o n i //\\ ~ ALinIdle t)
      *)
      match r with
      (*
        (ILoop //\\
          r <> o //\\ r = task t' o' n' i' //\\ task_placed t' o' n' i')
      *)
      | inl (CTask t o n i) =>
          (complete t o n i) ;;
          (* ILoop *)
          Ret r
      (* 
        (* failed *)
        (r <> o //\\ isVal r //\\ ALin t (linr ccas r))
        (* my task *)
        (r = o //\\ task_placed t o n //\\ ~ ALinIdle t)
      *)
      | _ => Ret r
      end
    } Loop >= r =>
    ((if beq r o then
      (*
        r = o //\\ task_placed t o n //\\ ~ ALinIdle t
      *)
      complete cid o n i
      (*
        ALin t linr r
      *)
    else
      (*
        ALin t (linr ccas r)
      *)
      Ret tt) ;;
    Ret r).

  Definition setFlag_impl b (_ : tid) : Prog (li_sig E) unit :=
    inr (set b) >= _ => Ret tt.
  
  
  Create HintDb stableDB.
  Hint Resolve stable_ccas_l0 Istable : stableDB.

  (* Ltac extract n H :=
    (* let Hneed := fresh "H" in *)
    lazymatch n with
      | O => idtac
      | S ?n' =>
          destruct H as [_ H];
          extract n' H
    end;
    try destruct H as [H _]. *)

    
  Program Definition MCCAS : layer_implementation E F := {|
    li_impl m :=
      match m with
    | cas o n => ccas_impl o n
    | setFlag b => setFlag_impl b
      end
  |}.
  Next Obligation.
    eapply RGILogic.soundness with (R:=R) (G:=G) (I:=I).
    (* valid RG *)
    {
      constructor.
      apply R_domexact.
    }
    {
      intros. intros s1 s2 [? | ?]; [eapply RG_compatible; eauto |].
      destruct H1 as [[? | ?] | ?].
      - unfold GINV, Ginv, LiftRelation_Δ in *.
        destruct H1 as [? [? [? ?]]].
        split; [unfold R_task, CurrentTask; rewrite H1; auto|].
        do 2 left.
        unfold R_id. intros; split; intros [ρ [π [? ?]]].
        + pose proof ACInv (Δ s1) t1 x _ _ H4.
          apply H3 in H6.
          exists ρ, (TMap.add t1 (ls_inv x) π); split; auto.
          rewrite TMap.gso; auto.
        + apply H3 in H4.
          inversion H4; subst.
          exists ρ, π0; split; auto.
          rewrite TMap.gso; auto.
      - unfold GRET, Gret, LiftRelation_Δ in *.
        destruct H1 as [? [? [? [? ?]]]].
        split; [unfold R_task, CurrentTask; rewrite H1; auto|].
        do 2 left.
        unfold R_id. intros; split; intros [ρ [π [? ?]]].
        + pose proof ACRes (Δ s1) t1 _ _ H4.
          apply H3 in H6.
          exists ρ. eexists. split; eauto.
          rewrite TMap.gro; auto.
        + apply H3 in H4.
          inversion H4; subst.
          exists ρ, π0; split; auto.
          rewrite TMap.gro; auto.
      - unfold GId in H1; subst.
        split; unfold R_task; auto.
        do 2 left. unfold R_id; intros; tauto.
    }
    (* method provable *)
    {
      intros t.
      destruct f.
      (* set flag *)
      {
        admit.
      }
      (* ccas *)
      {
        (* pre-condition *)
        exists (I //\\ ALin t (ls_inv (cas o n))
                  //\\ ∀ o n i, !! CurrentTask (CTask t o n i)).
        (* post-condition *)
        exists (fun r => I //\\ ALin t (ls_linr (cas o n) r)).
        constructor;
        try solve_conj_impl;
        try solve_conj_stable' stableDB.
        (* invocation *)
        {
          intros ? ?.
          split; [apply Ginv_I in H0; auto|].
          destruct H0 as [s' [HI [Hσ [? HΔ]]]].
          split.
          - intros ? ? ?.
            apply HΔ in H1. inversion H1; subst.
            rewrite TMap.gss. auto.
          - intros ? ? ? ?.
            unfold I in HI. extract 3 HI.
            unfold I_cur_task, CurrentTask in *.
            rewrite <- Hσ in *. apply HI in H1 as [_ [_ ?]].
            destruct H1 as [? [? [? [? ?]]]].
            apply H0 in H1. congruence.
        }
        (* response *)
        {
          intros. intros [? [[? ?] ?]].
          eapply Gret_I; eexists; do 2 (split; eauto).
        }
        {
          intros. apply H0 in H1. auto.
        }

        unfold ccas_impl. simpl.

        (* allocTask *)
        eapply provable_vis_safe with
          (P' := I //\\
                ALin t (ls_inv (cas o n)) //\\
                (∀ (o0 n0 : Val) (i : nat), !! CurrentTask (CTask t o0 n0 i)))
          (Q' := fun i => I //\\
                ALin t (ls_inv (cas o n)) //\\
                !! IsExpired (i) //\\
                (∀ (o0 n0 : Val), !! CurrentTask (CTask t o0 n0 i)));
          try solve_no_error;
          try solve_conj_impl;
          try solve_conj_stable stableDB.
          [solve_no_error | | |].
      }
    }




(* ************ Outdate ************* *)

  Definition ccas_impl o n (cid : tid) : Prog (li_sig E) Val :=
    inl (allocTask o n) >= i =>
    Do {
      (*
        I //\\ alin t (inv ccas) 
        (* my ticket is not IsExpired *)
        (* other wise it breaks the invariant *)
        //\\ ~ In i IsExpired
      *)
      inl (tryPlaceTask o n i) >= r =>
      (* I //\\ 
            (* failed *)
            (r <> o //\\ isVal r //\\ alin t (linr ccas r))
            (* other task *)
            (r <> o //\\ alin t (inv ccas) //\\ r = task t' o' n' i' //\\ 
                (task_placed t' o' n' i' \\// task_resolved t t' o' n' i'))
            (* my task *)
            (r = o //\\ task_placed t o n i)
      *)
      match r with
      (* I //\\
            (r <> o //\\ alin t (inv ccas) //\\ r = task t' o' n' i' //\\ 
                (task_placed t' o' n' i' \\// task_resolved t t' o' n' i'))
      *)
      | inl (CTask t o n i) =>
          (complete t o n i) ;;
          (* I //\\ r = task t' o' n' i' //\\ alin t (inv ccas) *)
          Ret r
      (* I //\\ 
            (* failed *)
            (r <> o //\\ isVal r //\\ alin t (linr ccas r))
            (* my task *)
            (r = o //\\ task_placed t o n)
      *)
      | _ => Ret r
      end
    } Loop >= r =>
    (if beq r o then
      (* I //\\ 
            (r = o //\\ task_placed t o n)
      *)
      complete cid o n i
      (* I //\\ 
            (r = o //\\ alin t (linr ccas r))
      *)
    else
      (* I //\\
            (r <> o //\\ isVal r //\\ alin t (linr ccas r))
      *)
      Ret tt) ;;
    Ret r.
  
  Definition setFlag_impl b (_ : tid) : Prog (li_sig E) unit :=
    inr (set b) >= _ => Ret tt.

  Instance PSS_Join_equiv : Join (@ProofState _ _ (li_lts E) (li_lts F)) :=
    (@PSS_Join _ _ _ _ equiv_Join equiv_Join).

  (* Task placed but not executed *)
  Definition notDone t (o n : Val) : assertion :=
    ALin' t (ls_inv (cas o n)) * (∃ b, (@Aρ _ _ _ (li_lts F) (Idle (pair o b)))).
  
  (* Task executed and succeeded *)
  Definition endSucc t o n : assertion :=
    ALin' t (ls_linr (cas o n) o) * (∃ b, @Aρ _ _ _ (li_lts F) (Idle (pair n b))).

  (* Task executed but failed *)
  Definition endFail t o n : assertion :=
    ALin' t (ls_linr (cas o n) o) * (∃ b, @Aρ _ _ _ (li_lts F) (Idle (pair o b))).

  Definition trySucc t o n : assertion :=
    notDone t o n ⨁ endSucc t o n.
  Definition tryFail t o n : assertion :=
    notDone t o n ⨁ endFail t o n.
  Definition tryBoth t o n : assertion :=
    notDone t o n ⨁ endSucc t o n ⨁ endFail t o n.

  Definition ACAS P : assertion := fun s => P (fst (σ s)).
  Notation "'cas' ↦ v" :=
    (ACAS (fun c => state c = v))
    (at level 30, no associativity).
  
  Definition CTask t o n : assertion :=
    cas ↦ inl (task t o n) //\\
    (notDone t o n \\// trySucc t o n \\// tryFail t o n \\// tryBoth t o n).
  Definition CVal : assertion :=
    ∃ v : Val, cas ↦ inr v //\\ ∃ b, @Aρ _ _ _ (li_lts F) (Idle (pair v b)).
  
  Definition ICAS : assertion :=
    CVal \\// ∃ t, ∃ o, ∃ n, CTask t o n.

  Definition AFlag P : assertion := fun s => P (snd (σ s)).
  Notation "'flag' ↦ v" :=
    (AFlag (fun b => state b = v))
    (at level 30, no associativity).
  
  Definition IFlag : assertion :=
    ∃ b, flag ↦ b //\\ (fun s => forall ρ π, Δ s ρ π -> snd (state ρ) = b).
    (* FIXME: the assertion below cannot handle the case with multiple possibilities *)
    (* separation of v and b is necessary *)
    (* ∃ v, @Aρ _ _ _ (li_lts F) (Idle (pair v b)). *)

  (* MARK: for the sake of simplicity, use race-free register *)
  (* Definition IRacy : assertion :=
    ∀ t, ∀ b', ∀ s, AFlag (fun b => b = Pending s t (set b'))
      ==>> (ALin' t (ls_inv (setFlag b'))). *)

  Definition I : assertion := Inv.

    (fun s => state (σ s) )
            ((state (σ s) = None /\
              exists ρt ρf, (Aρ ρt ⊕ Aρ ρf) s /\ state ρt = true /\ state ρf = false)
            \/ (exists b, state (σ s) = Some b /\
              exists ρ, Aρ ρ s /\ state ρ = b))
        /\  (forall v t w, σ s = Pending v t (set w) ->
              exists b : bool, @Aρ _ _ _ (li_lts F) (Pending b t flip) s)
        /\  ((forall v w t, σ s <> Pending v t (set w)) -> exists b, @Aρ _ _ _ (li_lts F) (Idle b) s).
    
  
  (* Definition I : assertion :=
    fun s =>
            (* state correspondence *)
            ((state (σ s) = None /\ forall b, exists ρ π, Δ s ρ π /\ state ρ = b) \/
            (exists b, state (σ s) = Some b /\ exists ρ π, Δ s ρ π /\ state ρ = b))
            (* racy set implies racy flip *)
        /\  (forall v t w, σ s = Pending v t (set w) ->
              exists ρ π, Δ s ρ π /\ exists b, ρ = Pending b t flip)
        /\  ((forall v w t, σ s <> Pending v t (set w)) -> forall ρ π, Δ s ρ π -> exists b, ρ = Idle b)
        . *)
  
  Lemma idle_not_pending : forall (u v w : option bool) t, Idle u <> Pending v t (set w).
  Proof. inversion 1. Qed.

  Definition π_independent (P : assertion) := forall s1 s2,
    σ s1 = σ s2 ->
    (forall ρ1 π1, Δ s1 ρ1 π1 -> exists ρ2 π2, Δ s2 ρ2 π2 /\ ρ1 = ρ2) ->
    (forall ρ2 π2, Δ s2 ρ2 π2 -> exists ρ1 π1, Δ s1 ρ1 π1 /\ ρ1 = ρ2) ->
    P s1 -> P s2.

  (* Lemma I_π_independent: π_independent I.
  Proof.
    unfold π_independent; intros.
    unfold I in *. rewrite H in *.
    destruct H2 as [? ?].
    split; [|split].
    - destruct H2.
      + left.
        destruct H2.
        split; auto.
        intros. specialize (H4 b) as [? [? [? ?]]].
        specialize (H0 _ _ H4) as [? [? [? ?]]]; subst.
        eauto.
      + right.
        destruct H2 as [b [? [? [? [? ?]]]]].
        specialize (H0 _ _ H4) as [? [? [? ?]]]; subst.
        eexists; eauto.
    - intros.
      eapply H3 in H4 as [? [? [? ?]]].
      specialize (H0 _ _ H4) as [? [? [? ?]]]; subst.
      eauto.
    - destruct H3. intros.
      apply H1 in H6 as [? [? [? ?]]]; subst.
      eapply H4; eauto.
  Qed. *)
  

  Definition domexact_G t : rg_relation := 
    fun s1 s2 => forall t', t <> t' ->
        forall ρ1 π1 ρ2 π2, Δ s1 ρ1 π1 -> Δ s2 ρ2 π2 -> TMap.find t' π1 = None <-> TMap.find t' π2 = None.
  
  Definition domexact_R t : rg_relation :=
    fun s1 s2 =>
      forall ρ1 π1 ρ2 π2, Δ s1 ρ1 π1 -> Δ s2 ρ2 π2 -> TMap.find t π1 = None <-> TMap.find t π2 = None.
  
  Lemma domexact_RG_compatible : forall t1 t2, t1 <> t2 -> (domexact_G t1 ⊆ domexact_R t2)%RGRelation.
  Proof.
    intros. intros ? ?.
    unfold domexact_R, domexact_G.
    intros. eapply H0; eauto.
  Qed.

  Lemma GINV_domexact : forall t1 t2, t1 <> t2 -> (GINV t1 ⊆ domexact_R t2)%RGRelation.
  Proof.
    intros. intros ? ?.
    unfold domexact_R, GINV, Ginv, LiftRelation_Δ.
    intros.
    destruct H0 as [? [? [? ?]]].
    apply H4 in H2.
    inversion H2; subst.
    rewrite PositiveMap.gso; auto.
    eapply (ac_domexact (Δ x)); eauto.
  Qed.

  Lemma GRET_domexact : forall t1 t2, t1 <> t2 -> (GRET t1 ⊆ domexact_R t2)%RGRelation.
  Proof.
    intros. intros ? ?.
    unfold domexact_R, GRET, Gret, LiftRelation_Δ.
    intros.
    destruct H0 as [? [? [? [? ?]]]].
    apply H4 in H2.
    inversion H2; subst.
    rewrite PositiveMap.gro; auto.
    eapply (ac_domexact (Δ x)); eauto.
  Qed.

  Lemma domexact_R_refl : forall t s, domexact_R t s s.
  Proof.
    intros. intros ? ?.
    unfold domexact_R, GId.
    intros; subst.
    eapply (ac_domexact (Δ s)); eauto.
  Qed.

  Definition G t : rg_relation := domexact_G t ∩
    fun s1 s2 => forall t' ls, t <> t' -> ALin t' ls s1 -> ALin t' ls s2.

  Definition R t : rg_relation := domexact_R t ∩
    fun s1 s2 => forall ls, ALin t ls s1 -> ALin t ls s2.

  Lemma Istable {t} : Stable (R t) I I.
  Proof. unfold Stable. apply ConjRightImpl, ImplRefl. Qed.

  Lemma ALinstable {t ls}: Stable (R t) I (ALin t ls).
  Proof.
    unfold Stable, R.
    intros ? [[? [? [? ?]]] ?] ? ? ?.
    apply H1 in H. apply H in H3. auto.
  Qed.

  Lemma ALin'stable {t ls}: Stable (R t) I (ALin' t ls).
  Proof.
    unfold Stable, R.
    intros ? [[? [? [? ?]]] ?] ? ? ?.
    apply H1 in H. apply H in H3. auto.
  Qed.

  Create HintDb stableDB.
  Hint Resolve Istable ALinstable : stableDB.



End CCASImpl.

Print Assumptions OneShotLazyCoinImpl.Mcoin.