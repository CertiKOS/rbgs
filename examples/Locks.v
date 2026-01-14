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


Module TicketDispenserImpl.
  Import LinCCALBase.
  Import LTSSpec.
  Import Lang.
  Import AssertionsSingle.
  Import RGILogic.
  Import TPSimulation.
  Import AtomicLTS FAISpec RegSpec TicketSpec.
  Import (coercions, canonicals, notations) Sig.
  Import (notations) LinCCAL.
  Import (canonicals) Sig.Plus.
  Open Scope prog_scope.
  
  Definition E : layer_interface :=
  {|
    li_sig := Sig.Plus.omap EFAI (EReg nat);
    li_lts := tens_lts VFAI VReg;
    li_init := (Idle O, Idle O);
  |}.
  
  Definition F : layer_interface :=
  {|
    li_sig := ETicket;
    li_lts := VTicket;
    li_init := Idle (TKS O nil O)
  |}.

  Definition acq_ticket_impl : Prog (li_sig E) nat :=
    inl fai >= t => Ret t.
  
  Definition cmp_ticket_impl t : Prog (li_sig E) bool :=
    inr get >= cur => Ret (t =? cur).

  Definition rel_ticket_impl : Prog (li_sig E) unit :=
    inr get >= cur =>
    inr (set (S cur)) >= _ =>
    Ret tt.

  Definition assertion := @Assertion _ _ (li_lts E) (li_lts F).
  Definition rg_relation := @RGRelation _ _ (li_lts E) (li_lts F).

  Definition TicketOwnedBy t : assertion :=
    fun s => exists q, ts_q (state (ρ s)) = t :: q.
  
  Lemma TicketOwnedExclusive {t t' s}:
    t <> t' -> TicketOwnedBy t s -> TicketOwnedBy t' s -> False.
  Proof.
    unfold TicketOwnedBy.
    intros ? [? ?] [? ?].
    rewrite H0 in H1. congruence.
  Qed.

  Definition RegVal v : assertion :=
    fun s => state (snd (σ s)) = v.

  Definition I : assertion :=
    fun s =>
          (* fai matches tail *)
          state (fst (σ s)) = ts_tl (state (ρ s))
          (* reg matches head *)
      /\  state (snd (σ s)) = ts_hd (state (ρ s))
          (* only owner can set tail *)
      /\  (forall t v w, snd (σ s) = Pending v t (set w) -> TicketOwnedBy t s)
      /\  exists tks, ρ s = Idle tks
    .
  
  Definition G t : rg_relation := 
      (* (G_lock t ∪ G_unlock t ∪ G_id t) ∩ *)
      fun s1 s2 => forall t', t <> t'
        -> TMap.find t' (π s1) = TMap.find t' (π s2)
          /\  (TicketOwnedBy t' s1 -> TicketOwnedBy t' s2 /\ state (snd (σ s1)) = state (snd (σ s2))).

  Definition R t : rg_relation :=
    fun s1 s2 =>
      (TicketOwnedBy t s1 -> TicketOwnedBy t s2 /\ state (snd (σ s1)) = state (snd (σ s2))) /\
      (TMap.find t (π s1) = TMap.find t (π s2)).

  Lemma Istable {t} : Stable (R t) I I.
  Proof. unfold Stable. apply ConjRightImpl, ImplRefl. Qed.
  
  Lemma ALinstable {t ls}: Stable (R t) I (ALin t ls).
  Proof.
    unfold Stable, ALin, R.
    intros ? [[? [? [? ?]]] ?].
    rewrite <- H1. auto.
  Qed.

  Lemma OwnedBystable {t} : Stable (R t) I (TicketOwnedBy t).
  Proof.
    unfold Stable, ALin, R.
    intros ? [[? [? [? ?]]] ?].
    destruct (H0 H). auto.
  Qed.

  Lemma OwnedRegValstable {t v} : Stable (R t) I (TicketOwnedBy t //\\ RegVal v).
  Proof.
    unfold Stable, ALin, R.
    intros ? [[? [[? ?] [? ?]]] ?].
    destruct (H1 H). split; auto.
    unfold RegVal in *; rewrite <- H5; auto.
  Qed.

  Create HintDb stableDB.
  Hint Resolve
    Istable
    ALinstable
    OwnedBystable
    OwnedRegValstable
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

  Program Definition Mticket : layer_implementation E F := {|
    li_impl m :=
      match m with
      | acq_ticket => acq_ticket_impl
      | cmp_ticket t => cmp_ticket_impl t
      | rel_ticket => rel_ticket_impl
      end
  |}.
  Next Obligation.
    eapply RGILogic.soundness with (R:=R) (G:=G) (I:=I).
    (* valid RG *)
    {
      constructor.
      unfold R. intros.
      destruct H.
      rewrite H1. tauto.
    }
    (* G ⊆ R *)
    {
      unfold G, R.
      intros. intros ? ? ?.
      destruct H0; [specialize (H0 _ H) as [? ?]; split; intros; auto|].
      unfold GINV, Ginv, GRET, Gret, GId, LiftRelation_π in H0;
      destruct H0 as [[? | ?] | ?]; eauto.
      - destruct H0 as (? & ? & ? & ? & ?).
        unfold TicketOwnedBy.
        split; [rewrite H0, H1|]; auto.
        rewrite H3. rewrite PositiveMap.gso; try tauto; auto.
      - destruct H0 as (? & ? & ? & ? & ? & ?).
        unfold TicketOwnedBy.
        split; [rewrite H0, H1|]; auto.
        rewrite H3. rewrite PositiveMap.gro; try tauto; auto.
      - subst; auto.
    }
    intros t; destruct f; simpl.
    (* acq *)
    {
      (* pre-condition *)
      exists (I //\\ ALin t (Semantics.ls_inv acq_ticket)).
      (* post-condition *)
      exists (fun ret => I //\\ ALin t (Semantics.ls_linr acq_ticket ret)).
      constructor;
      try solve_conj_impl;
      try solve_conj_stable stableDB;
      try apply IGinv; try apply IGret.
      {
        unfold ALin. intros.
        destruct H; auto.
      }
      simpl. unfold acq_ticket_impl.
      (* fai *)
      eapply provable_vis_safe with
        (P':=I //\\ ALin t (Semantics.ls_inv acq_ticket))
        (Q':=fun ret => I //\\ ALin t (Semantics.ls_linr acq_ticket ret));
      try solve_conj_impl;
      try solve_conj_stable stableDB;
      [solve_no_error| | | ].
      (* inv *)
      {
        pupdate_intros_atomic.
        pupdate_finish.
        split; auto. unfold G; intros; simpl; auto.
      }
      (* res *)
      {
        pupdate_intros_atomic.
        destruct Hpre as [[? [? [? [tks ?]]]] ?]; simpl in *; subst.
        destruct tks as [hd q tl]; simpl in *.
        pupdate_start.
        pupdate_forward t (InvEv acq_ticket).
        pupdate_forward t (ResEv acq_ticket tl).
        pupdate_finish.
        split.
        + unfold Semantics.linstate_atomic_step, ALin, I in *.
          split; simpl in *; [|apply PositiveMap.gss; auto].
          do 2 split; auto. split; eauto.
          intros; subst.
          specialize (H1 _ _ _ eq_refl) as [? ?].
          unfold TicketOwnedBy in *; simpl in *; subst.
          exists (x ++ t :: nil). auto.
        + unfold G. simpl. intros.
          do 2 (rewrite PositiveMap.gso; auto).
          split; auto. unfold TicketOwnedBy. simpl.
          intros [? ?]. split; auto.
          exists (x ++ t :: nil). subst; auto.
      }
      (* return *)
      intros.
      eapply provable_ret_safe; destruct ret;
      try solve_conj_impl;
      try solve_conj_stable stableDB;
      try apply ImplRefl.
    }
    (* cmp *)
    {
      rename t0 into tk. 
      (* pre-condition *)
      exists (I //\\ ALin t (Semantics.ls_inv (cmp_ticket tk))).
      (* post-condition *)
      exists (fun ret => I //\\ ALin t (Semantics.ls_linr (cmp_ticket tk) ret)).
      constructor;
      try solve_conj_impl;
      try solve_conj_stable stableDB;
      try apply IGinv; try apply IGret.
      {
        unfold ALin. intros.
        destruct H; auto.
      }
      simpl. unfold cmp_ticket_impl.
      (* get *)
      eapply provable_vis_safe with
        (P':=I //\\ ALin t (Semantics.ls_inv (cmp_ticket tk)))
        (Q':=fun ret => I //\\ ALin t (Semantics.ls_linr (cmp_ticket tk) (tk =? ret)));
      try solve_conj_impl;
      try solve_conj_stable stableDB;
      [solve_no_error| | | ].
      (* inv *)
      {
        pupdate_intros_atomic.
        pupdate_finish.
        do 2 split; destruct Hpre; auto.
        unfold I in *; simpl in *; subst; do 3 (split; try tauto).
        inversion 1.
      }
      (* res *)
      {
        pupdate_intros_atomic.
        destruct Hpre as [[? [? [? [tks ?]]]] ?]; simpl in *; subst.
        destruct tks as [hd q tl]; simpl in *.

        pupdate_start.
        pupdate_forward t (InvEv (cmp_ticket tk)).
        pupdate_forward t (ResEv (cmp_ticket tk) (tk =? hd)).
        pupdate_finish.

        split.
        + unfold Semantics.linstate_atomic_step, ALin, I in *.
          split; simpl in *; [|apply PositiveMap.gss; auto].
          do 2 (split; auto). split; eauto.
          inversion 1.
        + unfold G. simpl. intros.
          do 2 (rewrite PositiveMap.gso; auto).
      }
      (* return *)
      intros.
      eapply provable_ret_safe; destruct ret;
      try solve_conj_impl;
      try solve_conj_stable stableDB;
      try apply ImplRefl.
    }
    (* rel *)
    {
      (* pre-condition *)
      exists (I //\\ ALin t (Semantics.ls_inv rel_ticket)).
      (* post-condition *)
      exists (fun ret => I //\\ ALin t (Semantics.ls_linr rel_ticket ret)).
      constructor;
      try solve_conj_impl;
      try solve_conj_stable stableDB;
      try apply IGinv; try apply IGret.
      {
        unfold ALin. intros.
        destruct H; auto.
      }
      simpl. unfold rel_ticket_impl.
      (* perror *)
      eapply provable_perror with (P':=I //\\ ALin t (Semantics.ls_inv rel_ticket) //\\ TicketOwnedBy t).
      {
        unfold ALin, I. intros ? ?.
        destruct H as [[? [? [? [? ?]]]] ?].
        destruct s, ρ0; simpl in *; try congruence.
        inversion H2; subst.
        destruct x as [hd q tl]; simpl in *.
        destruct q as [| t' q];
        [ right; do 2 econstructor; simpl; eauto;
          constructor; eapply error_empty_queue; eauto |].
        destruct (Pos.eq_dec t t'); subst; simpl in *.
        - unfold TicketOwnedBy. left.
          do 2 (split; simpl; eauto).
        - right; do 2 econstructor; simpl; eauto;
          constructor; eapply error_jump_queue; eauto.
      }
      (* get *)
      eapply provable_vis_safe with
        (P':=I //\\ ALin t (Semantics.ls_inv rel_ticket) //\\ TicketOwnedBy t)
        (Q':=fun ret => I //\\ ALin t (Semantics.ls_inv rel_ticket) //\\ (TicketOwnedBy t //\\ RegVal ret));
      try solve_conj_impl;
      try solve_conj_stable stableDB;
      [solve_no_error| | | ].
      (* inv *)
      {
        pupdate_intros_atomic.
        pupdate_finish.
        
        do 2 split; destruct Hpre as [[? ?] ?]; auto.
        unfold I in *; simpl in *; subst; do 4 (split; try tauto).
        inversion 1.
      }
      (* res *)
      {
        pupdate_intros_atomic.
        destruct Hpre as [[[? [? [? [tks ?]]]] ?] ?]; simpl in *; subst.
        destruct tks as [hd q tl]; simpl in *.
        pupdate_finish.

        unfold I, TicketOwnedBy, RegVal.
        do 3 split; simpl; eauto.
        unfold I in *; simpl in *; subst; do 3 (split; try tauto; eauto).
        inversion 1.
      }
      intros v.
      (* set *)
      eapply provable_vis_safe with
        (P':=I //\\ ALin t (Semantics.ls_inv rel_ticket) //\\ (TicketOwnedBy t //\\ RegVal v))
        (Q':=fun ret => I //\\ ALin t (Semantics.ls_linr rel_ticket tt));
      try solve_conj_impl;
      try solve_conj_stable stableDB;
      [ | | | ].
      (* safe *)
      {
        intros ? ([? ?] & ? & ?) ?.
        destruct s, σ0; simpl in *.
        inversion H3; subst.
        destruct H as (_ & _ & ? & _).
        specialize (H _ _ _ eq_refl).
        eapply TicketOwnedExclusive; eauto.
      }
      (* inv *)
      {
        pupdate_intros_atomic.
        pupdate_finish.

        do 2 split; destruct Hpre as [[? ?] ?]; auto.
        unfold I in *; simpl in *; subst; do 4 (split; try tauto).
        inversion 1; subst.
        destruct H1. auto.
      }
      (* res *)
      {
        pupdate_intros_atomic.
        destruct Hpre as [[[? [? [? [tks ?]]]] ?] [[q' ?] ?]]; simpl in *; subst.
        destruct tks as [hd q tl]; subst; simpl in *.
        inversion Hstep; subst.

        pupdate_start.
        pupdate_forward t (InvEv rel_ticket).
        pupdate_forward t (ResEv rel_ticket tt).
        pupdate_finish.

        split.
        + unfold Semantics.linstate_atomic_step, ALin, I in *.
          split; simpl in *; [|apply PositiveMap.gss; auto].
          do 2 split; auto. split; eauto. inversion 1.
        + unfold G. simpl. intros.
          do 2 (rewrite PositiveMap.gso; auto).
          split; auto. unfold TicketOwnedBy. simpl.
          intros [? ?]. congruence.
      }

      (* return *)
      intros.
      eapply provable_ret_safe; destruct ret;
      try solve_conj_impl;
      try solve_conj_stable stableDB;
      try apply ImplRefl.
    }
    {
      unfold I; simpl.
      do 3 (split; eauto).
      inversion 1.
    }
  Defined.

  Print Assumptions Mticket.

End TicketDispenserImpl.



Module TicketLockImpl.
  Import LinCCALBase.
  Import LTSSpec.
  Import Lang.
  Import AssertionsSingle.
  Import RGILogic.
  Import TPSimulation.
  Import AtomicLTS TicketSpec LockSpec.
  Import (coercions, canonicals, notations) Sig.
  Import (notations) LinCCAL.
  Import (canonicals) Sig.Plus.
  Import List.

  Open Scope nat.
  Open Scope list.
  Open Scope prog_scope.

  Definition E : layer_interface :=
  {|
    li_sig := ETicket;
    li_lts := VTicket;
    li_init := Idle (TKS O nil O);
  |}.
  
  Definition F : layer_interface :=
  {|
    li_sig := ELock;
    li_lts := VLock;
    li_init := Idle Unlocked
  |}.
  
  Definition acq_impl : Prog (li_sig E) unit :=
    (*
      NotInQueue t /\ (Unlocked \/ exists t' <> t, Locked t')
      \/
      exists tk', InQueue t tk'
    *)
    acq_ticket >= my =>
    (*
      InQueue t my /\
      (Unlocked \/ exists t' <> t, Locked t' \/ exists tk', (InQueue t tk' /\ tk' < my))
    *)
    Do {
      cmp_ticket my >= b => Ret b
      (* if b then linearized else (InQueue t my) *)
    } While (negb b) >= b =>
    Ret tt.

  Definition rel_impl : Prog (li_sig E) unit :=
    (* OwnedBy t *)
    rel_ticket >= _ => Ret tt.
  
  Definition assertion := @Assertion _ _ (li_lts E) (li_lts F).
  Definition rg_relation := @RGRelation _ _ (li_lts E) (li_lts F).

  Open Scope rg_relation_scope.
  Open Scope assertion_scope.

  Definition InQueue t mytk : assertion :=
    fun s => nth_error (ts_q (state (σ s))) (mytk - ts_hd (state (σ s))) = Some t /\ ts_hd (state (σ s)) <= mytk.

  Definition TicketOwnedBy t : assertion :=
    fun s => exists q, ts_q (state (σ s)) = t :: q.

  Definition NotOwned : assertion :=
    fun s => state (ρ s) = Unlocked.
  
  Definition OwnedBy t : assertion :=
    fun s => state (ρ s) = Locked t.
  
  Definition NotOwnedBy t : assertion :=
    fun s => state (ρ s) <> Locked t.

  Definition DuplicateAcqOrNot t tk : assertion :=
    fun s => NotOwned s \/ (exists t', t <> t' /\ OwnedBy t' s) \/ (exists tk', InQueue t tk' s /\ tk' < tk).

  Definition I : assertion :=
    fun s => 
          (exists ls, ρ s = Idle ls)
      /\  (forall t, OwnedBy t s -> TicketOwnedBy t s)
      /\  (length (ts_q (state (σ s))) = (ts_tl (state (σ s)) - ts_hd (state (σ s))))
      /\  (ts_hd (state (σ s)) <= ts_tl (state (σ s))).

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

  Definition G t : rg_relation :=
    fun s1 s2 => forall t', t <> t'
        -> TMap.find t' (π s1) = TMap.find t' (π s2)
            /\ (OwnedBy t' s1 <-> OwnedBy t' s2)
            /\ (forall tk, InQueue t' tk s1 <-> InQueue t' tk s2).

  Definition R t : rg_relation :=
    fun s1 s2 =>
          (OwnedBy t s1 <-> OwnedBy t s2)
      /\  (forall tk, InQueue t tk s1 <-> InQueue t tk s2)
      /\  (TMap.find t (π s1) = TMap.find t (π s2)).

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
    intros ? [[? [? [? [? ?]]]] ?].
    rewrite <- H2. auto.
  Qed.
  
  Lemma InQueuestable {t tk}: Stable (R t) I (InQueue t tk).
  Proof.
    unfold Stable, R.
    intros ? [[? [? [? [? ?]]]] ?].
    destruct (H1 tk); auto.
  Qed.

  Lemma DuplicateAcqOrNotstable {t tk} : Stable (R t) I (DuplicateAcqOrNot t tk).
  Proof.
    unfold Stable, R, DuplicateAcqOrNot.
    intros ? [[? [? [? [? ?]]]] ?].
    destruct s, x. unfold InQueue in *. simpl in *.
    unfold I in *. unfold NotOwned, OwnedBy, TicketOwnedBy in *. simpl in *.
    destruct (state ρ0); [right|tauto].
    destruct (Pos.eq_dec t t0) eqn:eq; subst; [right|eauto].
    destruct H3 as [? [? [? ?]]].
    specialize (H4 _ eq_refl).
    destruct H0 as [_ ?]. specialize (H0 eq_refl).
    destruct H as [? | [[? [? ?]] | [tk' [? ?]]]]; try congruence.
    exists tk'. split; auto.
    eapply H1; auto.
  Qed.

  Create HintDb stableDB.
  Hint Resolve Istable OwnedBystable ALinstable InQueuestable DuplicateAcqOrNotstable : stableDB.

  Lemma IGinv : forall t f, ⊨ Ginv t f ⊚ I ==>> I //\\ ALin t (Semantics.ls_inv f).
  Proof.
    unfold I, ALin.
    intros ? ? [? ?] [? [[[? ?] (? & ? & ?)] (? & ? & ? & ?)]]; simpl in *; subst.
    do 3 try split; eauto; simpl in *.
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
  
  Program Definition Mlock : layer_implementation E F := {|
    li_impl m :=
      match m with
      | acq => acq_impl
      | rel => rel_impl
      end
  |}.
  Next Obligation.
    eapply RGILogic.soundness with (R:=R) (G:=G) (I:=I).
    (* valid RG *)
    {
      constructor.
      unfold R. intros.
      destruct H as [? [? ?]]. rewrite H2. tauto.
    }
    (* G ⊆ R *)
    {
      unfold G, R.
      intros. intros ? ? [[? [? ?]] | ?]; eauto.
      destruct H0 as [[? | ?] | ?].
      + unfold GINV, Ginv, LiftRelation_π in *.
        destruct H0 as (? & ? & ? & ? & ?).
        unfold OwnedBy, InQueue.
        rewrite H0, H1. do 2 (split; auto; try tauto).
        rewrite H3, PositiveMap.gso; try tauto; auto.
      + unfold Gret, LiftRelation_π in *.
        destruct H0 as (? & ? & ? & ? & ? & ?).
        unfold OwnedBy, InQueue.
        rewrite H0, H1. do 2 (split; auto; try tauto).
        rewrite H3. rewrite PositiveMap.gro; try tauto; auto.
      + destruct H0; subst. tauto.
    }
    (* method provable *)
    {
      intros t. destruct f.
      (* acq *)
      {
        (* pre-condition *)
        exists (I //\\ ALin t (Semantics.ls_inv acq)).
        (* post-condition *)
        exists (fun ret => I //\\ ALin t (Semantics.ls_linr acq ret)).
        constructor;
        try solve_conj_impl;
        try solve_conj_stable stableDB;
        try apply IGinv; try apply IGret.
        {
          unfold ALin. intros.
          destruct H; auto.
        }
        simpl. unfold acq_impl.
        (* conseq pre *)
        eapply provable_conseq_weak_pre with (P':=I //\\ ALin t (Semantics.ls_inv acq) //\\ (fun s => exists tk, DuplicateAcqOrNot t tk s)).
        {
          intros ? ?. split; auto.
          unfold DuplicateAcqOrNot.
          destruct s. unfold InQueue in *. simpl in *.
          unfold I, NotOwned, OwnedBy, TicketOwnedBy in *. simpl in *.
          destruct H as [[? [? [? ?]]] ?]. simpl in *.
          destruct (state ρ0); [|exists O; tauto].
          destruct (Pos.eq_dec t t0) eqn:eq; subst; [|exists O; eauto].
          specialize (H0 _ eq_refl) as [? ?].
          exists (ts_hd (state σ0) + 1). right; right.
          rewrite H0. exists (ts_hd (state σ0)); simpl.
          assert ((ts_hd (state σ0) - ts_hd (state σ0)) = O) by lia.
          rewrite H4. simpl. split; try lia; auto.
        }
        (* fai *)
        eapply provable_vis_safe with
          (P':=I //\\ ALin t (Semantics.ls_inv acq) //\\ (fun s => exists tk, DuplicateAcqOrNot t tk s))
          (Q':=fun mytk => I //\\ ALin t (Semantics.ls_inv acq) //\\ InQueue t mytk //\\ DuplicateAcqOrNot t mytk);
        try solve_conj_impl;
        try solve_conj_stable stableDB;
        [ | | | | ].
        (* safe *)
        {
          intros ? ? ?.
          destruct s. simpl in *. inversion H0; subst.
          inversion Herror; subst.
          - dependent destruction H2.
          - dependent destruction H1.
        }
        (* stable *)
        {
          apply ConjStable; [solve_conj_stable stableDB|].
          intros ? [[? [[? ?] ?]] ?].
          exists x0.
          apply DuplicateAcqOrNotstable.
          split; auto.
          eexists. split; eauto.
        }
        (* inv *)
        {
          pupdate_intros_atomic.
          inversion Hstep0; subst; inversion_thread_event_eq.
          pupdate_finish.
          split; auto. unfold G; intros; simpl; tauto.
        }
        (* res *)
        {
          pupdate_intros_atomic.
          inversion Hstep0; subst; inversion_thread_event_eq.
          dependent destruction H2.
          destruct Hpre as [[[[ls ?] [? [? ?]]] ?] [tk' ?]]; simpl in *; subst.
          pupdate_finish.
          
          do 3 try split; eauto; try tauto.
          - unfold I. simpl. do 3 (try split; eauto);
            unfold OwnedBy, TicketOwnedBy in *; simpl in *; eauto.
            + intros; subst.
              specialize (H0 _ eq_refl) as [? ?]; subst.
              exists (x ++ t1 :: nil). auto.
            + rewrite app_length, H1. simpl.
              destruct hd; simpl; lia.
          - unfold InQueue. simpl.
            rewrite <- H1, nth_error_app2; try lia.
            destruct (length q - length q) eqn:eq; split; try lia; auto.
          - destruct H4 as [? | [? | ?]];
            unfold DuplicateAcqOrNot, NotOwned, OwnedBy in *; simpl in *; try tauto.
            do 2 right. destruct H as [tk ?]. exists tk.
            unfold InQueue in *; simpl in *. do 2 destruct H.
            assert (nth_error q (tk - hd) <> None) by congruence.
            apply nth_error_Some in H6. split; try lia.
            rewrite nth_error_app1; auto.
          - unfold InQueue. simpl. intros. split; intros [? ?].
            + rewrite nth_error_app1; try tauto.
              apply nth_error_Some; congruence.
            + destruct (S (tk - hd) - length q) eqn:eq.
              * rewrite nth_error_app1 in H5; try lia; split; auto.
              * rewrite nth_error_app2 in H5; try lia.
                destruct (tk - hd - length q); simpl in H5; inversion H5;
                try congruence. destruct n0; simpl in *; congruence.
        }
        intros mytk.
        eapply provable_seq.
        (* loop *)
        {
          eapply provable_dowhile with (Q:=
            fun b : bool => if b 
                            then I //\\ ALin t (Semantics.ls_linr acq tt)
                            else I //\\ ALin t (Semantics.ls_inv acq) //\\ InQueue t mytk //\\ DuplicateAcqOrNot t mytk
                            
          );
          try solve [destruct a; solve_conj_impl];
          try solve [destruct a; solve_conj_stable stableDB].
          (* loop invariant *)
          {
            unfold APure.
            intros ? ? [? ?].
            destruct a; auto.
            inversion H0.
          }
          (* loop body *)
          {
            eapply provable_vis_safe with
              (P':=(I //\\ ALin t (Semantics.ls_inv acq)) //\\ InQueue t mytk //\\ DuplicateAcqOrNot t mytk)
              (Q':=fun b : bool => if b 
                            then I //\\ ALin t (Semantics.ls_linr acq tt)
                            else I //\\ ALin t (Semantics.ls_inv acq) //\\ InQueue t mytk //\\ DuplicateAcqOrNot t mytk);
            try solve_conj_impl;
            try solve_conj_stable stableDB;
            try solve [destruct a; solve_conj_impl];
            try solve [destruct a; solve_conj_stable stableDB].
            (* safe *)
            {
              intros ? ? ?.
              destruct s. simpl in *. inversion H0; subst.
              inversion Herror; subst.
              - dependent destruction H2.
              - dependent destruction H1.
            }
            (* inv *)
            {
              pupdate_intros_atomic.
              inversion Hstep0; subst; inversion_thread_event_eq.
              destruct Hpre as [[[? ?] [? ?]] ?].
              pupdate_finish.
              do 4 try split; simpl in *; eauto.
            }
            (* res *)
            {
              intros b.
              pupdate_intros_atomic.
              inversion Hstep0; subst; inversion_thread_event_eq.
              dependent destruction H3.
              destruct Hpre as [[[? ?] ?] ?].
              
              destruct (tk =? ts_hd s0) eqn:eq.
              - (* succeeded *)
                rewrite Nat.eqb_eq in eq; subst.
                destruct H as [[ls ?] [? [? ?]]]; simpl in *; subst.
                destruct H2 as [? | [? | ?]].
                + (* unlocked *)
                  unfold NotOwned in H. simpl in *; subst.
                
                  pupdate_start.
                  pupdate_forward t1 (InvEv acq).
                  pupdate_forward t1 (ResEv acq tt).
                  pupdate_finish.
                  
                  split.
                  * unfold Semantics.linstate_atomic_step, ALin, I in *.
                    split; simpl in *; [|apply PositiveMap.gss; auto].
                    split; eauto. split; auto.
                    intros; subst. unfold OwnedBy in *. simpl in *.
                    inversion H; subst. unfold TicketOwnedBy. simpl.
                    destruct H1 as [? ?]. simpl in *.
                    replace (ts_hd s0 - ts_hd s0) with O in H1 by lia.
                    destruct (ts_q s0); inversion H1; subst. eauto.
                  * unfold G. simpl in *. intros.
                    do 2 (rewrite PositiveMap.gso; auto).
                    unfold OwnedBy, InQueue in *; simpl in *.
                    do 2 (split; auto; try tauto).
                    split; congruence.
                + destruct H as [? [? ?]].
                  apply H3 in H2.
                  unfold TicketOwnedBy in H2; simpl in *.
                  unfold InQueue in H1. simpl in *.
                  destruct H2. rewrite H2 in H1.
                  replace (ts_hd s0 - ts_hd s0) with O in H1 by lia.
                  simpl in H1; destruct H1. congruence.
                + destruct H as [? [[? ?] ?]].
                  simpl in *. lia.
              - (* failed *)
                destruct H1.
                pupdate_finish.
                do 4 try split; eauto.
            }
            intros.
            eapply provable_ret_safe;
            destruct ret;
            try solve_conj_impl;
            try solve_conj_stable stableDB.
          }
        }
        (* ret *)
        {
          intros.
          eapply provable_ret_safe;
          try solve_conj_impl;
          try solve_conj_stable stableDB.
          intros ? [? ?]. unfold APure in H0.
          destruct a; simpl in H0; try congruence; auto.
        }
      }
      (* rel *)
      {
        (* pre-condition *)
        exists (I //\\ ALin t (Semantics.ls_inv rel)).
        (* post-condition *)
        exists (fun ret => I //\\ ALin t (Semantics.ls_linr rel ret)).
        constructor;
        try solve_conj_impl;
        try solve_conj_stable stableDB;
        try apply IGinv; try apply IGret.
        {
          unfold ALin. intros.
          destruct H; auto.
        }
        simpl. unfold rel_impl.
        (* perror *)
        eapply provable_perror with (P':=I //\\ ALin t (Semantics.ls_inv rel) //\\ OwnedBy t).
        {
          intros ? [([ls ?] & ? & ? & ?) ?].
          destruct ls; [destruct (Pos.eq_dec t t0)|]; subst.
          - left. unfold I; do 2 try split; eauto.
            unfold OwnedBy. rewrite H; auto.
          - right. constructor. rewrite H.
            econstructor; eauto. do 2 constructor; auto.
          - right. constructor. rewrite H.
            econstructor; eauto. do 2 constructor; auto.
        }
        (* rel *)
        eapply provable_vis_safe with
          (P':=(I //\\ ALin t (Semantics.ls_inv rel)) //\\ OwnedBy t)
          (Q':=fun _ => I //\\ ALin t (Semantics.ls_linr rel tt));
        try solve_conj_impl;
        try solve_conj_stable stableDB;
        [ | | | ].
        (* safe *)
        {
          intros ? [[(? & ? & ? & ?) ?] ?].
          destruct s.
          inversion 1; subst. inversion Herror; subst;
          simpl in *; subst; simpl in *;
          apply H0 in H4; destruct H4; simpl in *; congruence.
        }
        (* inv *)
        {
          pupdate_intros_atomic.
          pupdate_finish.
          inversion Hstep0; subst; inversion_thread_event_eq.
          split; auto. unfold G; intros; simpl; tauto.
        }
        (* res *)
        {
          pupdate_intros_atomic.
          inversion Hstep0; subst; inversion_thread_event_eq.
          dependent destruction H2.
          destruct Hpre as [[([? ?] & ? & ? & ?) ?] ?].
          unfold OwnedBy in *. do 2 (simpl in *; subst).

          pupdate_start.
          pupdate_forward t1 (InvEv rel).
          pupdate_forward t1 (ResEv rel tt).
          pupdate_finish.
          
          split.
          * unfold Semantics.linstate_atomic_step, ALin, I in *.
            split; simpl in *; [|apply PositiveMap.gss; auto].
            do 2 (split; eauto; try tauto; try lia).
            intros; subst. unfold OwnedBy in *. simpl in *.
            inversion H; subst.
          * unfold G. simpl in *. intros.
            do 2 (rewrite PositiveMap.gso; auto).
            unfold OwnedBy, InQueue in *; simpl in *.
            do 2 (split; auto; try tauto).
            split; congruence. split; intros [? ?].
            - destruct (tk - hd) eqn:eq; simpl in H4; try congruence.
              assert ((tk - S hd) = n) by lia. rewrite H6.
              split; auto. lia.
            - split; try lia.
              assert ((tk - hd) = S ((tk - S hd))) by lia.
              rewrite H6; simpl. auto.
        }
        (* ret *)
        intros.
        eapply provable_ret_safe;
        try solve_conj_impl;
        try solve_conj_stable stableDB.
        apply ImplRefl.
      }
    }
    {
      unfold I. simpl.
      do 2 (split; eauto).
      unfold OwnedBy, TicketOwnedBy. simpl. inversion 1.
    }
  Defined.

  Print Assumptions Mlock.
End TicketLockImpl.

