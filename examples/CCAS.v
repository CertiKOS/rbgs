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


  Lemma conj_from_imp : forall (P Q : Prop), P -> (P -> Q) -> P /\ Q.
  Proof. eauto. Qed.
  
  Lemma conj_right_imp {P Q R : Prop} :
    (Q -> R) -> (P /\ Q) -> (P /\ R).
  Proof. tauto. Qed.

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

Module CASTaskImpl.
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
    li_init := Idle (cts (inr vInit) O (fun _ => Inactive));
  |}.

  Definition allocTask_impl (_ : tid) : Prog (li_sig E) nat :=
    inr fai >= i => Ret i.
  
  Definition tryPlaceTask_impl o n i (cid : tid) : Prog (li_sig E) ((CASTask Val) + Val) :=
    inl (cas (inr o) (inl (CTask cid o n i))) >= r => Ret r.
  
  Definition tryResolveTask_impl tsk v (_ : tid) : Prog (li_sig E) unit :=
    inl (cas (inl tsk) (inr v)) >= _ => Ret tt.
  
  Definition assertion := @Assertion (@ProofState _ _ (li_lts E) (li_lts F)).
  Definition rg_relation := @RGRelation _ _ (li_lts E) (li_lts F).

  Open Scope rg_relation_scope.
  Open Scope assertion_scope.
  
  Definition ALinEx t ls : assertion := fun s => exists ρ π, Δ s ρ π /\ TMap.find t π = ls.

  Definition SafeTicket i : assertion :=
    fun s => forall ρ π, Δ s ρ π -> owner (state ρ) i <> Inactive.

  Definition I_cas : assertion := fun s =>
    forall ρ π, Δ s ρ π ->
      state (fst (σ s)) = current (state ρ).

  Definition I_ticket : assertion := fun s =>
    forall ρ π, Δ s ρ π ->
      state (snd (σ s)) = ticket (state ρ) /\
      forall i, ticket (state ρ) <= i -> owner (state ρ) i = Inactive.

  Definition I_atomic : assertion := fun s =>
    exists ρ π c, Δ s ≡ [(ρ , π)] /\ ρ = Idle c.
    
  Definition I : assertion :=
    I_atomic //\\ I_cas //\\ I_ticket.
  
  Definition R t : rg_relation :=
    fun s1 s2 =>
      (forall ls, ALinEx t ls s1 <-> ALinEx t ls s2)
      /\ (forall i, SafeTicket i s1 -> SafeTicket i s2).
  
  Definition G_id : rg_relation :=
    fun s1 s2 =>
      state (fst (σ s1)) = state (fst (σ s2)) /\
      state (snd (σ s1)) = state (snd (σ s2)) /\
      Δ s1 ≡ Δ s2.

  Definition G_other t : rg_relation :=
    fun s1 s2 => forall t', t <> t' -> R t' s1 s2.
  
  Definition G t := G_id ∪ G_other t.

  Ltac simpl_all :=
    unfold R, G, G_id, G_other, I, I_atomic, I_ticket, I_cas, SafeTicket, owner_upd,
          Conj, Disj, Imply in *; simpl in *.

  Lemma RG_compatible : forall t1 t2, t1 <> t2 -> (I ⊓ G t1 ⊆ R t2).
  Proof.
    intros. intros ? ? [? ?].
    destruct H0.
    - unfold G_id, R, ALinEx, SafeTicket in *.
      split.
      + split; intros [? [? [HΔ ?]]];
        apply H0 in HΔ; do 2 eexists; eauto.
      + intros. apply H0 in H3. eauto.
    - apply H0; eauto.
  Qed.

  Lemma R_domexact : forall t0 s1 s2, R t0 s1 s2 -> I s2 ->
    (forall (ρ1 : State (li_lts F)) (π1 : tmap LinState), Δ s1 ρ1 π1 -> TMap.find t0 π1 = None) <->
    (forall (ρ2 : State (li_lts F)) (π2 : tmap LinState), Δ s2 ρ2 π2 -> TMap.find t0 π2 = None).
  Proof.
    intros.
    split; intros.
    - pose proof ac_nonempty (Δ s1) as [? [? ?]].
      apply H1 in H3 as ?.
      assert (ALinEx t0 None s1) by (do 2 eexists; eauto).
      apply H in H5 as [? [? [? ?]]].
      eapply (ac_domexact (Δ s2)) in H6; eauto.
    - pose proof ac_nonempty (Δ s2) as [? [? ?]].
      apply H1 in H3 as ?.
      assert (ALinEx t0 None s2) by (do 2 eexists; eauto).
      apply H in H5 as [? [? [? ?]]].
      eapply (ac_domexact (Δ s1)) in H6; eauto.
  Qed.

  Lemma ALinLinExI : forall t ls s,
    I s -> (ALinEx t (Some ls) s <-> ALin t ls s).
  Proof.
    intros. destruct H as [[? [? [? [? ?]]]]].
    split; intros.
    - intros ? ? ?. apply H in H3; inversion H3; subst.
      destruct H2 as [? [? [? ?]]].
      apply H in H0; inversion H0; subst. auto.
    - exists x, x0. split; [apply H; constructor|].
      pose proof ac_nonempty (Δ s) as [? [? ?]].
      apply H in H3; inversion H3; subst.
      eapply H2. apply H; eauto.
  Qed.

  Lemma ALinLinEx : forall t ls s,
    ALin t ls s -> ALinEx t (Some ls) s.
  Proof.
    intros.
    pose proof ac_nonempty (Δ s) as [? [? ?]].
    apply H in H0 as ?. do 2 eexists; eauto.
  Qed.

  Lemma stable_ALin : forall t ls, Stable (R t) I (ALin t ls).
  Proof.
    intros. intros ? [[? [? ?]] ?].
    rewrite <- ALinLinExI; eauto. apply H0.
    apply ALinLinEx; auto.
  Qed.

  Lemma stable_I : forall t, Stable (R t) I I.
  Proof. intros. intros ? [[? [? ?]] ?]; auto. Qed.

  Lemma stable_SafeTicket : forall t i, Stable (R t) I (SafeTicket i).
  Proof.
    intros. intros ? [[? [? ?]] ?].
    apply H0. auto.
  Qed.

  Lemma G_id_I : ⊨ G_id ⊚ I ==>> I.
  Proof.
    intros ? [? [? [? [? ?]]]].
    destruct H as [[? [? [? [? ?]]]] [? ?]]; subst.
    simpl_all. rewrite H0 in *. rewrite H1 in *.
    split; [|split]; eauto.
    - exists (Idle x2), x1, x2.
      split; auto. etransitivity; eauto. symmetry; auto.
    - intros. apply H2 in H3; eauto.
    - intros. apply H2 in H3; eauto.
  Qed.

  Create HintDb stableDB.
  Hint Resolve stable_I stable_ALin stable_SafeTicket
  : stableDB.

  Lemma G_id_G : forall s1 s2 t, G_id s1 s2 -> G t s1 s2.
  Proof. left; auto. Qed.
  
  Ltac post_pupdate_id :=
            eapply conj_right_imp; [apply G_id_G |];
                    apply and_comm, conj_from_imp; intros.

  Program Definition MCASTask : layer_implementation E F := {|
    li_impl m :=
      match m with
      | allocTask _ _ => allocTask_impl
      | tryPlaceTask o n i => tryPlaceTask_impl o n i
      | tryResolveTask tsk v => tryResolveTask_impl tsk v
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
      intros. intros s1 s2 [[? | ?] HI];
      [eapply RG_compatible; eauto; try (split; auto)|].
      destruct H0 as [[? | ?] | ?].
      - unfold GINV, Ginv, LiftRelation_Δ in *.
        destruct H0 as [? [? [? ?]]].
        split.
        * split; intros [? [? [? ?]]].
          + exists x0, (TMap.add t1 (ls_inv x) x1).
            split; [|rewrite TMap.gso;auto].
            apply H2. constructor; auto.
          + apply H2 in H3. inversion H3; subst.
            do 2 eexists; split; eauto.
            rewrite TMap.gso; auto.
        * unfold SafeTicket. intros.
          apply H2 in H4. inversion H4; subst. eauto.
      - unfold GRET, Gret, LiftRelation_Δ in *.
        destruct H0 as [? [? [? [? ?]]]].
        split.
        * split; intros [? [? [? ?]]].
          + exists x1, (TMap.remove t1 x2).
            split; [|rewrite TMap.gro;auto].
            apply H2. constructor; auto.
          + apply H2 in H3. inversion H3; subst.
            do 2 eexists; split; eauto.
            rewrite TMap.gro; auto.
        * unfold SafeTicket. intros.
          apply H2 in H4. inversion H4; subst. eauto.
      - unfold GId in *; subst. unfold R. tauto.
    }
    (* method provable *)
    {
      intros t f.
      exists (I //\\ ALin t (ls_inv f)).
      exists (fun r => I //\\ ALin t (ls_linr f r)).
      constructor;
      try solve_conj_impl;
      try solve_stable stableDB.
      (* invocation *)
      {
        intros ? [s' [? [? [? ?]]]]. simpl_all.
        rewrite H0 in *.
        destruct H as [[? [? [? [? ?]]]] [? ?]]; subst.
        split;[split;[|split]|].
        - exists (Idle x1), (TMap.add t (ls_inv f) x0).
          exists x1; split; auto.
          etransitivity; eauto.
          split; inversion 1; subst; try constructor; eauto.
          + apply H in Hposs; inversion Hposs; subst; auto.
            constructor.
          + apply H. constructor.
        - intros. apply H2 in H3; inversion H3; subst. eauto.
        - intros. apply H2 in H3. inversion H3; subst. eauto.
        - intros ? ? ?. apply H2 in H3; inversion H3; subst.
          rewrite TMap.gss; eauto.
      }
      (* response *)
      {
        intros ? ? [? [[? ?] [? [? ?]]]]. simpl_all.
        rewrite H1 in *.
        destruct H as [[? [? [? [? ?]]]] [? ?]]; subst.
        split;[|split].
        - exists (Idle x2), (TMap.remove t x1).
          exists x2; split; auto.
          etransitivity; eauto.
          split; inversion 1; subst; try constructor; eauto.
          + apply H in Hposs; inversion Hposs; subst; auto.
            constructor.
          + apply H. constructor.
        - intros. apply H3 in H4; inversion H4; subst. eauto.
        - intros. apply H3 in H4; inversion H4; subst. eauto.
      }
      {
        intros. destruct H as [_ ?]. eauto.
      }
      (* method body *)
      {
        destruct f.
        (* alloc *)
        {
          simpl.
          eapply provable_vis_safe with
            (P' := I //\\ ALin t (ls_inv (allocTask o n)))
            (Q' := fun r : nat => I //\\ ALin t (ls_linr (allocTask o n) r));
          try solve_no_error;
          try solve_conj_impl;
          try solve_stable stableDB.
          (* inv *)
          {
            pupdate_intros_atomic.
            dependent destruction Hstep.
            pupdate_start. eapply ac_steps_refl.
            
            post_pupdate_id.
            { unfold G_id; simpl; do 2 (split; auto); reflexivity. }
            destruct Hpre as [? ?].
            split; [apply G_id_I; eexists; eauto|].
            intros ? ? ?.
            apply H1 in H2. auto.
          }
          (* res *)
          {
            pupdate_intros_atomic.
            dependent destruction Hstep.
            destruct Hpre as [? ?].
            pose proof ac_nonempty (Δ1) as [? [? ?]].
            apply H0 in H1 as ?.
            destruct H as [[? [? [? [? ?]]]] ?].
            apply H in H1 as HΔ; inversion HΔ; subst. simpl in *.
            destruct x3.

            pupdate_start.
            pupdate_trylin_from H1.
            pupdate_forward t (InvEv (allocTask o n)).
            pupdate_forward t (ResEv (allocTask o n) ticket0).
            pupdate_finish.
            eapply ACTrylinFinish.

            repeat split; simpl_all.
            - exists (Idle {| current := current0; ticket := S ticket0; owner := owner_upd owner0 ticket0 (Owned t) |}).
              exists (TMap.add t (ls_linr (allocTask o n) ticket0) (TMap.add t (ls_lini (allocTask o n)) x0)).
              eexists; split; [|split;eauto].
              constructor; inversion 1; subst; try constructor; eauto.
              pupdate_forward t (InvEv (allocTask o n)).
              pupdate_forward t (ResEv (allocTask o n) ticket0).
              pupdate_finish.
            - inversion 1; subst. simpl in *.
              destruct H4.
              apply H4 in H1. eauto.
            - inversion H3; subst. simpl. apply f_equal.
              apply H4 in H1 as [? ?]. eauto.
            - inversion H3; subst. simpl.
              apply H4 in H1 as [? ?]. simpl in *.
              intros. unfold owner_upd.
              destruct (Nat.eqb_spec ticket0 i); subst; eauto; try lia.
              eapply H5. lia.
            - inversion 1; subst. simpl_all.
              rewrite TMap.gss; eauto.
              apply H4 in Hposs as [? ?]; simpl in *. subst. eauto.
            - right. intros. simpl_all.
              split.
              * split; intros [? [? [? ?]]]; [|inversion H5;subst].
                + exists (Idle {| current := current0; ticket := S ticket0; owner := owner_upd owner0 ticket0 (Owned t) |}),
                  (TMap.add t (ls_linr (allocTask o n) ticket0) (TMap.add t (ls_lini (allocTask o n)) x0)).
                  apply H in H5 as HΔ'; inversion HΔ'; simpl in *; subst.
                  simpl. split; [constructor|do 2 (rewrite TMap.gso; eauto) ]; eauto.
                  pupdate_forward t (InvEv (allocTask o n)).
                  pupdate_forward t (ResEv (allocTask o n) ticket0).
                  pupdate_finish.
                + exists (Idle {| current := current0; ticket := ticket0; owner := owner0 |}), x0. split; eauto.
                  do 2 (rewrite TMap.gso; eauto).
              * intros. inversion H6; subst. simpl in *.
                apply H5 in Hposs. simpl in *.
                destruct (Nat.eqb_spec ticket0 i); subst; eauto.
                congruence.
          }
          intros.
          eapply provable_ret;
          try solve_conj_impl;
          try solve_stable stableDB.
          left; auto.
        }
        (* place *)
        {
          simpl.
          eapply provable_vis_safe with
            (P' := I //\\ ALin t (ls_inv (tryPlaceTask o n i)))
            (Q' := fun r => I //\\ ALin t (ls_linr (tryPlaceTask o n i) r));
          try solve_no_error;
          try solve_conj_impl;
          try solve_stable stableDB.
          (* inv *)
          {
            pupdate_intros_atomic.
            dependent destruction Hstep.
            pupdate_start. eapply ac_steps_refl.
            
            post_pupdate_id.
            { unfold G_id; simpl; do 2 (split; auto); reflexivity. }
            destruct Hpre as [? ?].
            split; [apply G_id_I; eexists; eauto|].
            intros ? ? ?.
            apply H1 in H2. auto.
          }
          (* res *)
          {
            pupdate_intros_atomic;
            dependent destruction Hstep.
            (* succeed *)
            {
              destruct Hpre as [? ?].
              pose proof ac_nonempty (Δ1) as [? [? ?]].
              apply H0 in H1 as ?.
              destruct H as [[? [? [? [? ?]]]] ?].
              apply H in H1 as HΔ; inversion HΔ; subst. simpl in *.
              destruct x3.
              pose proof H4 as [? _]. apply H3 in H1 as ?; simpl in *. subst.

              pupdate_start.
              pupdate_trylin_from H1.
              eapply rt_trans.
              eapply rt_step, ps_inv; eauto.
              do 2 constructor.
              eapply rt_step, ps_ret; eauto.
              constructor. eapply step_tryPlaceTask_succ; eauto.
              rewrite TMap.gss; auto.
              eapply ACTrylinFinish.

              repeat split; simpl_all.
              - exists (Idle {| current := inl (CTask t0 o n i); ticket := ticket0; owner := owner0 |}),
                (TMap.add t0 (ls_linr (tryPlaceTask o n i) (inr o)) (TMap.add t0 (ls_lini (tryPlaceTask o n i)) x0)).
                eexists; split; [|split;eauto].
                constructor; inversion 1; subst; try constructor; eauto.
                eapply rt_trans.
                eapply rt_step, ps_inv; eauto.
                do 2 constructor.
                eapply rt_step, ps_ret; eauto.
                constructor. eapply step_tryPlaceTask_succ; eauto.
                rewrite TMap.gss; auto.
              - inversion 1; subst. simpl in *.
                destruct H4.
                apply H4 in H1. eauto.
              - inversion H5; subst. simpl.
                apply H4 in H1 as [? ?]. eauto.
              - inversion H5; subst. simpl.
                apply H4 in H1 as [? ?]. simpl in *.
                intros. unfold owner_upd.
                destruct (Nat.eqb_spec ticket0 i); subst; eauto; try lia.
              - inversion 1; subst. simpl_all.
                rewrite TMap.gss; eauto.
              - right. intros. simpl_all.
                split.
                * split; intros [? [? [? ?]]]; [|inversion H6;subst].
                  + exists (Idle {| current := inl (CTask t0 o n i); ticket := ticket0; owner := owner0 |}),
                      (TMap.add t0 (ls_linr (tryPlaceTask o n i) (inr o)) (TMap.add t0 (ls_lini (tryPlaceTask o n i)) x0)).
                    apply H in H6 as HΔ'; inversion HΔ'; simpl in *; subst.
                    simpl. split; [constructor|do 2 (rewrite TMap.gso; eauto) ]; eauto.
                    eapply rt_trans.
                    eapply rt_step, ps_inv; eauto.
                    do 2 constructor.
                    eapply rt_step, ps_ret; eauto.
                    constructor. eapply step_tryPlaceTask_succ; eauto.
                    rewrite TMap.gss; auto.
                  + do 2 eexists; split; eauto.
                    do 2 (rewrite TMap.gso; eauto).
              * intros. inversion H7; subst. simpl in *.
                apply H6 in Hposs. simpl in *.
                destruct (Nat.eqb_spec ticket0 i); subst; eauto.
            }
            (* fail *)
            {
              clear H0. rename H1 into Hneq.
              destruct Hpre as [? ?].
              pose proof ac_nonempty (Δ1) as [? [? ?]].
              apply H0 in H1 as ?.
              destruct H as [[? [? [? [? ?]]]] ?]. subst.
              apply H in H1 as HΔ; inversion HΔ; subst. simpl in *.
              destruct x3.
              pose proof H4 as [? _]. apply H3 in H1 as ?; simpl in *. subst.
              destruct current0.
              (* fail *)
              {
                pupdate_start.
                pupdate_trylin_from H1.
                eapply rt_trans.
                eapply rt_step, ps_inv; eauto.
                do 2 constructor.
                eapply rt_step, ps_ret; eauto.
                constructor. eapply step_tryPlaceTask_block; eauto.
                rewrite TMap.gss; auto.
                eapply ACTrylinFinish.

                repeat split; simpl_all.
                - exists (Idle {| current := inl c; ticket := ticket0; owner := owner0 |}),
    (TMap.add t0 (ls_linr (tryPlaceTask o n i) (inl c)) (TMap.add t0 (ls_lini (tryPlaceTask o n i)) x0)).
                  eexists; split; [|split;eauto].
                  constructor; inversion 1; subst; try constructor; eauto.
                  eapply rt_trans.
                  eapply rt_step, ps_inv; eauto.
                  do 2 constructor.
                  eapply rt_step, ps_ret; eauto.
                  constructor. eapply step_tryPlaceTask_block; eauto.
                  rewrite TMap.gss; auto.
                - inversion 1; subst. simpl in *.
                  destruct H4.
                  apply H4 in H1. eauto.
                - inversion H5; subst. simpl.
                  apply H4 in H1 as [? ?]. eauto.
                - inversion H5; subst. simpl.
                  apply H4 in H1 as [? ?]. simpl in *.
                  intros. unfold owner_upd.
                  destruct (Nat.eqb_spec ticket0 i); subst; eauto; try lia.
                - inversion 1; subst. simpl_all.
                  rewrite TMap.gss; eauto.
                - right. intros. simpl_all.
                  split.
                  * split; intros [? [? [? ?]]]; [|inversion H6;subst].
                    + exists (Idle {| current := inl c; ticket := ticket0; owner := owner0 |}),
      (TMap.add t0 (ls_linr (tryPlaceTask o n i) (inl c)) (TMap.add t0 (ls_lini (tryPlaceTask o n i)) x0)).
                      apply H in H6 as HΔ'; inversion HΔ'; simpl in *; subst.
                      simpl. split; [constructor|do 2 (rewrite TMap.gso; eauto) ]; eauto.
                      eapply rt_trans.
                      eapply rt_step, ps_inv; eauto.
                      do 2 constructor.
                      eapply rt_step, ps_ret; eauto.
                      constructor. eapply step_tryPlaceTask_block; eauto.
                      rewrite TMap.gss; auto.
                    + do 2 eexists; split; eauto.
                      do 2 (rewrite TMap.gso; eauto).
                  * intros. inversion H7; subst. simpl in *.
                    apply H6 in Hposs. simpl in *.
                    destruct (Nat.eqb_spec ticket0 i); subst; eauto.
              }
              (* fail *)
              {
                assert (Hneq' : v <> o) by congruence.
                pupdate_start.
                pupdate_trylin_from H1.
                eapply rt_trans.
                eapply rt_step, ps_inv; eauto.
                do 2 constructor.
                eapply rt_step, ps_ret; eauto.
                constructor. eapply step_tryPlaceTask_fail; eauto.
                rewrite TMap.gss; auto.
                eapply ACTrylinFinish.

                repeat split; simpl_all.
                - exists (Idle {| current := inr v; ticket := ticket0; owner := owner0 |}),
    (TMap.add t0 (ls_linr (tryPlaceTask o n i) (inr v)) (TMap.add t0 (ls_lini (tryPlaceTask o n i)) x0)).
                  eexists; split; [|split;eauto].
                  constructor; inversion 1; subst; try constructor; eauto.
                  eapply rt_trans.
                  eapply rt_step, ps_inv; eauto.
                  do 2 constructor.
                  eapply rt_step, ps_ret; eauto.
                  constructor. eapply step_tryPlaceTask_fail; eauto.
                  rewrite TMap.gss; auto.
                - inversion 1; subst. simpl in *.
                  destruct H4.
                  apply H4 in H1. eauto.
                - inversion H5; subst. simpl.
                  apply H4 in H1 as [? ?]. eauto.
                - inversion H5; subst. simpl.
                  apply H4 in H1 as [? ?]. simpl in *.
                  intros. unfold owner_upd.
                  destruct (Nat.eqb_spec ticket0 i); subst; eauto; try lia.
                - inversion 1; subst. simpl_all.
                  rewrite TMap.gss; eauto.
                - right. intros. simpl_all.
                  split.
                  * split; intros [? [? [? ?]]]; [|inversion H6;subst].
                    + exists (Idle {| current := inr v; ticket := ticket0; owner := owner0 |}),
      (TMap.add t0 (ls_linr (tryPlaceTask o n i) (inr v)) (TMap.add t0 (ls_lini (tryPlaceTask o n i)) x0)).
                      apply H in H6 as HΔ'; inversion HΔ'; simpl in *; subst.
                      simpl. split; [constructor|do 2 (rewrite TMap.gso; eauto) ]; eauto.
                      eapply rt_trans.
                      eapply rt_step, ps_inv; eauto.
                      do 2 constructor.
                      eapply rt_step, ps_ret; eauto.
                      constructor. eapply step_tryPlaceTask_fail; eauto.
                      rewrite TMap.gss; auto.
                    + do 2 eexists; split; eauto.
                      do 2 (rewrite TMap.gso; eauto).
                  * intros. inversion H7; subst. simpl in *.
                    apply H6 in Hposs. simpl in *.
                    destruct (Nat.eqb_spec ticket0 i); subst; eauto.
              }
            }
          }
          intros.
          eapply provable_ret;
          try solve_conj_impl;
          try solve_stable stableDB.
          left; auto.
        }
        (* resolve *)
        {
          simpl.
          destruct tsk.
          eapply provable_perror with
            (P' := I //\\ ALin t (ls_inv (tryResolveTask (CTask t0 o n i) v))
                    //\\ SafeTicket i).
          {
            intros ? [? ?].
            assert (SafeTicket i s \/ ~ SafeTicket i s) by apply classic.
            destruct H1; [left; do 2 (split; auto)|right].
            assert ((exists ρ π, Δ s ρ π /\ owner (state ρ) i = Inactive) \/ ~ (exists ρ π, Δ s ρ π /\ owner (state ρ) i = Inactive)) by apply classic.
            destruct H2.
            2:{
              exfalso. apply H1.
              intros ? ? ? ?.
              apply H2. eauto.
            }
            clear H1. destruct H2 as [? [? [? ?]]].
            econstructor; [exact H1|].
            apply rt_step.
            apply H0 in H1 as ?.
            econstructor; eauto.
            destruct H as [[? [? [? [? ?]]]] _].
            apply H in H1. inversion H1; subst.
            constructor. destruct x3.
            econstructor; eauto.
          }

          eapply provable_vis_safe with
            (P' := I //\\ ALin t (ls_inv (tryResolveTask (CTask t0 o n i) v)) //\\ SafeTicket i)
            (Q' := fun _ => I //\\ ALin t (ls_linr (tryResolveTask (CTask t0 o n i) v) tt));
          try solve_no_error;
          try solve_conj_impl;
          try solve_stable stableDB.
          (* inv *)
          {
            pupdate_intros_atomic.
            dependent destruction Hstep.
            pupdate_start. eapply ac_steps_refl.
            
            post_pupdate_id.
            { unfold G_id; simpl; do 2 (split; auto); reflexivity. }
            destruct Hpre as [? [? ?]].
            split; [apply G_id_I; eexists; eauto|].
            split.
            + intros ? ? ?.
              apply H1 in H3. auto.
            + intros ? ? ?. apply H in H3.
              apply H2 in H3. eauto.
          }
          (* res *)
          {
            pupdate_intros_atomic;
            dependent destruction Hstep.
            (* has task placed *)
            {
              destruct Hpre as [? [? Hticket]].
              pose proof ac_nonempty (Δ1) as [? [? ?]].
              apply H0 in H1 as ?.
              destruct H as [[? [? [? [? ?]]]] ?].
              apply H in H1 as HΔ; inversion HΔ; subst. clear HΔ. simpl in *.
              destruct x3.
              assert (current0 = inl (CTask t0 o n i) \/ current0 <> inl (CTask t0 o n i)) by apply classic.
              destruct H3 as [? | Hneq]; subst.
              (* succeed *)
              {
                pupdate_start.
                pupdate_trylin_from H1.
                eapply rt_trans.
                eapply rt_step, ps_inv; eauto.
                do 2 constructor.
                eapply rt_step, ps_ret; eauto; [|rewrite TMap.gss; auto].
                constructor. eapply step_tryResolveTask_succ; eauto.
                eapply ACTrylinFinish.

                  (* * intros. inversion H7; subst. simpl in *.
                    apply H6 in Hposs. simpl in *.
                    destruct (Nat.eqb_spec ticket0 i); subst; eauto. *)

                repeat split; simpl_all.
                - exists(Idle
                    {|
                      current := inr v;
                      ticket := ticket0;
                      owner := fun i' : nat => if i =? i' then Expired else owner0 i'
                    |}),
                  (TMap.add t1 (ls_linr (tryResolveTask (CTask t0 o n i) v) tt)
                    (TMap.add t1 (ls_lini (tryResolveTask (CTask t0 o n i) v)) x0)).
                  eexists; split; [|split;eauto].
                  constructor; inversion 1; subst; try constructor; eauto.
                  eapply rt_trans.
                  eapply rt_step, ps_inv; eauto.
                  do 2 constructor.
                  eapply rt_step, ps_ret; eauto; [|rewrite TMap.gss; auto].
                  constructor. eapply step_tryResolveTask_succ; eauto.
                - inversion 1; subst. simpl in *.
                  destruct H4.
                  apply H4 in H1. eauto.
                - inversion H3; subst. simpl.
                  apply H4 in H1 as [? ?]. eauto.
                - inversion H3; subst. simpl.
                  apply H4 in H1 as [? ?]. simpl in *.
                  intros. unfold owner_upd.
                  destruct (Nat.eqb_spec i i0); subst; eauto; try lia.
                  simpl_all.
                  apply Hticket in Hposs as ?. simpl in *.
                  apply H5 in H6. congruence.
                - inversion 1; subst. simpl_all.
                  rewrite TMap.gss; eauto.
                - right. intros. simpl_all.
                  split.
                  * split; intros [? [? [? ?]]]; [|inversion H6;subst].
                    + exists (Idle
                    {|
                      current := inr v;
                      ticket := ticket0;
                      owner := fun i' : nat => if i =? i' then Expired else owner0 i'
                    |}),
                  (TMap.add t1 (ls_linr (tryResolveTask (CTask t0 o n i) v) tt)
                    (TMap.add t1 (ls_lini (tryResolveTask (CTask t0 o n i) v)) x0)). simpl.
                      apply H in H5 as HΔ'; inversion HΔ'; simpl in *; subst.
                      simpl. split; [constructor|do 2 (rewrite TMap.gso; eauto) ]; eauto.
                      eapply rt_trans.
                      eapply rt_step, ps_inv; eauto.
                      do 2 constructor.
                      eapply rt_step, ps_ret; eauto.
                      constructor. eapply step_tryResolveTask_succ; eauto.
                      rewrite TMap.gss; auto.
                    + simpl_all. inversion H5; subst.
                      do 2 eexists; split; eauto.
                      do 2 (rewrite TMap.gso; eauto).
                  * intros. inversion H6; subst. simpl in *.
                    apply H5 in Hposs as ?. simpl in *. 
                    destruct (Nat.eqb_spec i i0); subst; eauto. congruence.
              }
              (* fail *)
              {
                pupdate_start.
                pupdate_trylin_from H1.
                eapply rt_trans.
                eapply rt_step, ps_inv; eauto.
                do 2 constructor.
                eapply rt_step, ps_ret; eauto; [|rewrite TMap.gss; auto].
                constructor. eapply step_tryResolveTask_fail; eauto.
                eapply ACTrylinFinish.

                  (* * intros. inversion H7; subst. simpl in *.
                    apply H6 in Hposs. simpl in *.
                    destruct (Nat.eqb_spec ticket0 i); subst; eauto. *)

                repeat split; simpl_all.
                - exists (Idle {| current := current0; ticket := ticket0; owner := owner0 |}),
                (TMap.add t1 (ls_linr (tryResolveTask (CTask t0 o n i) v) tt)
                  (TMap.add t1 (ls_lini (tryResolveTask (CTask t0 o n i) v)) x0)).
                  eexists; split; [|split;eauto].
                  constructor; inversion 1; subst; try constructor; eauto.
                  eapply rt_trans.
                  eapply rt_step, ps_inv; eauto.
                  do 2 constructor.
                  eapply rt_step, ps_ret; eauto; [|rewrite TMap.gss; auto].
                  constructor. eapply step_tryResolveTask_fail; eauto.
                - destruct H4. apply H3 in H1. simpl in *. congruence.
                - inversion H3; subst. simpl.
                  apply H4 in H1 as [? ?]. eauto.
                - inversion H3; subst. simpl.
                  apply H4 in H1 as [? ?]. simpl in *.
                  intros. unfold owner_upd.
                  destruct (Nat.eqb_spec i i0); subst; eauto; try lia.
                - inversion 1; subst. simpl_all.
                  rewrite TMap.gss; eauto.
                - right. intros. simpl_all.
                  split.
                  * split; intros [? [? [? ?]]]; [|inversion H6;subst].
                    + exists (Idle {| current := current0; ticket := ticket0; owner := owner0 |}),
                      (TMap.add t1 (ls_linr (tryResolveTask (CTask t0 o n i) v) tt)
                        (TMap.add t1 (ls_lini (tryResolveTask (CTask t0 o n i) v)) x0)). simpl.
                      apply H in H5 as HΔ'; inversion HΔ'; simpl in *; subst.
                      simpl. split; [constructor|do 2 (rewrite TMap.gso; eauto) ]; eauto.
                      eapply rt_trans.
                      eapply rt_step, ps_inv; eauto.
                      do 2 constructor.
                      eapply rt_step, ps_ret; eauto.
                      constructor. eapply step_tryResolveTask_fail; eauto.
                      rewrite TMap.gss; auto.
                    + simpl_all. inversion H5; subst.
                      do 2 eexists; split; eauto.
                      do 2 (rewrite TMap.gso; eauto).
                  * intros. inversion H6; subst. simpl in *.
                    apply H5 in Hposs as ?. simpl in *. 
                    destruct (Nat.eqb_spec i i0); subst; eauto.
              }
            }
            (* fail *)
            {
              clear H0. rename H1 into Hneq.
              destruct Hpre as [? [? Hticket]].
              pose proof ac_nonempty (Δ1) as [? [? ?]].
              apply H0 in H1 as ?.
              destruct H as [[? [? [? [? ?]]]] ?].
              apply H in H1 as HΔ; inversion HΔ; subst. clear HΔ. simpl in *.
              destruct x3.
              pose proof H4 as [Hcas _].
              apply Hcas in H1 as ?. simpl in *; subst ret. clear Hcas.

              pupdate_start.
              pupdate_trylin_from H1.
              eapply rt_trans.
              eapply rt_step, ps_inv; eauto.
              do 2 constructor.
              eapply rt_step, ps_ret; eauto; [|rewrite TMap.gss; auto].
              constructor. eapply step_tryResolveTask_fail; eauto.
              eapply ACTrylinFinish.

                (* * intros. inversion H7; subst. simpl in *.
                  apply H6 in Hposs. simpl in *.
                  destruct (Nat.eqb_spec ticket0 i); subst; eauto. *)

              repeat split; simpl_all.
              - exists (Idle {| current := current0; ticket := ticket0; owner := owner0 |}),
              (TMap.add t1 (ls_linr (tryResolveTask (CTask t0 o n i) v) tt)
                (TMap.add t1 (ls_lini (tryResolveTask (CTask t0 o n i) v)) x0)).
                eexists; split; [|split;eauto].
                constructor; inversion 1; subst; try constructor; eauto.
                eapply rt_trans.
                eapply rt_step, ps_inv; eauto.
                do 2 constructor.
                eapply rt_step, ps_ret; eauto; [|rewrite TMap.gss; auto].
                constructor. eapply step_tryResolveTask_fail; eauto.
              - inversion 1; subst. auto.
              - inversion H3; subst. simpl.
                apply H4 in H1 as [? ?]. eauto.
              - inversion H3; subst. simpl.
                apply H4 in H1 as [? ?]. simpl in *.
                intros. unfold owner_upd.
                destruct (Nat.eqb_spec i i0); subst; eauto; try lia.
              - inversion 1; subst. simpl_all.
                rewrite TMap.gss; eauto.
              - right. intros. simpl_all.
                split.
                * split; intros [? [? [? ?]]]; [|inversion H6;subst].
                  + exists (Idle {| current := current0; ticket := ticket0; owner := owner0 |}),
                    (TMap.add t1 (ls_linr (tryResolveTask (CTask t0 o n i) v) tt)
                      (TMap.add t1 (ls_lini (tryResolveTask (CTask t0 o n i) v)) x0)). simpl.
                    apply H in H5 as HΔ'; inversion HΔ'; simpl in *; subst.
                    simpl. split; [constructor|do 2 (rewrite TMap.gso; eauto) ]; eauto.
                    eapply rt_trans.
                    eapply rt_step, ps_inv; eauto.
                    do 2 constructor.
                    eapply rt_step, ps_ret; eauto.
                    constructor. eapply step_tryResolveTask_fail; eauto.
                    rewrite TMap.gss; auto.
                  + simpl_all. inversion H5; subst.
                    do 2 eexists; split; eauto.
                    do 2 (rewrite TMap.gso; eauto).
                * intros. inversion H6; subst. simpl in *.
                  apply H5 in Hposs as ?. simpl in *. 
                  destruct (Nat.eqb_spec i i0); subst; eauto.
            }
          }
          intros.
          eapply provable_ret;
          try solve_conj_impl;
          try solve_stable stableDB.
          left; auto.
        }
      }
    }
    {
      simpl_all.
      repeat split.
      - exists (Idle {| current := inr vInit; ticket := 0; owner := fun _ : nat => Inactive |}), (TMap.empty LinState); eexists; split; eauto.
        reflexivity.
      - inversion 1; subst. simpl. auto.
      - inversion H; subst; auto.
      - inversion H; subst; auto.
    }
  Qed.
End CASTaskImpl.


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
    li_init := Idle (pair vInit true);
  |}.

  Definition assertion := @Assertion (@ProofState _ _ (li_lts E) (li_lts F)).
  Definition rg_relation := @RGRelation _ _ (li_lts E) (li_lts F).

  Open Scope rg_relation_scope.
  Open Scope assertion_scope.

  Definition ALinExv t ls v : assertion :=
      fun s => exists ρ π, Δ s ρ π /\ TMap.find t π = ls /\ (fst (state ρ)) = v.
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
  
  Lemma ALinIdleExv : forall t, ⊨ ALinIdle t ==>> ∃ v, ALinExv t None v.
  Proof.
    intros ? ? [? [? [? ?]]].
    exists (fst (state x)).
    do 2 eexists; eauto.
  Qed.

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
      exists ρ π, Δ s ≡ [(ρ, π)] /\ fst (state ρ) = v.
      (* forall ρ π, Δ s ρ π -> fst (state ρ) = v. *)

  Definition NotDone t o n : assertion :=
    fun s =>
      exists ρ π, Δ s ρ π /\
      TMap.find t π = Some (ls_inv (cas o n)) /\
      fst (state ρ) = o.

  Definition I_cur_task : assertion :=
    ∀ t o n i , CurrentTask (CTask t o n i) ==>>
      (
        OwnedBy i t //\\
        (!! ALinIdle t) //\\
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
      (forall t f r, ALin t (ls_linr f r) s1 -> ALin t (ls_linr f r) s2) /\
      (exists t o n i, CurrentTask (CTask t o n i) s1 /\
        forall t', t <> t' -> forall ls, ALin t' ls s1 -> ALin t' ls s2) /\
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

  Definition G_id : rg_relation :=
    fun s1 s2 =>
      state (fst (σ s1)) = state (fst (σ s2)) /\
      state (snd (σ s1)) = state (snd (σ s2)) /\
      Δ s1 ≡ Δ s2.

  Definition R_task t : rg_relation :=
    fun s1 s2 =>
      (* only the owner can place the task *)
      (forall o n i, CurrentTask (CTask t o n i) s2 -> CurrentTask (CTask t o n i) s1) /\
      (* no one removing any task *)
      (forall t o n i, CurrentTask (CTask t o n i) s1 ->
        CurrentTask (CTask t o n i) s2 /\
        (forall ls v, ALinExv t (Some ls) v s1 -> ALinExv t (Some ls) v s2)).

  Definition R_IsExpired : rg_relation :=
    fun s1 s2 => forall i, IsExpired i s1 -> IsExpired i s2.

  Definition R_notplaced t : rg_relation :=
    fun s1 s2 => forall i, NotPlacedBy i t s1 -> NotPlacedBy i t s2.

  (* need this to ensure domexact *)
  (* actually more than domexact *)
  Definition R_id t : rg_relation :=
    fun s1 s2 => 
      forall ls ρ, ALinExv t ls ρ s1 <-> ALinExv t ls ρ s2.

  (* Definition R_id' t : rg_relation :=
    fun s1 s2 => 
      forall ls, ALinEx t ls s1 <-> ALinEx t ls s2. *)

  Definition R_flag t : rg_relation :=
    fun s1 s2 =>
      forall b, ALin t (ls_inv (setFlag b)) s1 -> ALin t (ls_inv (setFlag b)) s2.

  Definition G_fail t : rg_relation :=
    fun s1 s2 => forall t', t <> t' ->
      (R_IsExpired ∩ R_notplaced t' ∩ R_task t' ∩ R_id t' ∩ R_flag t') s1 s2.
  
  (* Definition G_flag t : rg_relation :=
    fun s1 s2 =>
      state (fst (σ s1)) = state (fst (σ s2)) /\
      state (snd (σ s1)) = state (snd (σ s2)) /\
      Δ s1 ≡ Δ s2. *)

  Definition G t : rg_relation :=
    G_id ∪ G_alloc t ∪ G_place_task t ∪ G_trylin ∪ G_resolve ∪ G_fail t.

  Definition R t : rg_relation :=
    R_IsExpired ∩ R_notplaced t ∩ R_flag t ∩
    ((R_task t ∩ R_id t) ∪ G_trylin ∪ G_resolve).

    
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

  Lemma ALinExvCongruence : forall t ls1 ls2 ρ,
    ⊨ ALin t ls1 ==>> ALinExv t ls2 ρ ==>> ⌜Some ls1 = ls2⌝.
  Proof.
    intros. intros ? [? [? [? [? ?]]]].
    apply H0 in H1. congruence.
  Qed.

  Lemma RG_compatible : forall t1 t2, t1 <> t2 -> (I ⊓ G t1 ⊆ R t2).
  Proof.
    intros. intros s1 s2 ?.
    destruct H1 as [[[[[[? | ?] | ?] | ?] | ?] | ?] HI].
    - destruct H1 as [? [? ?]].
      unfold R, R_IsExpired, IsExpired, R_notplaced, NotPlacedBy, OwnedBy, Neg, CurrentTask, Conj, Forall, R_task, R_id, CurrentTask, ALinEx.
      repeat split; try solve [ rewrite H1 in *; eauto; try tauto ].
      + intros ?. eapply ALin_equiv; eauto.
      + do 2 left. 
        split;[split|]; try rewrite H1; try tauto.
        * intros. split; auto. intros ? ? [? [? [? [? ?]]]].
          apply H3 in H5. eexists; eauto.
        * split; intros [? [? [? [? ?]]]]; apply H3 in H4; do 2 eexists; eauto.
    - destruct H1 as [? ?].
      specialize (H2 _ _ eq_refl eq_refl) as [? [? [? ?]]].
      split;[split;[split|]|].
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
      + intros ?. eapply ALin_equiv; eauto.
      + do 2 left. split.
        * unfold R_task, CurrentTask, Forall, ALinEx.
          rewrite H2. split; try tauto.
          intros; split; auto.
          intros ? ? [? [? [? [? ?]]]].
          apply H1 in H7; eexists; eauto.
        * unfold R_id, ALinExv.
          split; intros [? [? [HΔ ?]]];
          apply H1 in HΔ; do 2 eexists; eauto.
    - destruct H1 as [[? [? [? [? ?]]]] [? ?]].
      specialize (H4 _ _ eq_refl eq_refl) as [? ?].
      split;[split;[split|]|].
      + unfold R_IsExpired, IsExpired; intros.
        rewrite <- H5. auto.
      + unfold R_notplaced, NotPlacedBy, OwnedBy. intros ? [? ?].
        rewrite H5 in H6. split; auto.
        intros ? ? ?.
        eapply CurrentTaskCongruence in H2; eauto.
        congruence.
      + intros ?. eapply ALin_equiv; eauto.
      + do 2 left. split.
        * split; intros.
          eapply CurrentTaskCongruence in H2; eauto. congruence.
          eapply TaskValConflict in H1; eauto; inversion H1.
        * unfold R_id, ALinEx.
          split; intros [? [? [HΔ ?]]];
          apply H3 in HΔ; do 2 eexists; eauto.
    - split; [|left; right; auto].
      destruct H1 as [? [_ [[? [? [? [? ?]]]] ?]]].
      specialize (H3 _ _ eq_refl eq_refl) as [? [? ?]].
      split; [split|].
      + unfold R_IsExpired, IsExpired.
        rewrite H5. auto.
      + unfold R_notplaced, NotPlacedBy, OwnedBy, CurrentTask, Forall, Neg.
        intros ? [? ?]. rewrite H3 in *. rewrite H5 in *.
        split; auto.
      + intros ? ?.
        destruct H2.
        apply HI in H2 as [_ [_ [? [? [? [? _]]]]]].
        destruct (Pos.eq_dec x t2); auto; subst.
        apply H6 in H2. clear - H2 H8.
        change (@LinState (li_sig F)) with (@LinState (ECCAS Val)) in H8.
        rewrite H2 in H8. congruence.
    - split; [| right; auto].
      destruct H1 as [[? ?] [? [? [? [? [? [? ?]]]]]]].
      specialize (H4 _ _ eq_refl eq_refl) as [? [? ?]].
      split; [split|].
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
      + destruct H3 as [? [? [? [? ?]]]].
        intros ? ? ? ? ?.
        apply H3 in H10; inversion H10; subst.
        apply H7 in H10. eauto.
    - specialize (H1 _ H0) as [[[[? ?] ?] ?] ?].
      split; [split; [split|]|]; auto.
      do 2 left. split; auto.
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
        assert (ALinExv t0 None (fst (state ρ1)) s1); unfold ALinExv; eauto.
        apply H0 in H5 as [? [? [? [? ?]]]].
        eapply ac_domexact; eauto.
      + pose proof ac_nonempty (Δ s2) as [ρ2 [π2 ?]].
        specialize (H2 _ _ H4).
        assert (ALinExv t0 None (fst (state ρ2)) s2); unfold ALinExv; eauto.
        apply H0 in H5 as [? [? [? [? ?]]]].
        eapply ac_domexact; eauto.
    (* - destruct H0 as (t & o & n & i & [_ [_ [_ ?]]]).
      split; intros; apply H0 in H3; eapply H2; eauto. *)
    - destruct H0 as [HΔ [_ [[t [o [n [i ?]]]] ?]]].
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
      rewrite Hσ in *.
      apply HI in H1 as [? [? [? ?]]]; subst.
      pose proof ac_nonempty (Δ s) as [? [? ?]].
      pose proof H2.
      apply HΔ in H2. inversion H2; subst.
      apply H1 in Hposs. inversion Hposs; subst.
      exists x1, (TMap.add t0 (ls_inv f) π). split; auto.
      etransitivity; eauto.
      split.
      + inversion 1; subst.
        apply H1 in Hposs0; inversion Hposs0; subst.
        constructor.
      + inversion 1; subst; auto.
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
      rewrite Hσ in *. apply HI in H1 as [? [? [? ?]]]; subst.
      exists x, (TMap.remove t0 x0); split; auto.
      etransitivity; eauto.
      split; inversion 1; subst.
      + apply H1 in Hposs. inversion Hposs; subst; constructor.
      + constructor. apply H1; constructor.
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
  
  Lemma G_id_G : forall s1 s2 t, G_id s1 s2 -> G t s1 s2.
  Proof. do 5 left; auto. Qed.

  Lemma G_trylin_G : forall s1 s2 t, G_trylin s1 s2 -> G t s1 s2.
  Proof. do 2 left; right; auto. Qed.

  Lemma G_resolve_G : forall s1 s2 t, G_resolve s1 s2 -> G t s1 s2.
  Proof. left; right; auto. Qed.

  Lemma Istable {t} : Stable (R t) I I.
  Proof. unfold Stable. apply ConjRightImpl, ImplRefl. Qed.

  Lemma stable_not_cur_task : forall t o n i,
    Stable (R t) I (!! CurrentTask (CTask t o n i)).
  Proof.
    unfold Stable, R.
    intros. intros [[s0 [? [? ?]]] ?].
    destruct H2 as [[? | ?] | ?].
    - intros ?. apply H2, H0 in H4. auto.
    - destruct H2 as [? [_ [[? [? [? [? ?]]]] ?]]].
      specialize (H5 _ _ eq_refl eq_refl) as [? [? ?]].
      unfold CurrentTask, Neg in *.
      rewrite H5 in *. eauto.
    - destruct H2 as [[? ?] [? [? [? [? [? [? ?]]]]]]].
      intros ?.
      eapply TaskValConflict in H2; eauto.
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

  Lemma stable_alin_flag : forall t b,
    Stable (R t) I (ALin t (ls_inv (setFlag b))).
  Proof.
    unfold Stable, R.
    intros. intros [[? [? [[_ ?] _]]] ?].
    eauto.
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
      assert (ALinExv t0 (TMap.find t0 π) (fst (state ρ)) s); [eexists; eauto|].
      apply H4 in H8.
      eapply ALinExvCongruence in H8; eauto.
    - destruct H4 as [? [_ [[? [? [? [? ?]]]] ?]]].
      specialize (H7 _ _ eq_refl eq_refl).
      apply H5 in H1 as [? ?].
      pose proof ac_nonempty (Δ s0) as [? [? ?]].
      pose proof H8.
      apply H4 in H8.
      apply H0 in H9.
      intros ? ? ?.
      apply H1 in H10, H8.
      change (li_sig F) with (ECCAS Val) in H8.
      rewrite H8 in H9; subst.
      rewrite H9 in H10; auto.
    - destruct H4 as [[? ?] [? [? [? [? [? [? ?]]]]]]].
      destruct H7 as [ρ [π [? [? ?]]]].
      intros ? ? ?.
      apply H7, H9, H0 in H11; auto.
  Qed.

  Lemma stable_notplaced: forall t i,
    Stable (R t) I (NotPlacedBy i t).
  Proof.
    unfold Stable, R.
    intros. intros ?.
    destruct H0 as [[? [? [[[_ ?] _] _]]] ?].
    eauto.
  Qed.

  Lemma stable_alinidle: forall t,
    Stable (R t) I (!! ALinIdle t).
  Proof.
    unfold Stable, R.
    intros. intros ?.
    destruct H0 as [[? [? [? ?]]] ?].
    destruct H2 as [[?|?]|?].
    - destruct H2.
      intros ?.
      apply ALinIdleExv in H5 as [? ?].
      apply H4 in H5 as [? [? [? [? ?]]]].
      apply H0; do 2 eexists; eauto.
    - destruct H2 as [? [? [? ?]]].
      specialize (H6 _ _ eq_refl eq_refl) as [? [? ?]].
      intros ?. unfold ALinIdle, ALinEx in *.
      apply H0.
      destruct H9 as [? [? [? ?]]].
      pose proof ac_nonempty (Δ x) as [? [? ?]].
      do 2 eexists; split; eauto.
      apply H2 in H11.
      pose proof ac_domexact _ _ _ _ _ H9 H11.
      apply H12; auto.
    - destruct H2 as [? [? [? [? [? [? [? ?]]]]]]].
      destruct H5 as [? [? [? [? ?]]]].
      intros ?; apply H0.
      unfold ALinIdle, ALinEx in *.
      destruct H9 as [? [? [? ?]]].
      apply H5, H7 in H9. eauto.
  Qed.


  Open Scope nat.

  Definition TaskCompleted t o n i : assertion :=
    IsExpired i //\\ (ALinIdle t \\// ALin t (ls_linr (cas o n) o)).

  Definition TaskPlaced t o n i : assertion :=
    (CurrentTask (CTask t o n i) //\\ NotDone t o n).

  Definition TaskAttempted t o n i v : assertion :=
    (CurrentTask (CTask t o n i) //\\ ALinExv t (Some (ls_linr (cas o n) o)) v).

  Lemma stable_alinr : forall t f r,
    Stable (R t) I (ALin t (ls_linr f r)).
  Proof.
    intros.
    unfold Stable, R.
    intros. intros ?.
    destruct H0 as [[s' [? [[? ?] [[[? ?] | ?] | ?]]]] ?].
    - unfold R_id in H4.
      intros ? ? ?.
      assert (ALinExv t0 (TMap.find t0 π) (fst (state ρ)) s) by (eexists; eauto).
      apply H4 in H7 as [? [? [? [? ?]]]].
      apply H0 in H7. rewrite <- H8. auto.
    - apply H3; auto.
    - destruct H3 as [_ [? [? [? [? [_ [? _]]]]]]].
      destruct H3 as [? [? [? [? ?]]]].
      intros ? ? ?.
      apply H3, H5, H0 in H7. auto.
  Qed.

  Lemma stable_task_completed : forall t o n i,
    Stable (R t) I (TaskCompleted t o n i).
  Proof.
    intros.
    unfold Stable, R.
    intros. intros ?.
    destruct H0 as [[s' [H [[? ?] ?]]] HI].
    split; [apply H0, H|].
    destruct H2 as [[[? ?] | ?] | ?].
    - destruct H as [_ [? | ?]].
      * left.
        apply ALinIdleExv in H4 as [? ?].
        apply H3 in H4 as [? [? [? [? ?]]]].
        do 2 eexists; eauto.
      * right. apply stable_alinr; split; auto; eexists.
        split; eauto. split; [split; eauto|].
        do 2 left; split; auto.
    - destruct H2 as [? [? [? ?]]].
      destruct H as [_ [? | ?]].
      + left. destruct H6 as [? [? [? ?]]].
        apply H2 in H6.
        do 2 eexists; eauto.
      + right. apply H3; auto.
    - destruct H2 as [? [? [? [? [? [? [? _]]]]]]].
      destruct H4 as [? [? [? [? ?]]]].
      destruct H as [_ [? | ?]].
      + destruct H7 as [? [? [? ?]]].
        left. exists x3, x4; split; try (apply H4; constructor).
        eapply ac_domexact; eauto.
        apply H5; constructor.
      + right. intros ? ? ?.
        apply H4, H5, H7 in H8. auto.
  Qed.
  
  Lemma stable_task_placed : forall t o n i,
    Stable (R t) I (TaskCompleted t o n i \\// TaskPlaced t o n i).
  Proof.
    intros.
    unfold Stable.
    intros. intros ?.
    destruct H0 as [[s' [? ?]] HI].
    destruct H0; [left; apply stable_task_completed; split; auto; eexists; eauto|].
    destruct H1 as [[? ?] [[[? ?] | ?] | ?]].
    - right.
      assert (CurrentTask (CTask t0 o n i) s) by apply H3, H0.
      split; auto.
      apply HI in H5. apply H5.
    - destruct H3 as [? [? [? ?]]].
      specialize (H6 _ _ eq_refl eq_refl) as [? [? ?]].
      right. 
      assert (CurrentTask (CTask t0 o n i) s).
      {
        unfold CurrentTask, Conj.
        rewrite <- H6. apply H0.
      }
      split; auto.
      apply HI in H9. apply H9.
    - left.
      destruct H3 as [? [? [? [? [? [? [? ?]]]]]]].
      specialize (H6 _ _ eq_refl eq_refl) as [? [? ?]].
      split.
      + unfold IsExpired.
        rewrite H8.
        destruct H0.
        eapply CurrentTaskCongruence in H0; eauto.
        inversion H0; subst.
        unfold owner_upd. rewrite Nat.eqb_refl. auto.
      + right. intros ? ? ?.
        destruct H5 as [? [? [? [? ?]]]].
        apply H5 in H9. inversion H9; subst.
        destruct H0.
        eapply CurrentTaskCongruence in H0; eauto.
        inversion H0; subst. auto.
  Qed.

  Lemma stable_task_attempted : forall t o n i v,
    Stable (R t) I (TaskCompleted t o n i \\// TaskAttempted t o n i v).
  Proof.
    intros.
    unfold Stable.
    intros. intros ?.
    destruct H0 as [[s' [? ?]] HI].
    destruct H0; [left; apply stable_task_completed; split; auto; eexists; eauto|].
    destruct H1 as [[? ?] [[[? ?] | ?] | ?]].
    - right.
      assert (CurrentTask (CTask t0 o n i) s) by apply H3, H0.
      split; auto.
      destruct H0 as [? ?]. apply H4 in H6; auto.
    - destruct H3 as [? [? [? ?]]].
      specialize (H6 _ _ eq_refl eq_refl) as [? [? ?]].
      right. 
      assert (CurrentTask (CTask t0 o n i) s).
      {
        unfold CurrentTask, Conj.
        rewrite <- H6. apply H0.
      }
      split; auto.
      destruct H0 as [_ [? [? [? [? ?]]]]].
      apply H3 in H0. do 2 eexists; eauto.
    - left.
      destruct H3 as [? [? [? [? [? [? [? ?]]]]]]].
      specialize (H6 _ _ eq_refl eq_refl) as [? [? ?]].
      split.
      + unfold IsExpired.
        rewrite H8.
        destruct H0.
        eapply CurrentTaskCongruence in H0; eauto.
        inversion H0; subst.
        unfold owner_upd. rewrite Nat.eqb_refl. auto.
      + right. intros ? ? ?.
        destruct H5 as [? [? [? [? ?]]]].
        apply H5 in H9. inversion H9; subst.
        destruct H0.
        eapply CurrentTaskCongruence in H0; eauto.
        inversion H0; subst. auto.
  Qed.

  (* Lemma stable_task_attemptedEX : forall t o n i,
    Stable (R t) I (TaskCompleted t o n i \\// ∃ v, TaskAttempted t o n i v).
  Proof.
    eapply EquivStable with
      .
  Qed. *)

  Lemma stable_task_placed_other : forall t t' o' n' i',
    Stable (R t) I (IsExpired i' \\// TaskPlaced t' o' n' i').
  Proof.
    intros.
    unfold Stable.
    intros. intros ?.
    destruct H0 as [[s' [? ?]] HI].
    destruct H0; [left; apply H1; auto|].
    destruct H1 as [[? ?] [[[? ?] | ?] | ?]].
    - right.
      assert (CurrentTask (CTask t' o' n' i') s) by apply H3, H0.
      split; auto.
      apply HI in H5. apply H5.
    - destruct H3 as [? [? [? ?]]].
      specialize (H6 _ _ eq_refl eq_refl) as [? [? ?]].
      right.
      assert (CurrentTask (CTask t' o' n' i') s).
      {
        unfold CurrentTask, Conj.
        rewrite <- H6. apply H0.
      }
      split; auto.
      apply HI in H9. apply H9.
    - left.
      destruct H3 as [? [? [? [? [? [? [? ?]]]]]]].
      specialize (H6 _ _ eq_refl eq_refl) as [? [? ?]].
      unfold IsExpired.
      rewrite H8.
      destruct H0.
      eapply CurrentTaskCongruence in H0; eauto.
      inversion H0; subst.
      unfold owner_upd. rewrite Nat.eqb_refl. auto.
  Qed.

  Lemma stable_task_attempted_other : forall t t' o' n' i' v,
    Stable (R t) I (IsExpired i' \\// TaskAttempted t' o' n' i' v).
  Proof.
    intros.
    unfold Stable.
    intros. intros ?.
    destruct H0 as [[s' [? ?]] HI].
    destruct H0; [left; apply H1; auto|].
    destruct H1 as [[? ?] [[[? ?] | ?] | ?]].
    - destruct H0. right.
      apply H3 in H0 as [? ?]. split; auto.
    - destruct H3 as [? [? [? ?]]].
      specialize (H6 _ _ eq_refl eq_refl) as [? [? ?]].
      right.
      assert (CurrentTask (CTask t' o' n' i') s).
      {
        unfold CurrentTask, Conj.
        rewrite <- H6. apply H0.
      }
      split; auto.
      destruct H0 as [? [? [? [? [? ?]]]]].
      apply H3 in H10. eexists; eauto.
    - left.
      destruct H3 as [? [? [? [? [? [? [? ?]]]]]]].
      specialize (H6 _ _ eq_refl eq_refl) as [? [? ?]].
      unfold IsExpired.
      rewrite H8.
      destruct H0.
      eapply CurrentTaskCongruence in H0; eauto.
      inversion H0; subst.
      unfold owner_upd. rewrite Nat.eqb_refl. auto.
  Qed.
  
  Ltac simpl_all :=
      unfold I, I_ρ_atomic, I_flag, I_val, I_cur_task, I_not_cur_task, ticket_not_owned, NotDone, NotPlacedBy, CurrentVal, CurrentTask, TaskAttempted, TaskCompleted, OwnedBy, ALinIdle, ALin, ALinEx, Neg, IsExpired, IsInactive, Conj, Disj, Forall, Imply, APure, owner_upd in *; simpl in *.

  Lemma G_id_I : ⊨ G_id ⊚ I ==>> I.
  Proof.
    intros s [s' [? ?]].
    destruct H1 as [? [? ?]].
    unfold I, I_ρ_atomic, I_flag, I_val, I_cur_task, I_not_cur_task, ticket_not_owned, Conj, Forall, NotDone, CurrentVal, CurrentTask, OwnedBy,
    ALinIdle, ALinEx, Neg, IsInactive in *.
    rewrite H1, H2 in *.
    split; [intros ? ? HΔ; apply H3 in HΔ; extract 0%nat H0; eauto|].
    split; [intros ? ? HΔ; apply H3 in HΔ; extract 1%nat H0; eauto|].
    split.
    {
      intros. apply H0 in H4 as [? [? [? ?]]]; subst.
      exists x, x0. split; auto.
      etransitivity; eauto. symmetry; auto.
    }
    (* split; [intros ? ? ? ? HΔ; apply H3 in HΔ; extract 2%nat H0; eauto|]. *)
    split.
    {
      intros. intros ?.
      extract 3 H0.
      rewrite <- H1 in *.
      apply H0 in H4 as [? [? ?]].
      split; eauto.
      split.
      - intros ?. apply H5.
        destruct H7 as [? [? [? ?]]].
        apply H3 in H7; eauto.
      - destruct H6 as [? [? [? [? ?]]]].
        apply H3 in H6. eauto.
    }
    split.
    {
      intros. intros ?.
      extract 4 H0.
      rewrite <- H1 in *.
      apply H0 in H4 as [? ?].
      exists x. intros.
      apply H3 in H5; eauto.
    }
    extract 5 H0. eauto.
  Qed.


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
  Hint Resolve stable_ccas_l0 Istable stable_notplaced stable_alinr
    stable_task_completed stable_task_placed stable_task_placed_other
    stable_alinidle stable_task_attempted stable_task_attempted_other
    stable_alin_flag
  : stableDB.

  (* Ltac extract n H :=
    (* let Hneed := fresh "H" in *)
    lazymatch n with
      | O => idtac
      | S ?n' =>
          destruct H as [_ H];
          extract n' H
    end;
    try destruct H as [H _]. *)

  Lemma conj_from_imp : forall (P Q : Prop), P -> (P -> Q) -> P /\ Q.
  Proof. eauto. Qed.
  
  Lemma conj_right_imp {P Q R : Prop} :
    (Q -> R) -> (P /\ Q) -> (P /\ R).
  Proof. tauto. Qed.

  Ltac post_pupdate_id :=
    eapply conj_right_imp; [apply G_id_G |];
            apply and_comm, conj_from_imp; intros.

  Lemma triple_complete : forall t t0 o0 n0 i0 F,
    ⊨ (G_id ∪ G_trylin ∪ G_resolve) ⊚ (F //\\ I) ==>> F ->
    Stable (R t) I F ->
    @HTripleProvable (li_sig E) (li_sig CCASImpl.F) (li_lts E) (li_lts CCASImpl.F) 
    (R t) (G t) I t unit
    (F //\\ I //\\
    ((⌜t = t0⌝ //\\ TaskCompleted t0 o0 n0 i0 \\// ⌜t <> t0⌝ //\\ IsExpired i0) \\//
     TaskPlaced t0 o0 n0 i0))
    (complete t0 o0 n0 i0)
    (fun _ : unit =>
      F //\\ I //\\ (⌜t = t0⌝ //\\ TaskCompleted t0 o0 n0 i0 \\// ⌜t <> t0⌝)).
  Proof.
    intros cid t0 o0 n0 i0 F HFG HFR.
    unfold complete.
    (* eapply provable_conseq_weak_pre with
      (P' := F //\\
          (
            (⌜cid = t0⌝ //\\ (TaskCompleted t0 o0 n0 i0 \\// TaskPlaced t0 o0 n0 i0))
            \\//
            (⌜cid <> t0⌝ //\\ (IsExpired i0 \\// TaskPlaced t0 o0 n0 i0))
          )).
    {
      intros ? [? [[[? ?]| [? ?]] | ?]]; split; auto.
      - left. split; auto. left; auto.
      - right. split; auto. left; auto.
      - destruct (Pos.eq_dec cid t0).
        + left; split; auto. right; auto.
        + right; split; auto. right; auto.
    } *)
    (* get *)
    eapply provable_vis_safe with
      (P' := F //\\ I //\\
              ((⌜cid = t0⌝ //\\ TaskCompleted t0 o0 n0 i0 \\// ⌜cid <> t0⌝ //\\ IsExpired i0) \\//
              TaskPlaced t0 o0 n0 i0))
      (Q' := fun b:bool => F //\\ I //\\
              ((⌜cid = t0⌝ //\\ TaskCompleted t0 o0 n0 i0 \\// ⌜cid <> t0⌝ //\\ IsExpired i0) \\//
              TaskAttempted t0 o0 n0 i0 ((if b then n0 else o0)) ));
      (* (P' := F //\\
          (
            (⌜cid = t0⌝ //\\ (TaskCompleted t0 o0 n0 i0 \\// TaskPlaced t0 o0 n0 i0))
            \\//
            (⌜cid <> t0⌝ //\\ (IsExpired i0 \\// TaskPlaced t0 o0 n0 i0))
          )) *)
      (* (Q' := fun b =>
          F //\\
          (
            (⌜cid = t0⌝ //\\ (TaskCompleted t0 o0 n0 i0 \\// TaskAttempted t0 o0 n0 i0))
            \\//
            (⌜cid <> t0⌝ //\\ (IsExpired i0 \\// TaskAttempted t0 o0 n0 i0))
          )); *)
    try solve_conj_impl;
    try solve_stable stableDB;
    try (intros; apply ConjLeftImpl; auto);
    try solve_no_error.
    (* stable *)
    {
      apply ConjStable; auto.
      eapply EquivStable with
        (P := I //\\ ((⌜cid = t0⌝ //\\ (TaskCompleted t0 o0 n0 i0 \\// TaskPlaced t0 o0 n0 i0))
            \\//
            (⌜cid <> t0⌝ //\\ (IsExpired i0 \\// TaskPlaced t0 o0 n0 i0))));
      try solve_stable stableDB.
      clear.
      split; intros; intros [? ?]; split; auto; simpl_all.
      - destruct H1 as [[?[?|?]]|[?[?|?]]]; eauto.
      - destruct H1 as [[[? ?]|[? ?]]|?]; eauto.
        destruct (Pos.eq_dec cid t0); eauto.
    }
    {
      intros b.
      apply ConjStable; auto.
      eapply EquivStable with
        (P := I //\\
            ((⌜cid = t0⌝ //\\ (TaskCompleted t0 o0 n0 i0 \\// TaskAttempted t0 o0 n0 i0 ((if b then n0 else o0)) ))
            \\//
            (⌜cid <> t0⌝ //\\ (IsExpired i0 \\// TaskAttempted t0 o0 n0 i0 ((if b then n0 else o0)) ))));
      try solve_stable stableDB.
      clear.
      split; intros; intros [? ?]; split; auto; simpl_all.
      - destruct H1 as [[?[?|?]]|[?[?|?]]]; eauto.
      - destruct H1 as [[[? ?]|[? ?]]|?]; eauto.
        destruct (Pos.eq_dec cid t0); eauto.
    }
    (* inv *)
    {
      pupdate_intros_atomic.
      dependent destruction Hstep.

      pupdate_start.
      apply ac_steps_refl.

      post_pupdate_id.
      { unfold G_id; simpl; do 2 (split; auto); reflexivity. }
      destruct Hpre. destruct H2.
      split; [eapply HFG; eexists; split; try split; eauto; do 2 left; auto|].
      split; auto.
    }
    (* res *)
    {
      pupdate_intros_atomic.
      dependent destruction Hstep.
      destruct Hpre as [? [HI [?|?]]].
      (* fail *)
      {
        pupdate_start.
        apply ac_steps_refl.

        post_pupdate_id.
        { unfold G_id; simpl; do 2 (split; auto); reflexivity. }
        split; [eapply HFG; eexists; split; try split; eauto; do 2 left; auto|].
        split; auto.
        left. apply H1.
      }
      (* succeed *)
      {
        destruct H1 as [? [ρ [π [? [? ?]]]]]. simpl in *.
        (* apply HFI in H0 as HI. *)
        pose proof HI. extract 1 H5.
        pose proof HI. extract 0 H6.
        apply H5 in H2 as ?.
        apply H6 in H2 as ?.
        destruct H8; subst.
        destruct x. simpl in *; subst ret.
        
        pupdate_start.
        pupdate_trylin_from H2.
        pupdate_forward t0 (InvEv (cas v n0)).
        pupdate_forward t0 (ResEv (cas v n0) v).
        pupdate_finish.

        (* add other poss *)
        apply ACTrylinContinue.
        apply ac_steps_refl.

        eapply conj_right_imp; [apply G_trylin_G |];
        apply and_comm, conj_from_imp; intros.
        {
          unfold G_trylin.
          repeat try split; simpl_all; subst; eauto.
          + constructor; auto.
          + intros.
            apply H4 in H2 as ?.
            destruct (Pos.eq_dec t0 t1); subst; try congruence.
            inversion H7; subst; eauto.
            inversion H9; subst; eauto.
            do 2 (rewrite TMap.gso; auto).
          + do 4 eexists; split; eauto.
            intros. inversion H8; subst; eauto.
            inversion H9; subst.
            do 2 (rewrite TMap.gso; eauto).
        }
        {
          split; [apply HFG; eexists; split; try split; eauto; left; right; auto|].
          clear H4.
          split.
          - repeat try split;
            try rewrite H1 in *; eauto; try apply HI.
            + inversion 1; subst; [eapply HI; eauto|].
              inversion H7; subst; eauto.
            + inversion 1; subst; [eapply HI; eauto|].
              inversion H7; subst; eauto.
            + simpl_all; rewrite H1 in *; inversion 1.
            + simpl_all; rewrite H1 in *; inversion H4; subst.
              extract 3 HI. apply (HI _ _ _ _ eq_refl).
            + simpl_all; rewrite H1 in *; inversion H4; subst.
              intros [? [? [? ?]]].
              inversion H7; subst.
              * eapply ac_domexact in H9; [| apply H2].
                apply H9 in H8. congruence.
              * inversion H9; subst.
                rewrite TMap.gss in H8. congruence.
            + simpl_all; rewrite H1 in *.
              do 2 eexists; split; [apply ACUnionLeft|]; eauto.
              inversion H4; subst; eauto.
            + simpl_all; rewrite H1 in *.
              intros. destruct (Pos.eq_dec t0 v0); subst; try congruence.
              apply HI in H4 as [? ?].
              exists x. inversion 1; subst; eauto.
              inversion H8; subst. do 2 (rewrite TMap.gso; eauto).
          - do 2 simpl_all. right.
            split; eauto.
            exists (Idle (pair (if b then n0 else v) b)), (TMap.add t0 (ls_linr (cas v n0) v) (TMap.add t0 (ls_lini (cas v n0)) π)).
            split; [|rewrite TMap.gss;auto].
            apply ACUnionRight. constructor; auto.
            pupdate_forward t0 (InvEv (cas v n0)).
            pupdate_forward t0 (ResEv (cas v n0) v).
            pupdate_finish.
        }
      }
    }
    
    intros b.
    (* try resolve *)
    eapply provable_vis_safe with
      (P' := F //\\ I //\\
            ((⌜cid = t0⌝ //\\ TaskCompleted t0 o0 n0 i0 \\// ⌜cid <> t0⌝ //\\ IsExpired i0) \\//
            TaskAttempted t0 o0 n0 i0 ((if b then n0 else o0)) ))
      (Q' := fun _ =>
            F //\\ I //\\ (⌜cid = t0⌝ //\\ TaskCompleted t0 o0 n0 i0 \\// ⌜cid <> t0⌝));
    try solve_conj_impl;
    try solve_stable stableDB;
    try solve [intros; apply ConjLeftImpl; auto].
    (* error *)
    {
      intros ? ? ?.
      destruct s, σ0. simpl in *.
      inversion H1; subst.
      dependent destruction Herror.
      destruct H0 as [? [? [[?|?]|?]]]; simpl_all.
      - destruct H4 as [? [? ?]]. congruence.
      - destruct H4. congruence.
      - destruct H4. apply H2 in H4 as [? _]. congruence.
    }
    (* stable *)
    {
      apply ConjStable; auto.
      eapply EquivStable with
        (P := I //\\ 
            ((⌜cid = t0⌝ //\\ (TaskCompleted t0 o0 n0 i0 \\// TaskAttempted t0 o0 n0 i0 ((if b then n0 else o0)) ))
            \\//
            (⌜cid <> t0⌝ //\\ (IsExpired i0 \\// TaskAttempted t0 o0 n0 i0 ((if b then n0 else o0)) ))));
      try solve_stable stableDB.
      clear.
      split; intros; intros [? ?]; split; auto; simpl_all.
      - destruct H1 as [[?[?|?]]|[?[?|?]]]; eauto.
      - destruct H1 as [[[? ?]|[? ?]]|?]; eauto.
        destruct (Pos.eq_dec cid t0); eauto.
    }
    (* inv *)
    {
      pupdate_intros_atomic.
      dependent destruction Hstep.

      pupdate_start.
      apply ac_steps_refl.

      post_pupdate_id.
      { unfold G_id; simpl; do 2 (split; auto); reflexivity. }
      destruct Hpre. destruct H2.
      split; [eapply HFG; eexists; split; try split; eauto; do 2 left; auto|].
      split; auto.
    }
    (* res *)
    {
      intros.
      pupdate_intros_atomic;
      dependent destruction Hstep.
      (* succeed *)
      {
        destruct Hpre as [? [HI [? | ?]]].
        {
          exfalso.
          clear H0.
          pose proof HI as H0.
          extract 3 H0.
          simpl_all.
          specialize (H0 _ _ _ _ eq_refl) as [? ?].
          rewrite H0 in H1.
          destruct H1 as [[_ [? _]]|[_ ?]]; congruence.
        }
        destruct H1 as [? [ρ [π [Hposs ?]]]]; simpl in *.

        pupdate_start.
        pupdate_trylin_from Hposs.
        pupdate_finish.
        apply ACTrylinFinish.

        eapply conj_right_imp; [apply G_resolve_G |];
        apply and_comm, conj_from_imp; intros.
        {
          unfold G_resolve.
          repeat try split; simpl_all; subst; eauto.
          do 4 eexists; split; eauto.
          split; intros; subst; simpl.
          + pose proof HI as [? _].
            apply H3 in Hposs as ?. destruct H4; subst.
            destruct x. simpl in *. destruct H2; subst. 
            exists (Idle (pair (if b then n else o) b0)), π.
            split; [|split;auto;try (inversion 1; subst; auto) ].
            intros ? ?.
            split; inversion 1; subst; try constructor; auto.
            apply rt_refl.
          + do 2 (split; auto).
            clear H0. pose proof HI as H0. simpl_all.
            extract 3 H0.
            specialize (H0 _ _ _ _ eq_refl). tauto.
        }
        {
          split; [apply HFG; eexists; split; try split; eauto; right; auto|].
          clear H3.
          pose proof HI as [? _].
          apply H3 in Hposs as ?. destruct H4; subst. clear H3.
          destruct x; simpl in *. destruct H2; subst.
          split.
          - repeat try split;
            try (solve [
              inversion 1; subst; eapply HI; eauto |
              inversion H3
            ]).
            + inversion 1; subst. simpl_all.
              exists (Idle (pair (if b then n else o) b0)), π.
              split; auto.
              apply ac_trylin_single.
            + simpl_all. intros.
              destruct (Pos.eq_dec t1 v); subst.
              * exists (Some (ls_linr (cas o n) o)).
                inversion 1; subst. auto.
              * extract 4 HI.
                assert (forall (v0 v1 : Val) (v2 : nat), @inl (CASTask Val) Val (CTask t1 o n i) <> inl (CTask v v0 v1 v2)) by congruence.
                apply HI in H4 as [? ?].
                exists x. inversion 1; subst. eauto.
            + simpl_all.
              assert (owner0 i = Owned t1) by (eapply HI; eauto).
              extract 5 HI. intros.
              destruct (Nat.eqb_spec i i0); auto.
              subst. apply HI in H4. congruence.
          - do 2 simpl_all.
            destruct (Pos.eq_dec cid0 t1); auto; subst.
            left; split; auto.
            rewrite Nat.eqb_refl.
            split; auto. right.
            intros. inversion H3; subst; auto.
        }
      }
      (* fail *)
      {
        destruct Hpre as [? [? [? | ?]]].
        2:{
          exfalso.
          do 2 simpl_all.
          destruct H4; congruence.
        }
        (* destruct H1 as [? [ρ [π [Hposs ?]]]]; simpl in *. *)

        pupdate_start.
        apply ac_steps_refl.

        post_pupdate_id.
        { unfold G_id; simpl; do 2 (split; auto); reflexivity. }
        split; [eapply HFG; eexists; split; try split; eauto; do 2 left; auto|].
        clear - H3 H4.
        split; auto.
        simpl_all.
        destruct H4; [left|right]; try tauto.
      }
    }

    intros.
    eapply provable_ret;
    try solve_conj_impl;
    try solve_stable stableDB.
    left. auto.
  Qed.

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
      intros. intros s1 s2 [[? | ?] HI];
      [eapply RG_compatible; eauto; try (split; auto)|].
      destruct H1 as [[? | ?] | ?].
      - unfold GINV, Ginv, LiftRelation_Δ in *.
        destruct H1 as [? [? [? ?]]].
        split.
        + unfold R_IsExpired, R_notplaced, R_flag, IsExpired, NotPlacedBy, CurrentTask, OwnedBy, Neg, Forall, Conj.
          split;[split|]; intros; simpl;
          try rewrite H1 in *; auto.
          intros ? ? ?. apply H3 in H5; inversion H5; subst.
          rewrite TMap.gso; eauto.
        + do 2 left.
          unfold R_id, R_task, CurrentTask.
          split; split; try rewrite H1; eauto.
          * intros; split; auto. intros ? ? [? [? [? [? ?]]]].
            exists x0, (TMap.add t1 (ls_inv x) x1).
            split;[apply H3;constructor;auto|].
            apply H2 in H5. destruct (Pos.eq_dec t1 t0); subst; try congruence.
            rewrite TMap.gso; auto.
          * intros [? [π [? [? ?]]]].
            pose proof ACInv (Δ s1) t1 x _ _ H4.
            apply H3 in H7.
            exists x0, (TMap.add t1 (ls_inv x) π); split; auto.
            rewrite TMap.gso; auto.
          * intros [? [π [? [? ?]]]].
            apply H3 in H4.
            inversion H4; subst.
            exists x0, π0; split; auto.
            rewrite TMap.gso; auto.
      - unfold GRET, Gret, LiftRelation_Δ in *.
        destruct H1 as [? [? [? [? ?]]]].
        split; [unfold R_IsExpired, R_notplaced, R_flag, IsExpired, NotPlacedBy, CurrentTask, OwnedBy, Neg, Forall, Conj;
          split;[split|]; intros; simpl;
          try rewrite H1 in *; auto|].
        intros ? ? ?. apply H3 in H5; inversion H5; subst.
        rewrite TMap.gro; eauto.
        do 2 left.
        split; split; unfold R_task; try (unfold CurrentTask; rewrite H1; tauto).
        + intros. split; [unfold CurrentTask; rewrite <- H1; auto|].
          apply HI in H4 as [_ [_ [? [? [? [? _]]]]]].
          apply H2 in H4.
          assert (t1 <> t0) by congruence.
          intros ? ? [? [? [? [? ?]]]].
          exists x3, (TMap.remove t1 x4).
          split; [apply H3; constructor; auto|].
          rewrite TMap.gro; auto.
        + unfold R_id. intros [π [? [? [? ?]]]].
          pose proof ACRes (Δ s1) t1 _ _ H4.
          apply H3 in H7.
          do 2 eexists. do 2 (split; eauto).
          rewrite TMap.gro; auto.
        + unfold R_id. intros [? [π [? [? ?]]]].
          apply H3 in H4.
          inversion H4; subst.
          exists x1, π0; split; auto.
          rewrite TMap.gro; auto.
      - unfold GId in H1; subst.
        split; [unfold R_IsExpired, R_notplaced, R_flag, IsExpired, NotPlacedBy, CurrentTask, OwnedBy, Neg, Forall, Conj; split; auto|].
        + split; auto.
        + do 2 left. unfold R_task, R_id; split; intros; tauto.
    }
    (* method provable *)
    {
      intros t.
      destruct f.
      (* set flag *)
      {
        (* pre-condition *)
        exists (I //\\ ALin t (ls_inv (setFlag b))).
        (* post-condition *)
        exists (fun r => I //\\ ALin t (ls_linr (setFlag b) r)).
        constructor;
        try solve_conj_impl;
        try solve_stable stableDB.
        (* invocation *)
        {
          intros ? ?.
          split; [apply Ginv_I in H0; auto|].
          destruct H0 as [s' [HI [Hσ [? HΔ]]]].
          intros ? ? ?.
          apply HΔ in H1. inversion H1; subst.
          rewrite TMap.gss. auto.
        }
        (* response *)
        {
          intros. intros [? [[? ?] ?]].
          eapply Gret_I; eexists; do 2 (split; eauto).
        }
        {
          intros. apply H0 in H1. auto.
        }
        unfold setFlag_impl.
        eapply provable_vis_safe with
          (P' :=I //\\ ALin t (ls_inv (setFlag b)))
          (Q' := fun _ => I //\\ ALin t (ls_linr (setFlag b) tt));
          try solve_no_error;
          try solve_conj_impl;
          try solve_stable stableDB.
        (* inv *)
        {
          pupdate_intros_atomic.
          dependent destruction Hstep.

          pupdate_start.
          apply ac_steps_refl.

          post_pupdate_id.
          { unfold G_id; simpl; do 2 (split; auto); reflexivity. }
          destruct Hpre as [? ?].
          split; [apply G_id_I; eexists; eauto|].
          unfold ALin, CurrentTask, Neg, Conj, Forall in *.
          eauto.
        }
        (* res *)
        {
          pupdate_intros_atomic.
          dependent destruction Hstep.
          destruct Hpre as [HI ?].
          pose proof HI. extract 0 H1.
          
          Definition ρstep b' (ρ : State (li_lts F)) : State (li_lts F) :=
            match ρ with
            | Idle (pair v b) => Idle (pair v b')
            | _ => ρ
            end.

          assert (Hpstep : forall ρ π, Δ1 ρ π -> poss_steps (PossOk ρ π) (PossOk (ρstep s4 ρ) (TMap.add t (ls_linr (setFlag s4) tt) (TMap.add t (ls_lini (setFlag s4)) π)))).
          {
            intros.
            apply H1 in H2 as ?. destruct H3; subst. destruct x.
            apply H0 in H2 as ?.
            pupdate_forward t (@InvEv (li_sig F) (setFlag s4)).
            pupdate_forward t (@ResEv (li_sig F) (setFlag s4) tt).
            pupdate_finish.
          }

          exists (ac_steps_π Δ1 t (ls_lini (setFlag s4)) (ls_linr (setFlag s4) tt) _ Hpstep).
          split;[|split].
          - inversion 1; subst.
            econstructor; eauto.
          - repeat split; simpl_all;
            try solve [ inversion 1; subst; eauto ].
            + inversion 1; subst.
              apply H1 in Hposs as [? ?]; subst.
              destruct x. simpl. eauto.
            + inversion 1; subst.
              apply H1 in Hposs as [? ?]; subst.
              destruct x. simpl. eauto.
            + intros. apply HI in H2 as [? [? [? ?]]].
              pose proof ac_nonempty Δ1 as [? [? ?]].
              pose proof H4.
              apply H1 in H5 as [? ?]; subst.
              apply H2 in H4; inversion H4; subst.
              destruct x3. simpl in *.
              exists (ρstep s4 (Idle (pair v b))). exists (TMap.add t (ls_linr (setFlag s4) tt) (TMap.add t (ls_lini (setFlag s4)) x2)).
              split; eauto. split; inversion 1; subst; eauto.
              * apply H2 in Hposs. inversion Hposs; subst. simpl.
                constructor.
              * constructor. apply H2; constructor.
            + apply HI in H2; tauto.
            + apply HI in H2.
              intros [? [? [? ?]]]. apply H2.
              inversion H3; subst.
              do 2 eexists; split; eauto.
              assert (v <> t).
              {
                intros ?; subst. rewrite TMap.gss in H4. congruence.
              }
              do 2 (rewrite TMap.gso in H4; eauto).
            + apply HI in H2 as [_ [_ [? [? [? [? ?]]]]]].
              exists ((ρstep s4) x), (TMap.add t (ls_linr (setFlag s4) tt) (TMap.add t (ls_lini (setFlag s4)) x0)).
              split; [constructor; eauto|].
              split.
              * assert (v <> t). { intros ?. apply H0 in H2. congruence. }
                do 2 (rewrite TMap.gso; eauto).
              * destruct x; simpl; auto. destruct s; auto.
            + intros. apply HI in H2.
              destruct (Pos.eq_dec v t); subst.
              * exists (Some (ls_linr (setFlag s4) tt)).
                inversion 1; subst. rewrite TMap.gss; auto.
              * destruct H2. exists x.
                inversion 1; subst. apply H2 in Hposs.
                do 2 (rewrite TMap.gso; eauto).
            + apply HI.
            + inversion 1; subst. rewrite TMap.gss; auto.
          - right. unfold G_fail.
            intros ? ?. unfold R_IsExpired, R_notplaced, R_task, R_id, R_flag.
            repeat split; simpl_all; eauto; try tauto.
            + intros. unfold ALinExv.
              destruct H4 as [? [? [? [? ?]]]]. simpl in *.
              pose proof HI as [? _]. apply H7 in H4 as ?. destruct H8; subst. clear H7.
              destruct x1.
              exists (ρstep s4 (Idle (pair v b))), (TMap.add t (ls_linr (setFlag s4) tt) (TMap.add t (ls_lini (setFlag s4)) x0)).
              repeat split; eauto.
              destruct (Pos.eq_dec t0 t); [|do 2 (rewrite TMap.gso; eauto) ].
              subst.
              apply HI in H3 as [_ [_ [? [? [? [? ?]]]]]].
              apply H0 in H3. congruence.
            + intros [? [? [? [? ?]]]]. simpl in *.
              pose proof HI as [? _]. apply H6 in H3 as ?. destruct H7; subst. clear H6.
              destruct x1.
              exists (ρstep s4 (Idle (pair v b))), (TMap.add t (ls_linr (setFlag s4) tt) (TMap.add t (ls_lini (setFlag s4)) x0)).
              repeat split; eauto.
              do 2 (rewrite TMap.gso; eauto).
            + intros [? [? [? [? ?]]]]. simpl in *.
              dependent destruction H3.
              pose proof HI as [? _]. apply H3 in Hposs as ?. destruct H6; subst ρ0. clear H3.
              do 2 (rewrite TMap.gso in H4; eauto).
              destruct x. subst.
              exists ((Idle (pair v b))), π.
              repeat split; eauto.
            + intros. dependent destruction H4.
              do 2 (rewrite TMap.gso; eauto).
        }
        intros _.
        eapply provable_ret;
        try solve_conj_impl;
        try solve_stable stableDB.
        left; auto.
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
        try solve_stable stableDB.
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
                (ALin t (ls_inv (cas o n)) //\\ (∀ (o0 n0 : Val) (i : nat), !! CurrentTask (CTask t o0 n0 i))) //\\
                NotPlacedBy i t);
          try (solve_no_error; congruence);
          try solve_conj_impl;
          try solve_stable stableDB.
        (* inv *)
        {
          pupdate_intros_atomic.
          dependent destruction Hstep.

          pupdate_start.
          apply ac_steps_refl.

          post_pupdate_id.
          { unfold G_id; simpl; do 2 (split; auto); reflexivity. }
          destruct Hpre as [? [? ?]].
          split; [apply G_id_I; eexists; eauto|].
          unfold ALin, CurrentTask, Neg, Conj, Forall in *.
          split; eauto.
        }
        (* res *)
        {
          pupdate_intros_atomic.
          dependent destruction Hstep.
          pupdate_start.
          apply ac_steps_refl.

          destruct Hpre as [[? [? [? [? [? ?]]]]] [? ?]].
          split.
          - split; [|simpl_all; rewrite Nat.eqb_refl; do 2 split; eauto].
            do 3 (split; auto).
            split;[|split; auto].
            + unfold I_cur_task in *.
              intros t0 ? ? i ?.
              apply H3 in H8 as [? [? ?]].
              clear - H8 H9 H10 H5.
              simpl_all.
              destruct (Nat.eqb_spec ret i); auto; subst.
              assert (i <= i) by lia. apply H5 in H0. congruence.
            + clear - H5.
              simpl_all. intros.
              destruct (Nat.eqb_spec ret i); auto; subst; try lia.
              assert (ret <= i) by lia. auto.
          - do 4 left; right.
            unfold G_alloc; simpl.
            split; [reflexivity|].
            intros; subst; simpl.
            do 3 (split; auto).
            apply H5. simpl. lia.
        }

        intros i.
        eapply provable_seq with
          (Q' := fun r =>
                      I //\\ (!! ALinIdle t) //\\
                      ((⌜r <> o⌝ //\\ ALin t (ls_linr (cas o n) r)) \\//
                      (⌜r = o⌝ //\\ (TaskCompleted t o n i \\// TaskPlaced t o n i)))).
        (* loop *)
        {
          eapply provable_doloop;
          try solve_conj_impl;
          try solve_stable stableDB.
          remember ((ALin t (ls_inv (cas o n)) //\\
                (∀ (o0 n0 : Val) (i0 : nat), !! CurrentTask (CTask t o0 n0 i0))) //\\ NotPlacedBy i t) as ILoop.
          (* try place task *)
          eapply provable_vis_safe with
            (P' := I //\\ ILoop)
            (Q' := fun r => I //\\
                    match r with
                    | inl (CTask t0 n0 o0 i0) => ILoop //\\ ⌜t <> t0⌝ //\\
                        (IsExpired i0 \\// TaskPlaced t0 n0 o0 i0)
                    | inr v =>
                        (!! ALinIdle t) //\\
                        ((⌜v <> o⌝ //\\ ALin t (ls_linr (cas o n) v) \\//
                        ⌜v = o⌝ //\\ (TaskCompleted t o n i \\// TaskPlaced t o n i)))
                    end);
          try (solve_no_error; congruence);
          try solve_conj_impl;
          try (subst; solve_stable stableDB).
          (* post stable *)
          {
            destruct a; [destruct c|]; subst; solve_stable stableDB.
          }
          (* inv *)
          {
            pupdate_intros_atomic.
            dependent destruction Hstep.

            pupdate_start.
            apply ac_steps_refl.

            post_pupdate_id.
            { unfold G_id; simpl; do 2 (split; auto); reflexivity. }
            destruct Hpre as [? [? ?]].
            split; [apply G_id_I; eexists; eauto|].
            unfold ALin, CurrentTask, Neg, Conj, Forall in *.
            split; eauto.
          }
          (* res *)
          {
            intros.
            pupdate_intros_atomic;
            dependent destruction Hstep.
            (* success *)
            {
              pupdate_start.
              apply ac_steps_refl.

              repeat try split;
              try apply Hpre; try (simpl_all; congruence).
              - inversion H0; subst. eapply Hpre.
              - inversion H0; subst.
                destruct Hpre as [_ [[? _] _]].
                simpl_all. intros [? [? [? ?]]].
                apply H1 in H2. congruence.
              - inversion H0; subst.
                destruct Hpre as [? [[? _] _]].
                extract 2 H1. simpl_all.
                specialize (H1 _ eq_refl) as [? [? [? ?]]].
                assert (Δ1 x x0) by (apply H1; constructor).
                exists x, x0. do 2 (split; auto).
                apply H2 in H4; auto.
              - simpl_all. intros. apply Hpre.
                congruence.
              - intros ?. destruct Hpre as [_ [[? _] _]].
                eapply ALinExCongruence in H0; eauto. congruence.
              - right. split; auto.
                right. split; unfold CurrentTask; auto.
                destruct Hpre as [? [[? _] _]].
                extract 2 H0. simpl_all.
                specialize (H0 _ eq_refl) as [? [? [? ?]]].
                assert (Δ1 x x0) by (apply H0; constructor).
                do 2 eexists; do 2 (split; eauto).
              - do 3 left; right.
                unfold G_place_task. simpl.
                split; [|split; try reflexivity; intros; subst; auto].
                simpl_all. eauto.
            }
            (* other task *)
            {
              pupdate_start.
              apply ac_steps_refl.

              (* failed to place so it satisfies G_id *)
              post_pupdate_id.
              { unfold G_id; simpl; do 2 (split; auto); reflexivity. }
              destruct Hpre as [HI [? ?]].
              split; [apply G_id_I; eexists; eauto|].
              destruct tsk.
              repeat split; try apply H1; try apply H2.
              - simpl_all. destruct H1.
                intros ?. apply (H3 o n i); subst; auto.
              - right. unfold TaskPlaced.
                split; [simpl_all; auto|].
                extract 3 HI. simpl_all.
                specialize (HI _ _ _ _ eq_refl) as [_ [_ ?]].
                eauto.
            }
            (* failed *)
            {
              destruct Hpre as [HI [? ?]].
              destruct HI as (? & Hflag & ? & HI).
              pose proof (H5 _ eq_refl) as [ρ [π [? ?]]]. simpl in *.
              assert (Hposs : Δ1 ρ π) by (apply H6; constructor).

              pose proof Hposs as Hπ. apply H2 in Hπ.
              pose proof Hposs as Hρ. apply H4 in Hρ as [? ?]; subst.
              destruct x as [v b]. simpl in *.

              pupdate_start.

              pupdate_trylin_from Hposs.
              pupdate_forward cid (InvEv (cas o0 n0)).
              pupdate_forward cid (ResEv (cas o0 n0) v).
              pupdate_finish.

              eapply ACTrylinFinish.

              repeat try split;
              try apply HI; try (simpl_all; congruence).
              - inversion 1; subst. eauto.
              - simpl_all.
                inversion 1; subst. simpl in *.
                apply Hflag in Hposs0. auto.
              - simpl_all. inversion 1; subst.
                exists (Idle (pair v0 b)), (TMap.add cid (ls_linr (cas o0 n0) v0) (TMap.add cid (ls_lini (cas o0 n0)) π)).
                split; simpl; eauto.
                split; inversion 1; subst; try constructor; auto.
                pupdate_forward cid (InvEv (cas o0 n0)).
                pupdate_forward cid (ResEv (cas o0 n0) v0).
                pupdate_finish.
              - simpl_all. intros.
                apply HI in H7 as [ls ?].
                destruct (Pos.eq_dec v0 cid); subst.
                + exists (Some (ls_linr (cas o0 n0) v)).
                  inversion 1; subst. rewrite TMap.gss; auto.
                + exists ls. inversion 1; subst.
                  do 2 (rewrite TMap.gso; eauto).
              - intros [? [? [? ?]]].
                inversion H7; subst.
                rewrite TMap.gss in H8. congruence.
              - left. split; auto. simpl_all.
                inversion 1; subst. rewrite TMap.gss; auto.
              - right. unfold G_fail. intros.
                unfold R_IsExpired, R_notplaced, R_flag, R_task, R_id. simpl_all.
                repeat split; simpl_all; eauto; try tauto; try congruence.
                + intros [? [? [? [? ?]]]].
                  apply H6 in H8; inversion H8; subst.
                  exists 
                    (Idle (pair v b)),
                    (* (Idle (pair v b)), *)
                    (TMap.add cid (ls_linr (cas o0 n0) v)
                      (TMap.add cid (ls_lini (cas o0 n0)) x0)).
                  split; [|do 2 (rewrite TMap.gso; auto) ].
                  constructor; eauto.
                  pupdate_forward cid (InvEv (cas o0 n0)).
                  pupdate_forward cid (ResEv (cas o0 n0) v).
                  pupdate_finish.
                + intros [? [? [? [? ?]]]].
                  simpl in *.
                  inversion H8; subst.
                  unfold ALinExv.
                  simpl in *.
                  do 2 eexists; split; eauto.
                  do 2 (rewrite TMap.gso; auto).
                + intros.
                  inversion H9; subst.
                  do 2 (rewrite TMap.gso; eauto).
            }
          }
          intros r.
          destruct r.
          (* exit loop *)
          2:{
            eapply provable_ret;
            try solve_conj_impl;
            try solve_stable stableDB.
            left. auto.
          }
          destruct c.
          (* complete *)
          eapply provable_seq with (Q' := fun _ => I //\\ ILoop).
          2:{
            intros; subst.
            eapply provable_ret;
            try solve_conj_impl;
            try solve_stable stableDB.
            left; auto.
          }
          eapply provable_conseq_weak_pre with
            (P' := ILoop //\\ I //\\
                  ((    (⌜t = t0⌝ //\\ TaskCompleted t0 o0 n0 i0)
                    \\//(⌜t <> t0⌝ //\\ IsExpired i0))
                  \\// TaskPlaced t0 o0 n0 i0)).
          {
            destruct 1 as [? [? ?]].
            do 2 (split; auto).
            destruct H2 as [? [? | ?]].
            - left; right. split; auto.
            - right; auto.
          }
          (* triple for complete *)
          eapply provable_conseq_weak_post;
          [| | |apply triple_complete];
          try solve_conj_impl;
          try (subst; solve_stable stableDB);
          try (intros; intros [? ?]; auto);
          try (destruct H1; split; auto).
          destruct H0 as [[? HI] [[?|?]|?]]; subst.
          - destruct H1 as [? [? ?]].
            simpl_all. rewrite H1 in *.
            destruct H0 as [[? ?] [? ?]].
            do 2 (split; auto).
            intros. apply H3 in H7; eauto.
          - destruct H1 as [? [? [? ?]]].
            specialize (H4 _ _ eq_refl eq_refl) as [? [? ?]].
            simpl_all. rewrite H4, H6 in *.
            destruct H0 as [[? ?] [? ?]].
            do 2 (split; auto).
            destruct H3 as (?&?&?&?&?&?).
            assert (x0 <> t) by congruence.
            specialize (H10 _ H11).
            apply H10. eauto.
          - destruct H1 as (?&?&?&?&?&?&?&?).
            specialize (H4 _ _ eq_refl eq_refl) as [? [? ?]].
            do 2 split.
            + simpl_all.
              destruct H3 as [? [? [? [? ?]]]].
              intros. apply H3 in H9. inversion H9; subst.
              assert (Δ x ρ π) by (apply H7; constructor).
              destruct H0 as [[? ?] [? ?]].
              apply H0 in H10. auto.
            + destruct H1. intros ? ? ? ?.
              eapply TaskValConflict; eauto.
            + simpl_all. rewrite H6 in *.
              destruct H0 as [[? ?] [? ?]].
              rewrite H8. destruct (Nat.eqb_spec x3 i); auto; subst.
              assert (t = x0) by congruence; subst. congruence.
            + destruct H1. intros ? ? ?. eapply TaskValConflict; eauto.
        }

        intros.
        destruct (beq a o) eqn:eq.
        (* succeeded *)
        {
          eapply provable_seq with (Q' := fun _ => I //\\ ALin t (ls_linr (cas o n) a)).
          2:{
            intros _.
            eapply provable_ret;
            try solve_conj_impl;
            try solve_stable stableDB.
            left; auto.
          }
          apply beq_true in eq; subst.
          eapply provable_conseq_weak_pre with
            (P' := !! ALinIdle t //\\ I //\\ (TaskCompleted t o n i \\// TaskPlaced t o n i)).
          {
            destruct 1 as [? [?[[? _] | [_ ?]]]]; try congruence.
            do 2 (split; auto).
          }
          eapply provable_conseq_weak_pre with
            (P' := !! ALinIdle t //\\ I //\\
                  ((    (⌜t = t⌝ //\\ TaskCompleted t o n i)
                    \\//(⌜t <> t⌝ //\\ IsExpired i))
                  \\// TaskPlaced t o n i)).
          {
            intros ? [? [? ?]].
            do 2 (split; eauto).
            destruct H2.
            - left; left; split; auto.
            - right; auto.
          }
          (* triple for complete *)
          eapply provable_conseq_weak_post;
          [| | |apply triple_complete];
          try solve_conj_impl;
          try (subst; solve_stable stableDB);
          try (intros; intros [? ?]; auto);
          try (destruct H1; split; auto).
          - destruct H2; try congruence.
            destruct H2 as [? [? [? | ?]]]; try congruence; auto.
          - destruct H0 as [[? ?] [[?|?]|?]].
            + destruct H2 as [? [? ?]].
              intros [? [? [? ?]]]. apply H0.
              apply H4 in H5. do 2 eexists; eauto.
            + destruct H2 as [? [? [? ?]]].
              intros [? [? [? ?]]]. apply H0.
              pose proof ac_nonempty (Δ x) as [? [? ?]].
              do 2 eexists; split; eauto.
              apply H2 in H8.
              pose proof ac_domexact _ _ _ _ _ H6 H8.
              apply H9; eauto.
            + destruct H2 as [? [? [? [? [? [? [? ?]]]]]]].
              destruct H4 as [? [? [? [? ?]]]].
              intros [? [? [? ?]]]. apply H0.
              apply H4 in H8. inversion H8; subst.
              apply H6 in H8. 
              do 2 eexists; split; eauto.
        }
        (* failed *)
        {
          eapply provable_seq with (Q' := fun _ => I //\\
            !! ALinIdle t //\\
            (⌜a <> o⌝ //\\ ALin t (ls_linr (cas o n) a) \\//
            ⌜a = o⌝ //\\ (TaskCompleted t o n i \\// TaskPlaced t o n i))).
          - eapply provable_ret;
            try solve_conj_impl;
            try solve_stable stableDB.
            left; auto.
          - intros _.
            eapply provable_ret;
            try solve_conj_impl;
            try solve_stable stableDB.
            left. destruct H0 as [? [? [[_ ?] | [? _]]]].
            + split; auto.
            + apply beq_false in eq. congruence.
        }
      }
    }
    {
      repeat try split; simpl_all;
      try (solve [
        inversion 1; subst; eauto |
        inversion H0
      ]).
      - inversion 1; subst.
        do 2 eexists; split; [reflexivity|]; eauto.
      - intros.
        exists None. intros.
        inversion H1; subst.
        destruct v; simpl; auto.
    }
  Qed.

End CCASImpl.
