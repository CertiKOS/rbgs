Require Import FMapPositive.
Require Import Relation_Operators Operators_Properties.
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
Require Import Assertion.
Require Import TPSimulationSet.
Require Import RGILogicSet.
Require Import Specs.


Module OneShotLazyCoinImpl.
  Import LinCCALBase.
  Import LTSSpec.
  Import Lang.
  Import Semantics.
  Import AssertionsSet.
  Import RGILogic.
  Import TPSimulation.
  Import AtomicLTS CoinSpec CASRegSpec.
  Import (coercions, canonicals, notations) Sig.
  Import (notations) LinCCAL.
  Import (canonicals) Sig.Plus.
  Open Scope prog_scope.
  Open Scope rg_relation_scope.

  Definition E : layer_interface :=
  {|
    li_sig := ECASReg (option bool);
    li_lts := VCASReg;
    li_init := Idle (Some false);
  |}.
  
  Definition F : layer_interface :=
  {|
    li_sig := ECoin;
    li_lts := VCoin;
    li_init := Idle false;
  |}.

  Parameter rand : bool.

  Definition flip_impl : Prog (li_sig E) unit :=
    set None >= _ => Ret tt.

  Definition read_impl : Prog (li_sig E) bool :=
    Do {
      get >= c =>
      match c with
      | Some b => Ret (inr b)
      | None =>
          let b := rand in
          cas None (Some b) >= succ =>
          Ret (if succ then inr b else inl tt)
      end
    } Loop.

  Definition assertion := @Assertion _ _ (li_lts E) (li_lts F).
  Definition rg_relation := @RGRelation _ _ (li_lts E) (li_lts F).

  Definition I : assertion :=
    fun s =>
            (* state correspondence *)
            ((state (σ s) = None /\ forall b, exists ρ π, Δ s ρ π /\ state ρ = b) \/
            (exists b, state (σ s) = Some b /\ exists ρ π, Δ s ρ π /\ state ρ = b))
            (* racy set implies racy flip *)
        /\  (forall v t w, σ s = Pending v t (set w) ->
              exists ρ π, Δ s ρ π /\ exists b, ρ = Pending b t flip)
        /\  ((forall v w t, σ s <> Pending v t (set w)) -> forall ρ π, Δ s ρ π -> exists b, ρ = Idle b)
        .
  
  Lemma idle_not_pending : forall (u v w : option bool) t, Idle u <> Pending v t (set w).
  Proof. inversion 1. Qed.

  Definition π_independent (P : assertion) := forall s1 s2,
    σ s1 = σ s2 ->
    (forall ρ1 π1, Δ s1 ρ1 π1 -> exists ρ2 π2, Δ s2 ρ2 π2 /\ ρ1 = ρ2) ->
    (forall ρ2 π2, Δ s2 ρ2 π2 -> exists ρ1 π1, Δ s1 ρ1 π1 /\ ρ1 = ρ2) ->
    P s1 -> P s2.

  Lemma I_π_independent: π_independent I.
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
  Qed.
  

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

  Create HintDb stableDB.
  Hint Resolve Istable ALinstable : stableDB.

  Program Definition Mcoin : layer_implementation E F := {|
    li_impl m :=
      match m with
      | flip => flip_impl
      | read => read_impl
      end
  |}.
  Next Obligation.
  eapply RGILogic.soundness with (R:=R) (G:=G) (I:=I).
    (* valid RG *)
    {
      constructor.
      unfold R. intros.
      destruct H.
      split; intros.
      - pose proof ac_nonempty (Δ s) as [? [? ?]].
        specialize (H2 _ _ H4).
        specialize (H _ _ _ _ H4 H3).
        rewrite <- H; auto.
      - pose proof ac_nonempty (Δ s') as [? [? ?]].
        specialize (H2 _ _ H4).
        specialize (H _ _ _ _ H3 H4).
        rewrite H; auto.
    }
    (* G ⊆ R *)
    {
      unfold G, R.
      intros. intros ? ? ?.
      destruct H0.
      - destruct H0.
        eapply domexact_RG_compatible in H0; eauto.
        split; auto.
      - do 2 destruct H0.
        + split; [eapply GINV_domexact|]; eauto.
          unfold GINV, Ginv, LiftRelation_Δ, ALin in *.
          destruct H0 as [? [? [? ?]]].
          intros. apply H2 in H4.
          inversion H4; subst.
          rewrite PositiveMap.gso; auto.
          eapply H3; eauto.
        + split; [eapply GRET_domexact|]; eauto.
          unfold GRET, Gret, LiftRelation_Δ, ALin in *.
          destruct H0 as [? [? [? [? ?]]]].
          intros. apply H2 in H4.
          inversion H4; subst.
          rewrite PositiveMap.gro; auto.
          eapply H3; eauto.
        + split; auto.
          apply domexact_R_refl.
    }
    (* method provable *)
    {
      intros t.
      destruct f.
      (* flip *)
      {
        (* precondition *)
        exists (I //\\ ALin t (Semantics.ls_inv flip)).
        (* postcondition *)
        exists (fun ret => I //\\ ALin t (Semantics.ls_linr flip ret)).
        constructor;
        try solve_conj_impl;
        try solve_conj_stable stableDB.
        {
          intros ? [? [? [? [? ?]]]].
          split; auto.
          - eapply I_π_independent; eauto.
            intros.
            exists ρ1. eexists; split; auto.
            apply H2. constructor; eauto.
            intros.
            apply H2 in H3. inversion H3; subst.
            exists ρ2. eexists; split; eauto.
          - intros ? ? ?.
            apply H2 in H3.
            inversion H3; subst.
            rewrite PositiveMap.gss; auto.
        }
        {
          intros. intros [? [[? ?] [? [? ?]]]].
          eapply I_π_independent; eauto.
          intros. exists ρ1. eexists; split; auto.
          apply H3. constructor; eauto.
          intros.
          apply H3 in H4. inversion H4; subst.
          do 2 eexists; split; eauto.
        }
        {
          intros.
          destruct H.
          unfold ALin in *.
          eapply H1. eauto.
        }
        {
          simpl; unfold flip_impl.
          (* perror *)
          eapply provable_perror with
            (P' := I //\\ ALin t (ls_inv flip) //\\ fun s => forall v t' w, t <> t' -> σ s <> Pending v t' (set w)).
          {
            intros ? ?.
            destruct (σ s) eqn:eq.
            - left. split; eauto.
              rewrite eq. congruence.
            - destruct op;
              try (left; split; eauto;
              rewrite eq; congruence).
              destruct (Pos.eq_dec t0 t).
              + left. split; eauto. rewrite eq,e. congruence.
              + right.
                destruct H as [[_ ?] ?].
                apply H in eq as [? [? [? [? ?]]]]; subst.
                pose proof H1.
                apply H0 in H1.
                econstructor; eauto.
                do 2 econstructor; eauto.
                econstructor; eauto.
          }
          (* set *)
          eapply provable_vis_safe with
            (P' := I //\\ ALin t (ls_lini flip))
            (Q' := fun _ => I //\\ ALin t (ls_linr flip tt));
          try solve_conj_impl;
          try solve_conj_stable stableDB.
          (* no error *)
          {
            intros ? [[[_ ?] ?] ?].
            intros ?.
            inversion H2; subst.
            dependent destruction H6.
            specialize (H1 v t' w H4). auto.
          }
          (* inv *)
          {
              pupdate_intros_atomic.
              dependent destruction Hstep0.
              destruct Hpre as [[? ?] ?].
              destruct H as [? [? ?]]. simpl in *.
              specialize (H3 (idle_not_pending _)). clear H2.
              destruct H.
              (* two poss *)
              {
                destruct H as [? ?].
                pose proof (H2 true) as [ρt [πt [Hposst ?]]].
                pose proof (H2 false) as [ρf [πf [Hpossf ?]]].
                clear H2.

                pose proof H3 _ _ Hposst as [? ?]; subst.
                pose proof H3 _ _ Hpossf as [? ?]; subst.
                simpl in *; subst.
                pose proof H0 _ _ Hposst.
                pose proof H0 _ _ Hpossf.

                pupdate_start.

                pupdate_trylin_from Hposst.
                pupdate_forward t0 (InvEv flip).
                pupdate_finish.

                eapply ACTrylinContinue.

                pupdate_trylin_from Hpossf.
                pupdate_forward t0 (InvEv flip).
                pupdate_finish.

                eapply ACTrylinFinish.

                do 2 split.
                - split; [|split]; simpl; auto.
                  + left. split; auto. intros.
                    destruct b;
                    [ exists (Pending true t0 flip) | exists (Pending false t0 flip) ];
                    eexists; split; auto;
                    [ right | left ]; econstructor; eauto;
                    do 2 constructor; try (do 2 econstructor); auto.
                  + inversion 1; subst.
                    do 2 eexists. split.
                    * left. constructor; eauto.
                      do 2 constructor; try (do 2 econstructor); auto.
                    * eauto.
                  + intros. exfalso. eapply H4. eauto.
                - unfold ALin; simpl.
                  inversion 1; subst;
                  inversion H5; subst;
                  rewrite PositiveMap.gss; auto.
                - unfold domexact_G; intros; simpl in *.
                  do 2 dependent destruction H6;
                  rewrite PositiveMap.gso; auto;
                  eapply (ac_domexact Δ1); eauto.
                - unfold ALin; simpl.
                  intros.
                  do 2 dependent destruction H6;
                  rewrite PositiveMap.gso; auto;
                  eapply H5; eauto.
              }
              (* single poss *)
              {
                destruct H as [? [? [ρ [π [Hposs ?]]]]]; subst.

                pose proof H3 _ _ Hposs as [? ?]; subst.
                pose proof H0 _ _ Hposs.
                simpl in *.

                pupdate_start.

                pupdate_trylin_from Hposs.
                pupdate_forward t0 (InvEv flip).
                pupdate_finish.

                eapply ACTrylinFinish.

                do 2 split.
                - split; [|split]; simpl; auto.
                  + right. eexists; split; eauto.
                    do 2 eexists; split.
                    constructor; auto.
                    do 2 constructor; try (do 2 econstructor); auto.
                    auto.
                  + inversion 1; subst.
                    do 2 eexists; split.
                    constructor; auto.
                    do 2 constructor; try (do 2 econstructor); auto.
                    eauto.
                  + intros. exfalso. eapply H2; eauto.
                - unfold ALin; simpl.
                  inversion 1; subst.
                  rewrite PositiveMap.gss; auto.
                - unfold domexact_G; intros; simpl in *.
                  dependent destruction H5.
                  rewrite PositiveMap.gso; auto;
                  eapply (ac_domexact Δ1); eauto.
                - unfold ALin; simpl.
                  intros.
                  dependent destruction H5;
                  rewrite PositiveMap.gso; auto.
                  eapply H4; eauto.
              }
          }
          (* res *)
          {
              pupdate_intros_atomic.
              dependent destruction Hstep0.
              destruct Hpre as [[? [? ?]] ?]. simpl in *.
              clear H1.
              specialize (H0 _ _ _ eq_refl) as [ρ [π [Hposs [b ?]]]]; subst.
              pose proof H2 _ _ Hposs.

              pupdate_start.

              pupdate_trylin_from Hposs.
              pupdate_forward t0 (ResEv flip tt).
              pupdate_finish.

              eapply ACTrylinContinue.

              pupdate_trylin_from Hposs.
              pupdate_forward t0 (ResEv flip tt).
              pupdate_finish.

              eapply ACTrylinFinish.

              Unshelve.
              2:{ exact true. }
              2:{ exact false. }

              do 2 split.
              - split; [|split]; simpl; auto.
                + left. split; auto. intros.
                  destruct b0;
                  [ exists (Idle true) | exists (Idle false) ];
                  eexists; split; eauto;
                  [ right | left ];
                  constructor; eauto;
                  do 2 constructor; try (do 2 econstructor); auto.
                + inversion 1.
                + intros.
                  do 2 dependent destruction H3; eauto.
              - unfold ALin; simpl.
                intros.
                do 2 dependent destruction H1;
                rewrite PositiveMap.gss; auto.
              - unfold domexact_G; intros; simpl in *.
                do 2 dependent destruction H4;
                rewrite PositiveMap.gso; auto;
                eapply (ac_domexact Δ1); eauto.
              - unfold ALin; simpl.
                intros.
                do 2 dependent destruction H4;
                rewrite PositiveMap.gso; auto;
                eapply H3; eauto.
          }

          (* return *)
          intros.
          eapply provable_ret_safe; destruct ret;
          try solve_conj_impl;
          try solve_conj_stable stableDB;
          try apply ImplRefl.
        }
      }
      (* read *)
      {
        (* precondition *)
        exists (I //\\ ALin t (Semantics.ls_inv read)).
        (* postcondition *)
        exists (fun ret => I //\\ ALin t (Semantics.ls_linr read ret)).
        constructor;
        try solve_conj_impl;
        try solve_conj_stable stableDB.
        {
          intros ? [? [? [? [? ?]]]].
          split; auto.
          - eapply I_π_independent; eauto.
            intros.
            exists ρ1. eexists; split; auto.
            apply H2. constructor; eauto.
            intros.
            apply H2 in H3. inversion H3; subst.
            exists ρ2. eexists; split; eauto.
          - intros ? ? ?.
            apply H2 in H3.
            inversion H3; subst.
            rewrite PositiveMap.gss; auto.
        }
        {
          intros. intros [? [[? ?] [? [? ?]]]].
          eapply I_π_independent; eauto.
          intros. exists ρ1. eexists; split; auto.
          apply H3. constructor; eauto.
          intros.
          apply H3 in H4. inversion H4; subst.
          do 2 eexists; split; eauto.
        }
        {
          intros.
          destruct H.
          unfold ALin in *.
          eapply H1. eauto.
        }
        {
          simpl; unfold read_impl.
          (* loop *)
          eapply provable_doloop;
          try solve_conj_impl;
          try solve_conj_stable stableDB.

          (* get *)
          eapply provable_vis_safe with
            (P' := I //\\ ALin t (ls_inv read))
            (
              Q' := fun c =>
                match c with
                | Some b => I //\\ ALin t (ls_linr read b)
                | None => I //\\ ALin t (ls_inv read)
                end
            );
          try ((try destruct a); solve_conj_impl);
          try ((try destruct a); solve_conj_stable stableDB).
          (* no error *)
          (* TODO: extract a more general tactic for solving no error *)
          {
            apply ImplTauto; intros ? H; destruct σ;
            inversion H; subst.
            dependent destruction H5.
          }
          (* inv *)
          {
            pupdate_intros_atomic.
            dependent destruction Hstep0.
            destruct Hpre as [[? [? ?]] ?]; simpl in *.

            pupdate_start.
            apply ac_steps_refl.

            do 2 split; auto.
            - split; [|split]; simpl; auto; try inversion 1.
              intros. eapply H1; eauto.
              apply idle_not_pending.
            - unfold domexact_G. simpl. intros.
              eapply (ac_domexact Δ1); eauto.
          }
          (* res *)
          {
            intro b.
            pupdate_intros_atomic.
            dependent destruction Hstep0.
            destruct Hpre as [[? [? ?]] ?]; simpl in *.
            (* clear H1 H0. *)
            destruct H as [[? ?] | ?]; subst; simpl in *.
            (* None *)
            {
              pupdate_start.
              apply ac_steps_refl.

              do 2 split; auto.
              - split; [|split]; simpl; auto; try inversion 1; subst.
                intros. eapply H1; eauto. inversion 1.
              - unfold domexact_G. simpl. intros.
                eapply (ac_domexact Δ1); eauto.
            }
            (* Some *)
            {
              destruct H as [b0 [? [ρ [π [Hposs ?]]]]]; subst. simpl in *.
              clear H0.
              pose proof Hposs.
              eapply H1 in H as [? ?]; try congruence; subst; simpl in *.

              pupdate_start.

              pupdate_trylin_from Hposs.
              pupdate_forward t0 (InvEv read).
              pupdate_forward t0 (ResEv read x).
              pupdate_finish.

              apply ACTrylinFinish.

              do 2 split.
              - split; [|split]; simpl; auto.
                + right. eexists; split; eauto.
                  exists (Idle x); eexists; split; auto.
                  econstructor; auto.
                  apply H2 in Hposs.
                  eapply rt_trans; do 2 constructor; auto;
                  try constructor;
                  [apply step_read_inv | apply step_read_res |].
                  rewrite PositiveMap.gss; auto.
                + inversion 1.
                + intros. dependent destruction H0; eauto.
              - unfold ALin; simpl.
                intros. dependent destruction H.
                rewrite PositiveMap.gss. auto.
              - unfold domexact_G; simpl.
                intros. dependent destruction H3.
                do 2 try rewrite PositiveMap.gso; auto.
                eapply (ac_domexact Δ1); eauto.
              - unfold ALin; simpl.
                intros. dependent destruction H3.
                do 2 try rewrite PositiveMap.gso; eauto.
            }
          }

          destruct ret; 
          try (eapply provable_ret_safe;
          try solve_conj_impl;
          try solve_conj_stable stableDB;
          try apply ImplRefl).

          (* TODO: get the random value properly *)
          (* cas *)
          eapply provable_vis_safe with
            (P' := I //\\ ALin t (ls_inv read))
            (Q' := fun (succ : bool) => if succ then I //\\ ALin t (ls_linr read rand) else I //\\ ALin t (ls_inv read));
          try ((try destruct a); solve_conj_impl);
          try ((try destruct a); solve_conj_stable stableDB).
          (* no error *)
          {
            apply ImplTauto; intros ? H; destruct σ;
            inversion H; subst.
            dependent destruction H5.
          }
          (* inv *)
          {
            pupdate_intros_atomic.
            dependent destruction Hstep0.
            destruct Hpre as [[? [? ?]] ?]; simpl in *.

            pupdate_start.
            apply ac_steps_refl.

            do 2 split; auto.
            - split; [|split]; simpl; auto; try inversion 1.
              intros. eapply H1; eauto.
              apply idle_not_pending.
            - unfold domexact_G. simpl. intros.
              eapply (ac_domexact Δ1); eauto.
          }
          (* res *)
          {
            intro b.
            pupdate_intros_atomic.
            destruct Hpre as [[? [? ?]] ?]; simpl in *.
            remember (ResEv (cas None (Some rand)) b) as e in Hstep0.
            inversion Hstep0; subst; try inversion H5; subst.
            (* succ *)
            {
              clear H0.
              apply ResEvInversion in H5; subst.
              destruct H as [[_ ?] | [? [? ?]]]; [|congruence].
              specialize (H rand) as [ρ [π [Hposs ?]]].
              pose proof Hposs.
              eapply H1 in H0 as [? ?]; subst; try congruence.
              simpl in *; subst.
              
              pupdate_start.

              pupdate_trylin_from Hposs.
              pupdate_forward t0 (InvEv read).
              pupdate_forward t0 (ResEv read rand).
              pupdate_finish.

              apply ACTrylinFinish.

              do 2 split.
              - split; [|split]; simpl.
                + right. eexists; split; eauto.
                  do 2 eexists; split; econstructor; auto.
                  apply H2 in Hposs.
                  eapply rt_trans; do 2 constructor; try do 2 constructor; auto.
                  rewrite PositiveMap.gss; auto.
                + congruence.
                + intros.
                  dependent destruction H0. eauto.
              - unfold ALin; simpl.
                intros. dependent destruction H.
                rewrite PositiveMap.gss; auto.
              - unfold domexact_G; simpl.
                intros. dependent destruction H3.
                do 2 (rewrite PositiveMap.gso; auto).
                eapply (ac_domexact Δ1); eauto.
              - unfold ALin; simpl. intros.
                dependent destruction H3.
                do 2 (rewrite PositiveMap.gso; eauto).
            }
            {
              clear H0.
              inversion H4; subst.
              apply ResEvInversion in H4; subst.
              destruct H as [[? ?] | [? [? [ρ [π [Hposs ?]]]]]]; try congruence; subst.
              clear H8.
              pose proof Hposs.
              eapply H1 in H as [? ?]; subst; try congruence.

              pupdate_start.
              apply ac_steps_refl.
              
              do 2 split; auto.
              - split; [|split]; simpl.
                + right. eexists; split; eauto.
                + congruence.
                + intros. eapply H1; eauto.
                  congruence.
              - unfold domexact_G; simpl. intros.
                eapply (ac_domexact Δ1); eauto.
            }
          }

          (* return *)
          destruct ret;
          eapply provable_ret_safe;
          try solve_conj_impl;
          try solve_conj_stable stableDB;
          try apply ImplRefl.
        }
      }
    }
    {
      split; [|split]; simpl.
      - right. eexists; split; eauto.
        do 2 eexists; split; try constructor.
      - congruence.
      - intros. dependent destruction H0. eauto.
    }
  Defined.

End OneShotLazyCoinImpl.

Print Assumptions OneShotLazyCoinImpl.Mcoin.