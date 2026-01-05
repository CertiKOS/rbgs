Require Import FMapPositive.
Require Import Coq.PArith.PArith.
Require Import Coq.Program.Equality.
Require Import Classical.
Require Import Relation_Operators Operators_Properties.
Require Import Coq.Classes.RelationClasses.

Require Import coqrel.LogicalRelations.
Require Import models.EffectSignatures.
Require Import LinCCAL.
Require Import LTS.
Require Import Lang.
Require Import Semantics.
Require Import Assertion.
Require Import TPSimulationSet.


Module RGISimulation.
  Import Reg.
  Import LinCCALBase.
  Import LTSSpec.
  Import Semantics.
  Import AssertionsSet.
  Import TPSimulation.

  Section Simulations.
    Context {E : Op.t}.
    Context {F : Op.t}.
    Context {VE : @LTS E}.
    Context {VF : @LTS F}.
    Context (M : ModuleImpl E F).

    CoInductive RGISimulation (R G : @RGRelation _ _ VE VF) (I : @Assertion _ _ VE VF) t (σ : State VE) c (Δ : AbstractConfig VF) : Prop :=
    | RGISim_Error ρ π
      (Hinvariant : I (σ, Δ))
      (Hposs : Δ ρ π)
      (Herror : poss_steps (PossOk ρ π) (PossError))
    | RGISim_Continue
      (rgisim_invstep : forall f c'
        (Hstep : invstep M t f c c'),
          (Ginv t f ⊆ G)%RGRelation /\
          (forall ρ π, Δ ρ π -> TMap.find t π = None) /\
          RGISimulation R G I t σ c' (ac_inv Δ t f))
      (rgisim_retstep : forall f ret c'
        (Hstep : retstep t f ret c c'),
          (Gret t f ret ⊆ G)%RGRelation /\
          (forall ρ π, Δ ρ π -> TMap.find t π = Some (ls_linr f ret)) /\
          RGISimulation R G I t σ c' (ac_res Δ t))
      (rgisim_ustep : forall ev σ' c'
        (Hstep : ustep (Build_ThreadEvent t ev) σ c σ' c'),
          exists Δ', (Δ' ⊆ ac_steps Δ)%AbstractConfig /\
            G (σ, Δ) (σ', Δ') /\
            RGISimulation R G I t σ' c' Δ')
      (rgisim_linstep :
          exists Δ', (Δ' ⊆ ac_steps Δ)%AbstractConfig /\
          G (σ, Δ) (σ, Δ') /\
          RGISimulation R G I t σ c Δ')
      (rgisim_taustep : forall c' (Hstep : taustep t c c'),
        RGISimulation R G I t σ c' Δ)

      (rgisim_invariant : I (σ, Δ))
      (rgisim_stable : forall σ' Δ'
        (Hrely : R (σ, Δ) (σ', Δ'))
        (Hinvariant : I (σ', Δ')),
          RGISimulation R G I t σ' c Δ')

      (rgisim_noerror : forall ev, ~ uerror (Build_ThreadEvent t ev) σ c)
      (tpsim_nonemp : exists ρ π, Δ ρ π)
    .

    Variant RGISimulation_invariant (R G : RGRelation) (I : Assertion) t (X : State VE -> ThreadPoolState -> AbstractConfig VF -> Prop) σ c (Δ : AbstractConfig VF): Prop := 
    | RGISim_Inv_Error ρ π
      (Hinvariant : I (σ, Δ))
      (Hposs : Δ ρ π)
      (Herror : poss_steps (PossOk ρ π) (PossError))
    | RGISim_Inv_Continue
      (rgisim_invstep : forall f c'
        (Hstep : invstep M t f c c'),
          (Ginv t f ⊆ G)%RGRelation /\
          (forall ρ π, Δ ρ π -> TMap.find t π = None) /\
          X σ c' (ac_inv Δ t f))
      (rgisim_retstep : forall f ret c'
        (Hstep : retstep t f ret c c'),
          (Gret t f ret ⊆ G)%RGRelation /\
          (forall ρ π, Δ ρ π -> TMap.find t π = Some (ls_linr f ret)) /\
          X σ c' (ac_res Δ t))
      (rgisim_ustep : forall ev σ' c'
        (Hstep : ustep (Build_ThreadEvent t ev) σ c σ' c'),
          exists Δ', (Δ' ⊆ ac_steps Δ)%AbstractConfig /\
            G (σ, Δ) (σ', Δ') /\
            X σ' c' Δ')
      (rgisim_linstep :
          exists Δ', (Δ' ⊆ ac_steps Δ)%AbstractConfig /\
          G (σ, Δ) (σ, Δ') /\
          X σ c Δ')
      (rgisim_taustep : forall c' (Hstep : taustep t c c'),
        X σ c' Δ)

      (rgisim_invariant : I (σ, Δ))
      (rgisim_stable : forall σ' Δ'
        (Hrely : R (σ, Δ) (σ', Δ'))
        (Hinvariant : I (σ', Δ')),
          X σ' c Δ')

      (rgisim_noerror : forall ev, ~ uerror (Build_ThreadEvent t ev) σ c)
      (tpsim_nonemp : exists ρ π, Δ ρ π)
    .

    Lemma RGISimulation_invariant_sound R G I t (X : State VE -> ThreadPoolState -> AbstractConfig VF -> Prop):
      (forall σ c Δ, X σ c Δ -> RGISimulation_invariant R G I t X σ c Δ) ->
      forall σ c Δ, X σ c Δ ->
      RGISimulation R G I t σ c Δ.
    Proof.
      intros ?.
      cofix IH; intros.
      apply H in H0 as [? | ?];
      [eapply RGISim_Error; eauto|].
      apply RGISim_Continue; intros; auto.
      - (* inv *)
        eapply rgisim_invstep in Hstep as [? [? ?]].
        do 2 (split; eauto).
      - (* ret *)
        eapply rgisim_retstep in Hstep as [? [? ?]].
        do 2 (split; eauto).
      - (* ustep *)
        eapply rgisim_ustep in Hstep as [? [? [? ?]]]; eauto.
      - (* linstep *)
        destruct rgisim_linstep as (? & ? & ? & ?).
        exists x.
        do 2 (split; try tauto).
        apply IH; tauto.
    Qed.

    Lemma rgisim_local_cont : forall R G I t σ Δ c c',
      TMap.find t c = TMap.find t c' ->
      RGISimulation R G I t σ c Δ ->
      RGISimulation R G I t σ c' Δ.
    Proof.
      intros ? ? ? ?.
      cofix IH.
      intros ? ? ? ? Hfind Hsim.
      inversion Hsim; subst;
      [eapply RGISim_Error; eauto|].
      apply RGISim_Continue; intros; eauto.
      - eapply invstep_local_determ with (c2 := c) in Hstep as [? [? ?]]; eauto.
        specialize (rgisim_invstep _ _ H) as [? [? ?]]. do 2 (split; auto).
        eapply IH with (c := x); auto.
      - eapply retstep_local_determ with (c2 := c) in Hstep as [? [? ?]]; eauto.
        specialize (rgisim_retstep _ _ _ H) as [? [? ?]].
        do 2 (split; auto). eapply IH with (c := x); auto.
      - eapply ustep_local_determ with (c2 := c) in Hstep as [? [? ?]]; eauto.
        specialize (rgisim_ustep _ _ _ H) as (? & ? & ? & ?).
        exists x0.
        do 2 (split; auto).
        eapply IH with (c := x); auto.
      - destruct rgisim_linstep as (? & ? & ? & ?).
        exists x.
        do 2 (split; auto).
        eapply IH with (c := c); auto.
      - eapply taustep_local_determ with (c2 := c) in Hstep as [? [? ?]]; [|eauto].
        specialize (rgisim_taustep _ H).
        eapply IH with (c := x); auto.
      - unfold not in *.
        intros. eapply uerror_local_determ in H; eauto.
    Qed.
    
    Lemma rgisim_parapllel_composition :
      forall (R G : tid -> RGRelation) (I : Assertion)
        (HRG : forall t1 t2, t1 <> t2 -> (G t1 ⊆ R t2)%RGRelation),
      forall (σ : State VE) c Δ
        (Hnonemp : exists ρ π, Δ ρ π)
        (Htlsim : forall t, RGISimulation (R t) (G t) I t σ c Δ),
        TPSimulation M σ c Δ.
    Proof.
      intros ? ? ? ?.
      cofix IH.
      intros.
      assert ((exists ρ0 π0, Δ0 ρ0 π0 /\ poss_steps (ρ0, π0) PossError) \/ ~(exists ρ0 π0, Δ0 ρ0 π0 /\ poss_steps (ρ0, π0) PossError)) as [[? [? [? ?]]] | ?] by apply classic; [eapply TPSim_Error; eauto |].
      assert (forall ρ0 π0, Δ0 ρ0 π0 -> poss_steps (ρ0, π0) PossError -> False) as Hpnoerror; [intros; eauto|clear H].
      apply TPSim_Continue; intros; eauto.
      - (* inv *)
        eapply IH; intros.
        {
          destruct Hnonemp as [? [? ?]].
          do 2 eexists. econstructor. eauto.
        }
        pose proof (Htlsim t0) as [? | ?]; [exfalso; eapply Hpnoerror; eauto|].
        pose proof (Htlsim t1) as [? | ?]; [exfalso; eapply Hpnoerror; eauto|].
        destruct (Pos.eq_dec t0 t1); subst;
        specialize (rgisim_invstep _ _ Hstep) as (? & ? & ?); auto.
        eapply rgisim_local_cont with (c := c); auto.
        eapply invstep_local_cont; eauto.
        apply rgisim_stable0; [|inversion H1; auto].
        apply (HRG _ _ n), H.
        unfold Ginv, LiftRelation_Δ.
        do 2 (split; eauto). reflexivity.
      - (* ret *)
        pose proof (Htlsim t0) as [? | ?]; [exfalso; eapply Hpnoerror; eauto|].
        specialize (rgisim_retstep _ _ _ Hstep) as [? [? ?]].
        split; auto.
        eapply IH; intros.
        {
          destruct Hnonemp as [? [? ?]].
          do 2 eexists. econstructor. eauto.
        }
        pose proof (Htlsim t1) as [? | ?]; [exfalso; eapply Hpnoerror; eauto|].
        destruct (Pos.eq_dec t0 t1); subst; auto.
        eapply rgisim_local_cont with (c := c); auto.
        eapply retstep_local_cont; eauto.
        apply rgisim_stable0; [|inversion H1; auto].
        apply (HRG _ _ n), H.
        unfold Gret, LiftRelation_Δ.
        do 2 (split; eauto). reflexivity.
      - (* ustep *)
        destruct ev as [t ev].
        pose proof (Htlsim t) as [? | ?]; [exfalso; eapply Hpnoerror; eauto|].
        specialize (rgisim_ustep _ _ _ Hstep) as (Δ' & ? & ? & ?).
        exists Δ'. split; auto.
        eapply IH; intros.
        {
          destruct Hnonemp as [? [? ?]].
          inversion H1; eauto.
        }
        specialize (Htlsim t0) as [? | ?]; [exfalso; eapply Hpnoerror; eauto|].
        destruct (Pos.eq_dec t t0); subst; auto.
        eapply rgisim_local_cont with (c := c); eauto.
        eapply ustep_local_cont; eauto.
        apply rgisim_stable0; [|inversion H1; auto].
        eapply HRG; eauto.
      - exists Δ0. split; auto.
        apply TPSimulation.ac_steps_refl.
      - (* tau *)
        pose proof (Htlsim t0) as [? | ?]; [exfalso; eapply Hpnoerror; eauto|].
        specialize (rgisim_taustep _ Hstep).
        eapply IH; eauto; intros.
        destruct (Pos.eq_dec t1 t0); subst; auto.
        eapply rgisim_local_cont with (c := c); eauto.
        eapply taustep_local_cont; eauto.
      - (* no error *)
        destruct ev as [t ev].
        pose proof (Htlsim t) as [? | ?]; [exfalso; eapply Hpnoerror; eauto|].
        auto.
    Qed.

    CoInductive MethodSimulation (R G : @RGRelation _ _ VE VF) (I : Assertion) t (f : Sig.op F) (σ : State VE) p b (Δ : AbstractConfig VF) : Prop := 
    | MSim_Error ρ π
      (Hinvariant : I (σ, Δ))
      (Hposs : Δ ρ π)
      (Herror : poss_steps (PossOk ρ π) (PossError))
    | MSim_Continue
      (msim_ustep : forall ev σ' p' b'
        (Hstep : ts_step f (Build_ThreadEvent t ev) σ (Build_ThreadState f p b) σ' (Build_ThreadState f p' b')),
          exists Δ', (Δ' ⊆ ac_steps Δ)%AbstractConfig /\
            G (σ, Δ) (σ', Δ') /\
            MethodSimulation R G I t f σ' p' b' Δ')
      (msim_retstep : forall ret
          (Hretv : p = Lang.Ret ret /\ b = None),
          (Gret t f ret ⊆ G)%RGRelation /\
          (I (σ, ac_res Δ t)) /\
          (forall ρ π, Δ ρ π -> TMap.find t π = Some (ls_linr f ret)))
      (msim_linstep :
          exists Δ', (Δ' ⊆ ac_steps Δ)%AbstractConfig /\
          G (σ, Δ) (σ, Δ') /\
          MethodSimulation R G I t f σ p b Δ')
      (msim_taustep : forall p' b'
          (Hstep : ts_taustep (Build_ThreadState f p b) (Build_ThreadState f p' b')),
          MethodSimulation R G I t f σ p' b' Δ)

      (msim_invariant : I (σ, Δ))
      (msim_stable : forall σ' Δ'
        (Hrely : R (σ, Δ) (σ', Δ'))
        (Hinvariant : I (σ', Δ')),
          MethodSimulation R G I t f σ' p b Δ')
      
      (msim_noerror :
        forall ev, ~ ts_error f (Build_ThreadEvent t ev) σ (Build_ThreadState f p b))
      (msim_nonemp : exists ρ π, Δ ρ π)
    .

    Variant MethodSimulation_invariant (R G : RGRelation) (I : Assertion) t (f : Sig.op F) (X : State VE -> Lang.Prog E (Sig.ar f) -> option (Sig.op E) -> AbstractConfig VF -> Prop) σ p b Δ : Prop := 
    | MSim_Inv_Error ρ π
      (Hinvariant : I (σ, Δ))
      (Hposs : Δ ρ π)
      (Herror : poss_steps (PossOk ρ π) (PossError))
    | MSim_Inv_Continue
      (msim_ustep : forall ev σ' p' b'
        (Hstep : ts_step f (Build_ThreadEvent t ev) σ (Build_ThreadState f p b) σ' (Build_ThreadState f p' b')),
          exists Δ', (Δ' ⊆ ac_steps Δ)%AbstractConfig /\
            G (σ, Δ) (σ', Δ') /\
            X σ' p' b' Δ')
      (msim_retstep : forall ret
          (Hretv : p = Lang.Ret ret /\ b = None),
          (Gret t f ret ⊆ G)%RGRelation /\
          (I (σ, ac_res Δ t)) /\
          (forall ρ π, Δ ρ π -> TMap.find t π = Some (ls_linr f ret)))
      (msim_linstep :
          exists Δ', (Δ' ⊆ ac_steps Δ)%AbstractConfig /\
          G (σ, Δ) (σ, Δ') /\
          X σ p b Δ')
      (msim_taustep : forall p' b'
          (Hstep : ts_taustep (Build_ThreadState f p b) (Build_ThreadState f p' b')),
          X σ p' b' Δ)

      (msim_invariant : I (σ, Δ))
      (msim_stable : forall σ' Δ'
        (Hrely : R (σ, Δ) (σ', Δ'))
        (Hinvariant : I (σ', Δ')),
          X σ' p b Δ')
      
      (msim_noerror :
        forall ev, ~ ts_error f (Build_ThreadEvent t ev) σ (Build_ThreadState f p b))
      (msim_nonemp : exists ρ π, Δ ρ π)
    .

    Lemma MethodSimulation_invariant_sound : forall R G I t f (X : State VE ->
  Lang.Prog E (Sig.ar f) -> option (Sig.op E) -> AbstractConfig VF -> Prop),
      (forall σ p b Δ, X σ p b Δ -> MethodSimulation_invariant R G I t f X σ p b Δ) ->
      forall σ p b Δ, X σ p b Δ ->
      MethodSimulation R G I t f σ p b Δ.
    Proof.
      intros ? ? ? ? ? ? ?.
      cofix IH; intros.
      apply H in H0 as [? | ?];
      [eapply MSim_Error; eauto|].
      apply MSim_Continue; intros; auto.
      - (* ustep *)
        apply msim_ustep in Hstep as (? & ? & ? & ?).
        exists x. do 2 (split; auto).
      - (* linstep *)
        destruct msim_linstep as (? & ? & ? & ?).
        exists x. do 2 (split; auto).
    Qed.

    Record ValidRGI (R G : @RGRelation _ _ VE VF) (I : @Assertion _ _ VE VF) t : Prop := {
      (* HGinv : forall f, (Ginv t f ⊆ G)%RGRelation; *)
      (* HGI : forall f, (⊨ Ginv t f ⊚ I ==>> I)%Assertion; *)
      HRinv : forall s s', R s s' -> I s' ->
        (forall ρ π, Δ s ρ π -> TMap.find t π = None)
        <-> (forall ρ' π', Δ s' ρ' π' -> TMap.find t π' = None);

      HInonemp : forall s, I s -> exists ρ π, Δ s ρ π;

      HIpconsist: forall s ρ π, I s -> Δ s ρ π -> TMap.find t π = None ->
                    forall ρ π, Δ s ρ π -> TMap.find t π = None
    }.

    Lemma msim_sequential_composition :
      forall (R G : RGRelation) (I : Assertion) t
      (Hrgi : ValidRGI R G I t)
      (Hmsim : forall f σ Δ,
        (Ginv t f ⊚ I)%Assertion (σ, Δ) ->
        (forall ρ π, Δ ρ π -> TMap.find t π = Some (ls_inv f)) ->
        MethodSimulation R G I t f σ (M f) None Δ)
      σ ρ
      (Hinvariant : I (σ, ac_init ρ))
      (HGinv : forall f, (Ginv t f ⊆ G)%RGRelation)
      (HGid : forall s, G s s),
      RGISimulation R G I t σ (@TMap.empty _) (ac_init ρ).
    Proof.
      remember (TMap.empty ThreadState) as c0.
      intros ? ? ? ? ? ? ? ?.
      assert (TMap.find t0 c0 = None) as Hfindc;
      [ subst; rewrite PositiveMap.gempty; auto | clear Heqc0].
      remember (ac_init ρ) as Δ0.
      assert (exists ρ π, Δ0 ρ π) as Hnonemp;
      [ subst; eexists; econstructor; econstructor |].
      assert (forall ρ0 π0, Δ0 ρ0 π0 -> TMap.find t0 π0 = None) as Hfindπ;
      [ subst; inversion 1; subst; rewrite PositiveMap.gempty; auto | clear HeqΔ0].
      intros ? ? ?.

      apply RGISimulation_invariant_sound with (X:=fun σ c (Δ : AbstractConfig VF) =>
        (exists ρ π, Δ ρ π) /\
        ((
        (forall ρ π, Δ ρ π -> TMap.find t0 π = None) /\
        TMap.find t0 c = None /\
        I (σ, Δ))
        \/ 
        (exists ts, TMap.find t0 c = Some ts /\
        MethodSimulation R G I t0 (ts_op ts) σ (ts_prog ts) (ts_pend ts) Δ))
      ); try tauto.
      clear - Hrgi Hmsim HGinv HGid.
      intros.
      destruct H as [Hnonemp [[Hfindπ [Hfindc HI]] | [ts [Hfindc Hmsim']]]].
      (* invstep *)
      {
        assert ((exists ρ0 π0, Δ0 ρ0 π0 /\ poss_steps (ρ0, π0) PossError) \/ ~(exists ρ0 π0, Δ0 ρ0 π0 /\ poss_steps (ρ0, π0) PossError)) as [[? [? [? ?]]] | ?] by apply classic; [eapply RGISim_Inv_Error; eauto |].
        assert (forall ρ0 π0, Δ0 ρ0 π0 -> poss_steps (ρ0, π0) PossError -> False) as Hpnoerror; [intros; eauto|clear H].
        apply RGISim_Inv_Continue; intros; auto;
        try (inversion Hstep; subst; simpl in *; congruence).
        - inversion Hstep; subst. clear Hfind.
          do 2 (split; auto).
          split; [ destruct Hnonemp as [? [? ?]]; do 2 eexists; econstructor; eauto |].
          right.
          exists {| ts_op := f; ts_prog := M f; ts_pend := None |}.
          rewrite PositiveMap.gss.
          split; auto.
          simpl.
          eapply Hmsim.
          * exists (σ0, Δ0).
            split; auto.
            unfold Ginv, LiftRelation_Δ. simpl.
            do 2 (split; auto). reflexivity.
          * inversion 1; subst. rewrite PositiveMap.gss. auto.
        - exists Δ0. split; [apply TPSimulation.ac_steps_refl|].
          split; eauto.
        - destruct Hrgi.
          split; [ eapply HInonemp0 in Hinvariant; eauto |].
          left.
          split; try tauto.
          apply HRinv0 in Hrely; auto.
          simpl in Hrely. apply Hrely; auto.
        - unfold not; intros.
          inversion H; subst; simpl in *; try congruence.
      }
      (* other steps *)
      {
        clear Hmsim; rename Hmsim' into Hmsim.

        assert (I (σ0, Δ0)); [inversion Hmsim; auto|].
        assert ((exists ρ0 π0, Δ0 ρ0 π0 /\ poss_steps (ρ0, π0) PossError) \/ ~(exists ρ0 π0, Δ0 ρ0 π0 /\ poss_steps (ρ0, π0) PossError)) as [[? [? [? ?]]] | ?] by apply classic; [eapply RGISim_Inv_Error; eauto |].
        assert (forall ρ0 π0, Δ0 ρ0 π0 -> poss_steps (ρ0, π0) PossError -> False) as Hpnoerror; [intros; eauto|].
        clear H H0.
        
        apply RGISim_Inv_Continue; intros; auto;
        try (inversion Hstep; subst; simpl in *; congruence).
        - (* ret *)
          inversion Hstep; subst.
          rewrite Hfindc in Hfind.
          inversion Hfind; subst; clear Hfind.
          simpl in *.

          inversion Hmsim; [exfalso; eapply Hpnoerror; eauto|].
          specialize (msim_retstep _ (conj eq_refl eq_refl)) as [? [? ?]].
          do 2 (split; auto).
          split; [| left; do 2 try split; auto].
          + destruct msim_nonemp as [? [? ?]].
            do 2 eexists; econstructor; eauto.
          + inversion 1; subst. rewrite PositiveMap.grs. auto.
          + rewrite PositiveMap.grs. auto.
        - (* ustep *)
          inversion Hstep; subst. simpl in *.
          rewrite Hfindc in Hfind. inversion Hfind; subst.
          clear Hfind.
          inversion Hmsim; [exfalso; eapply Hpnoerror; eauto|].
          destruct ts1 as [f' p b].
          pose proof ts_step_inversion _ _ _ _ _ _ _ _ Hstep0 as [? [p' [b' ?]]]; subst.
          simpl in *.
          specialize (msim_ustep _ _ _ _ Hstep0) as [Δ' [? [? ?]]].
          exists Δ'.
          do 2 (split; auto).
          split; [inversion H1; eauto|].
          right.
          exists {| ts_op := f'; ts_prog := p'; ts_pend := b' |}.
          simpl.
          split; auto.
          rewrite PositiveMap.gss. auto.
        - (* linstep *)
          exists Δ0. split; [apply TPSimulation.ac_steps_refl |].
          split; eauto.
        - (* tau *)          
          inversion Hstep; subst.
          rewrite Hfindc in Hfind. inversion Hfind; subst.
          inversion Hstep0; subst; simpl in *.
          inversion Hmsim; [exfalso; eapply Hpnoerror; eauto|].
          split; eauto.
          apply msim_taustep in Hstep0. 
          right.
          exists {| ts_op := f; ts_prog := p; ts_pend := b |}.
          split; auto.
          rewrite PositiveMap.gss. auto.
        - (* invariant *)
          inversion Hmsim; auto.
        - (* rely *)
          split.
          + destruct Hrgi.
            apply HInonemp0 in Hinvariant; auto.
          + right.
            exists ts.
            split; auto.
            inversion Hmsim; [exfalso; eapply Hpnoerror; eauto|].
            auto.
        - (* noerror *)
          intros ?.
          inversion H; subst. simpl in *.
          inversion Herror; subst. simpl in *.
          rewrite Hfindc in Hfind.
          inversion Hfind; subst. simpl in *.
          inversion Hmsim; [exfalso; eapply Hpnoerror; eauto|].
          eapply msim_noerror; eauto.
      }
    Qed.

  End Simulations.

End RGISimulation.
