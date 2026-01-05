Require Import FMapPositive.
Require Import Coq.PArith.PArith.
Require Import Coq.Program.Equality.
Require Import Classical.
Require Import Relation_Operators Operators_Properties.

Require Import coqrel.LogicalRelations.
Require Import models.EffectSignatures.
Require Import LinCCAL.
Require Import LTS.
Require Import Lang.
Require Import Semantics.
Require Import Assertion.
Require Import TPSimulation.


Module RGISimulation.
  Import Reg.
  Import LinCCALBase.
  Import LTSSpec.
  Import Semantics.
  Import AssertionsSingle.
  Import TPSimulation.

  Section Simulations.
    Context {E : Op.t}.
    Context {F : Op.t}.
    Context {VE : @LTS E}.
    Context {VF : @LTS F}.
    Context (M : ModuleImpl E F).

    CoInductive RGISimulation (R G : RGRelation) (I : Assertion) t (σ : State VE) c (ρ : State VF) π : Prop :=
    | RGISim_Error
        (rgisim_invariant : I (σ, ρ, π))
        (rgisim_error : poss_steps (ρ, π) PossError) :
        RGISimulation R G I t σ c ρ π
    | RGISim_Continue
      (rgisim_invstep : forall f c'
        (Hstep : invstep M t f c c'),
          G (σ, ρ, π) (σ, ρ, TMap.add t (ls_inv f) π) /\
          TMap.find t π = None /\
          RGISimulation R G I t σ c' ρ (TMap.add t (ls_inv f) π))
      (rgisim_retstep : forall f ret c'
        (Hstep : retstep t f ret c c'),
          G (σ, ρ, π) (σ, ρ, TMap.remove t π) /\
          TMap.find t π = Some (ls_linr f ret) /\
          RGISimulation R G I t σ c' ρ (TMap.remove t π))
      (rgisim_ustep : forall ev σ' c'
        (Hstep : ustep (Build_ThreadEvent t ev) σ c σ' c'),
          exists ρ' π',
            poss_steps (ρ, π) (ρ', π') /\
            G (σ, ρ, π) (σ', ρ', π') /\
            RGISimulation R G I t σ' c' ρ' π')
      (rgisim_linstep :
          exists ρ' π',
          poss_steps (PossOk ρ π) (PossOk ρ' π') /\
          G (σ, ρ, π) (σ, ρ', π') /\
          RGISimulation R G I t σ c ρ' π')
      (rgisim_taustep : forall c' (Hstep : taustep t c c'),
        RGISimulation R G I t σ c' ρ π)

      (rgisim_invariant : I (σ, ρ, π))
      (rgisim_stable : forall σ' ρ' π'
        (Hrely : R (σ, ρ, π) (σ', ρ', π'))
        (Hinvariant : I (σ', ρ', π')),
          RGISimulation R G I t σ' c ρ' π')

      (rgisim_noerror : forall ev, ~ uerror (Build_ThreadEvent t ev) σ c) :
      
      RGISimulation R G I t σ c ρ π
    .

    Variant RGISimulation_invariant (R G : RGRelation) (I : Assertion) t (X : State VE -> ThreadPoolState -> State VF -> tmap LinState -> Prop) σ c ρ π: Prop := 
    | RGISim_Inv_Error
      (rgisim_invariant : I (σ, ρ, π))
      (rgisim_inv_error : poss_steps (ρ, π) PossError)
    | RGISim_Inv_Continue
      (rgisim_inv_invstep :
      forall f c'
        (Hstep : invstep M t f c c'),
          G (σ, ρ, π) (σ, ρ, TMap.add t (ls_inv f) π) /\
          TMap.find t π = None /\
          X σ c' ρ (TMap.add t (ls_inv f) π))
      (rgisim_inv_retstep :
        forall f ret c'
        (Hstep : retstep t f ret c c'),
          G (σ, ρ, π) (σ, ρ, TMap.remove t π) /\
          TMap.find t π = Some (ls_linr f ret) /\
          X σ c' ρ (TMap.remove t π))
      (rgisim_inv_ustep :
        forall ev σ' c'
        (Hstep : ustep (Build_ThreadEvent t ev) σ c σ' c'),
          exists ρ' π',
            poss_steps (ρ, π) (ρ', π') /\
            G (σ, ρ, π) (σ', ρ', π') /\
            X σ' c' ρ' π')
      (rgisim_inv_linstep :
          exists ρ' π',
          poss_steps (PossOk ρ π) (PossOk ρ' π') /\
          G (σ, ρ, π) (σ, ρ', π') /\
          X σ c ρ' π')
      (rgisim_inv_taustep :
        forall c' (Hstep : taustep t c c'),
        X σ c' ρ π)

      (rgisim_inv_invariant : I (σ, ρ, π))
      (rgisim_inv_stable :
        forall σ' ρ' π'
        (Hrely : R (σ, ρ, π) (σ', ρ', π'))
        (Hinvariant : I (σ', ρ', π')),
          X σ' c ρ' π')
      
      (rgisim_inv_noerror :
        forall ev, ~ uerror (Build_ThreadEvent t ev) σ c)
    .

    Lemma RGISimulation_invariant_sound R G I t (X : State VE -> ThreadPoolState -> State VF -> tmap LinState -> Prop):
      (forall σ c ρ π, X σ c ρ π -> RGISimulation_invariant R G I t X σ c ρ π) ->
      forall σ c ρ π, X σ c ρ π ->
      RGISimulation R G I t σ c ρ π.
    Proof.
      intros ?.
      cofix IH; intros.
      apply H in H0 as [? | ?];
      [constructor; auto|].
      apply RGISim_Continue; intros; auto.
      - (* inv *)
        eapply rgisim_inv_invstep in Hstep; eauto.
        do 2 (split; try tauto).
        apply IH; tauto.
      - (* ret *)
        eapply rgisim_inv_retstep in Hstep; eauto.
        do 2 (split; try tauto).
        apply IH; tauto.
      - (* ustep *)
        eapply rgisim_inv_ustep in Hstep as [? [? ?]]; eauto.
        exists x, x0.
        do 2 (split; try tauto).
        apply IH; tauto.
      - (* linstep *)
        destruct rgisim_inv_linstep as (? & ? & ? & ? & ?).
        exists x, x0.
        do 2 (split; try tauto).
        apply IH; tauto.
    Qed.

    Lemma rgisim_local_cont : forall R G I t σ ρ π c c',
      TMap.find t c = TMap.find t c' ->
      RGISimulation R G I t σ c ρ π ->
      RGISimulation R G I t σ c' ρ π.
    Proof.
      intros ? ? ? ?.
      cofix IH.
      intros ? ? ? ? ? Hfind Hsim.
      inversion Hsim; subst; [constructor; auto|].
      apply RGISim_Continue; intros; eauto.
      - eapply invstep_local_determ with (c2 := c) in Hstep as [? [? ?]]; eauto.
        specialize (rgisim_invstep _ _ H) as [? [? ?]].
        do 2 (split; auto).
        eapply IH with (c := x); auto.
      - eapply retstep_local_determ with (c2 := c) in Hstep as [? [? ?]]; eauto.
        specialize (rgisim_retstep _ _ _ H) as [? [? ?]].
        do 2 (split; auto).
        eapply IH with (c := x); auto.
      - eapply ustep_local_determ with (c2 := c) in Hstep as [? [? ?]]; eauto.
        specialize (rgisim_ustep _ _ _ H) as (? & ? & ? & ? & ?).
        exists x0, x1.
        do 2 (split; auto).
        eapply IH with (c := x); auto.
      - destruct rgisim_linstep as (? & ? & ? & ? & ?).
        exists x, x0.
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
      forall (σ : State VE) c (ρ : State VF) π
        (Htlsim : forall t, RGISimulation (R t) (G t) I t σ c ρ π),
        TPSimulation M σ c ρ π.
    Proof.
      intros ? ? ? ?.
      cofix IH.
      intros.
      assert (poss_steps (ρ0, π0) PossError \/ ~poss_steps (ρ0, π0) PossError)
      as [? | Hpnoerror] by apply classic; [constructor; auto |].
      apply TPSim_Continue; intros; eauto.
      - (* inv *)
        eapply IH; intros.
        pose proof (Htlsim t0) as [? | ?]; try congruence.
        pose proof (Htlsim t1) as [? | ?]; try congruence.
        destruct (Pos.eq_dec t0 t1); subst;
        specialize (rgisim_invstep _ _ Hstep) as (? & ? & ?); auto.
        eapply rgisim_local_cont with (c := c); auto.
        eapply invstep_local_cont; eauto.
        apply (rgisim_stable0 _ _ _ (HRG _ _ n _ _ H)).
        inversion H1; auto.
      - (* ret *)
        pose proof (Htlsim t0) as [? | ?]; try congruence.
        specialize (rgisim_retstep _ _ _ Hstep) as [? [? ?]].
        split; auto.
        eapply IH; intros.
        pose proof (Htlsim t1) as [? | ?]; try congruence.
        destruct (Pos.eq_dec t0 t1); subst; auto.
        eapply rgisim_local_cont with (c := c); auto.
        eapply retstep_local_cont; eauto.
        apply (rgisim_stable0 _ _ _ (HRG _ _ n _ _ H)).
        inversion H1; auto.
      - (* ustep *)
        destruct ev as [t ev].
        pose proof (Htlsim t) as [? | ?]; try congruence.
        specialize (rgisim_ustep _ _ _ Hstep) as (ρ' & π' & ? & ? & ?).
        exists ρ', π'. split; auto.
        eapply IH. intros.
        specialize (Htlsim t0) as [? | ?]; try congruence.
        destruct (Pos.eq_dec t t0); subst; auto.
        eapply rgisim_local_cont with (c := c); eauto.
        eapply ustep_local_cont; eauto.
        apply (rgisim_stable0 _ _ _ (HRG _ _ n _ _ H0)).
        inversion H1; auto.
      - (* linstep *)
        exists ρ0, π0.
        split; [apply rt_refl|]. auto.
      - (* tau *)
        pose proof (Htlsim t0) as [? | ?]; try congruence.
        specialize (rgisim_taustep _ Hstep).
        eapply IH. intros.
        destruct (Pos.eq_dec t1 t0); subst; auto.
        eapply rgisim_local_cont with (c := c); eauto.
        eapply taustep_local_cont; eauto.
      - destruct ev as [t ev].
        pose proof (Htlsim t) as [? | ?]; try congruence.
        auto.
    Qed.

    CoInductive MethodSimulation (R G : RGRelation) (I : Assertion) t (f : Sig.op F) (σ : State VE) p b (ρ : State VF) π : Prop := 
    | MSim_Error
      (msim_invariant : I (σ, ρ, π))
      (msim_error : poss_steps (ρ, π) PossError) :
      MethodSimulation R G I t f σ p b ρ π
    | MSim_Continue
      (msim_ustep : forall ev σ' p' b'
        (Hstep : ts_step f (Build_ThreadEvent t ev) σ (Build_ThreadState f p b) σ' (Build_ThreadState f p' b')),
          exists ρ' π',
            poss_steps (ρ, π) (ρ', π') /\
            G (σ, ρ, π) (σ', ρ', π') /\
            MethodSimulation R G I t f σ' p' b' ρ' π')
      (msim_retstep : forall ret
          (Hretv : p = Lang.Ret ret /\ b = None),
          (Gret t f ret ⊆ G)%RGRelation /\
          (I (σ, ρ, TMap.remove t π)) /\
          TMap.find t π = Some (ls_linr f ret))
      (msim_linstep :
          exists ρ' π',
          poss_steps (PossOk ρ π) (PossOk ρ' π') /\
          G (σ, ρ, π) (σ, ρ', π') /\
          MethodSimulation R G I t f σ p b ρ' π')
      (msim_taustep : forall p' b'
          (Hstep : ts_taustep (Build_ThreadState f p b) (Build_ThreadState f p' b')),
          MethodSimulation R G I t f σ p' b' ρ π)

      (msim_invariant : I (σ, ρ, π))
      (msim_stable : forall σ' ρ' π'
        (Hrely : R (σ, ρ, π) (σ', ρ', π'))
        (Hinvariant : I (σ', ρ', π')),
          MethodSimulation R G I t f σ' p b ρ' π')
      
      (msim_noerror :
        forall ev, ~ ts_error f (Build_ThreadEvent t ev) σ (Build_ThreadState f p b)) :
      
      MethodSimulation R G I t f σ p b ρ π
    .

    Variant MethodSimulation_invariant (R G : RGRelation) (I : Assertion) t (f : Sig.op F) (X : State VE -> Lang.Prog E (Sig.ar f) -> option (Sig.op E) -> State VF -> tmap LinState -> Prop) σ p b ρ π : Prop := 
    | MSim_Inv_Error
      (msim_invariant : I (σ, ρ, π))
      (msim_error : poss_steps (ρ, π) PossError)
    | MSim_Inv_Continue
      (msim_ustep : forall ev σ' p' b'
        (Hstep : ts_step f (Build_ThreadEvent t ev) σ (Build_ThreadState f p b) σ' (Build_ThreadState f p' b')),
          exists ρ' π',
            poss_steps (ρ, π) (ρ', π') /\
            G (σ, ρ, π) (σ', ρ', π') /\
            X σ' p' b' ρ' π')
      (msim_retstep : forall ret
          (Hretv : p = Lang.Ret ret /\ b = None),
          (Gret t f ret ⊆ G)%RGRelation /\
          (I (σ, ρ, TMap.remove t π)) /\
          TMap.find t π = Some (ls_linr f ret))
      (msim_linstep :
          exists ρ' π',
          poss_steps (PossOk ρ π) (PossOk ρ' π') /\
          G (σ, ρ, π) (σ, ρ', π') /\
          X σ p b ρ' π')
      (msim_taustep : forall p' b'
          (Hstep : ts_taustep (Build_ThreadState f p b) (Build_ThreadState f p' b')),
          X σ p' b' ρ π)

      (msim_invariant : I (σ, ρ, π))
      (msim_stable : forall σ' ρ' π'
        (Hrely : R (σ, ρ, π) (σ', ρ', π'))
        (Hinvariant : I (σ', ρ', π')),
          X σ' p b ρ' π')
      
      (msim_noerror :
        forall ev, ~ ts_error f (Build_ThreadEvent t ev) σ (Build_ThreadState f p b))
    .

    Lemma MethodSimulation_invariant_sound : forall R G I t f (X : State VE ->
  Lang.Prog E (Sig.ar f) -> option (Sig.op E) -> State VF -> tmap LinState -> Prop),
      (forall σ p b ρ π, X σ p b ρ π -> MethodSimulation_invariant R G I t f X σ p b ρ π) ->
      forall σ p b ρ π, X σ p b ρ π ->
      MethodSimulation R G I t f σ p b ρ π.
    Proof.
      intros ? ? ? ? ? ? ?.
      cofix IH; intros.
      apply H in H0 as [? | ?];
      [constructor; auto|].
      apply MSim_Continue; intros; auto.
      - (* ustep *)
        apply msim_ustep in Hstep as (? & ? & ? & ? & ?).
        exists x, x0. do 2 (split; auto).
      - (* linstep *)
        destruct msim_linstep as (? & ? & ? & ? & ?).
        exists x, x0. do 2 (split; auto).
    Qed.

    Record ValidRGI (R G : @RGRelation _ _ VE VF) (I : @Assertion _ _ VE VF) t : Prop := {
      (* HGinv : forall f, (Ginv t f ⊆ G)%RGRelation; *)
      (* HGI : forall f, (⊨ Ginv t f ⊚ I ==>> I)%Assertion; *)
      HRinv : forall s s', R s s' -> I s' -> TMap.find t (π s) = None <-> TMap.find t (π s') = None;
    }.

    Lemma msim_sequential_composition :
      forall (R G : RGRelation) (I : Assertion) t
      (Hrgi : ValidRGI R G I t)
      (Hmsim : forall f σ ρ π,
        (Ginv t f ⊚ I)%Assertion (σ, ρ, π) ->
        TMap.find t π = Some (ls_inv f) ->
        MethodSimulation R G I t f σ (M f) None ρ π)
      σ ρ
      (Hinvariant : I (σ, ρ, TMap.empty _))
      (HGinv : forall f, (Ginv t f ⊆ G)%RGRelation)
      (HGid : forall s, G s s),
      RGISimulation R G I t σ (@TMap.empty _) ρ (@TMap.empty _).
    Proof.
      remember (TMap.empty LinState) as π0.
      remember (TMap.empty ThreadState) as c0.
      intros ? ? ? ? ? ? ? ?.
      assert (TMap.find t0 π0 = None) as Hfindπ;
      [ subst; rewrite PositiveMap.gempty; auto | clear Heqπ0].
      assert (TMap.find t0 c0 = None) as Hfindc;
      [ subst; rewrite PositiveMap.gempty; auto | clear Heqc0].
      intros ? ? ?.

      apply RGISimulation_invariant_sound with (X:=fun σ c ρ π =>
        (
        TMap.find t0 π = None /\
        TMap.find t0 c = None /\
        I (σ, ρ, π))
        \/ 
        (exists ts, TMap.find t0 c = Some ts /\
        MethodSimulation R G I t0 (ts_op ts) σ (ts_prog ts) (ts_pend ts) ρ π)
      ); try tauto.
      clear - Hrgi Hmsim HGinv HGid.
      intros.
      destruct H as [[Hfindπ [Hfindc HI]] | [ts [Hfindc Hmsim']]].
      (* invstep *)
      {
        assert (poss_steps (ρ0, π0) PossError \/ ~poss_steps (ρ0, π0) PossError)
        as [? | Hpnoerror] by apply classic; [constructor; auto |].
        apply RGISim_Inv_Continue; intros; auto;
        try (inversion Hstep; subst; simpl in *; congruence).
        - inversion Hstep; subst. clear Hfind.
          split.
          {
            apply HGinv with (f:=f).
            unfold Ginv, LiftRelation_π.
            simpl; auto.
          }
          split; auto.
          right.
          exists {| ts_op := f; ts_prog := M f; ts_pend := None |}.
          rewrite PositiveMap.gss.
          split; auto.
          simpl.
          eapply Hmsim.
          * exists (σ0, ρ0, π0).
            split; auto.
            unfold Ginv, LiftRelation_π. auto.
          * rewrite PositiveMap.gss. auto.
        - exists ρ0, π0. split; [apply rt_refl|]; eauto.
        - left.
          split; try tauto.
          destruct Hrgi.
          apply HRinv0 in Hrely; auto.
          simpl in Hrely. apply Hrely; auto.
        - unfold not; intros.
          inversion H; subst; simpl in *; try congruence.
      }
      (* other steps *)
      {
        clear Hmsim; rename Hmsim' into Hmsim.
        
        assert (poss_steps (ρ0, π0) PossError \/ ~poss_steps (ρ0, π0) PossError)
        as [? | Hpnoerror] by apply classic; [constructor; auto; inversion Hmsim; auto |].
        apply RGISim_Inv_Continue; intros; auto;
        try (inversion Hstep; subst; simpl in *; congruence).
        - (* ret *)
          inversion Hstep; subst.
          rewrite Hfindc in Hfind.
          inversion Hfind; subst; clear Hfind.
          simpl in *.

          inversion Hmsim; try congruence.
          specialize (msim_retstep _ (conj eq_refl eq_refl)) as [? [? ?]].
          split.
          {
            eapply H.
            unfold Gret, LiftRelation_π. auto.
          }
          split; auto. left.
          do 2 rewrite PositiveMap.grs. auto.
        - (* ustep *)
          inversion Hstep; subst. simpl in *.
          rewrite Hfindc in Hfind. inversion Hfind; subst.
          clear Hfind.
          inversion Hmsim; try congruence.
          destruct ts1 as [f' p b].
          pose proof ts_step_inversion _ _ _ _ _ _ _ _ Hstep0 as [? [p' [b' ?]]]; subst.
          simpl in *.
          specialize (msim_ustep _ _ _ _ Hstep0) as [ρ' [π' [? [? ?]]]].
          exists ρ', π'.
          do 2 (split; auto).
          right.
          exists {| ts_op := f'; ts_prog := p'; ts_pend := b' |}.
          simpl.
          split; auto.
          rewrite PositiveMap.gss. auto.
        - (* linstep *)
          exists ρ0, π0. split; [apply rt_refl|]; eauto.
        - (* tau *)          
          inversion Hstep; subst.
          rewrite Hfindc in Hfind. inversion Hfind; subst.
          inversion Hstep0; subst; simpl in *.
          inversion Hmsim; try congruence.
          apply msim_taustep in Hstep0.
          right.
          exists {| ts_op := f; ts_prog := p; ts_pend := b |}.
          split; auto.
          rewrite PositiveMap.gss. auto.
        - (* invariant *)
          inversion Hmsim; auto.
        - (* rely *)
          right.
          exists ts.
          split; auto.
          inversion Hmsim; try congruence; auto.
        - (* noerror *)
          intros ?.
          inversion H; subst. simpl in *.
          inversion Herror; subst. simpl in *.
          rewrite Hfindc in Hfind.
          inversion Hfind; subst. simpl in *.
          inversion Hmsim; try congruence.
          eapply msim_noerror; eauto.
      }
    Qed.

  End Simulations.

End RGISimulation.
