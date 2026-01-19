Require Import FMapPositive.
Require Import Coq.PArith.PArith.
Require Import Coq.Program.Equality.
Require Import Lia.
Require Import Relation_Operators Operators_Properties.
Require Import Classical.

Require Import coqrel.LogicalRelations.
Require Import models.EffectSignatures.
Require Import LinCCAL.
Require Import LTS.
Require Import Lang.
Require Import Semantics.
Require Import Assertion.
Require Import TPSimulationSet.
Require Import RGISimulationSet.


(* threadpool simulation *)
Module RGILogic.
  Import Reg.
  Import LinCCALBase.
  Import LTSSpec.
  Import Semantics.
  Import AssertionsSet.
  Import TPSimulation.
  Import RGISimulation.
  Import Lang.

  Open Scope assertion_scope.

  Section ProgramLogic.
    Context {E : Op.t}.
    Context {F : Op.t}.
    Context {VE : @LTS E}.
    Context {VF : @LTS F}.
    Context (M : ModuleImpl E F).
    Context (R G : @RGRelation _ _ VE VF).
    Context (I : @Assertion _ _ VE VF).
    Context (t : tid).

    CoInductive HTripleProvable {A} : @Assertion _ _ VE VF -> Prog E A -> (A -> @Assertion _ _ VE VF) -> Prop :=
    | provable_ret : forall a P Q Punsafe
        (Hperror : ⊨ Punsafe ==>> P \\// APError)
        (HP : ⊨ P ==>> Q a)
        (HinvQ : ⊨ Q a ==>> I)
        (HstableQ : Stable R I (Q a)),
        HTripleProvable Punsafe (Ret a) Q
    | provable_vis : forall P Q m k P' Q' Punsafe
        (Hperror : ⊨ Punsafe ==>> P \\// APError)
        (Herror : ⊨ P ==>> ANoError (Build_ThreadEvent t (InvEv m)))
        (* invariant checks *)
        (HinvP' : ⊨ P' ==>> I)
        (HinvQ' : forall a, ⊨ Q' a ==>> I)
        (* stability checks *)
        (HstableP' : Stable R I P')
        (HstableQ' : forall a, Stable R I (Q' a)),
        (* possibility updates *)
        (G ⊨ P [ Build_ThreadEvent t (InvEv m) ]⭆ P') ->
        (forall ret, G ⊨ P' [ Build_ThreadEvent t (ResEv m ret) ]⭆ Q' ret) ->
        (* continuation Hoare triple *)
        (forall ret, HTripleProvable (Q' ret) (k ret) Q) ->
        HTripleProvable Punsafe (Vis m k) Q
    | provable_tau : forall P Q p,
        HTripleProvable P p Q ->
        HTripleProvable P (Tau p) Q
    (* MARK: cannot do induction over the proof tree *)
    (* | provable_perror : forall P P' Q p
        (HinvP' : ⊨ P' ==>> I)
        (HstableP' : Stable R I P')
        (HP' : ⊨ P ==>> P' \\// APError),
        HTripleProvable P' p Q ->
        HTripleProvable P p Q *)
    (* MARK: the current definition does not support linstep *)
    (* | provable_conseq_pre : forall P P' Q p
        (HinvP : ⊨ P' ==>> I)
        (HstableP : Stable R I P')
        (Hweak : G ⊨ P ⭆ P'),
        HTripleProvable P' p Q ->
        HTripleProvable P p Q *)
    .

    Inductive HTripleProvable_invariant {A} (X : @Assertion _ _ VE VF -> Prog E A -> Prop) Punsafe (p: Prog E A) Q: Prop :=
    | provable_inv_ret a P
        (Hp : p = Ret a)
        (Hperror : ⊨ Punsafe ==>> P \\// APError)
        (HP : ⊨ P ==>> Q a)
        (HinvQ : ⊨ Q a ==>> I)
        (HstableQ : Stable R I (Q a))
    | provable_inv_vis P m k P' Q'
        (Hp : p = (Vis m k))
        (Hperror : ⊨ Punsafe ==>> P \\// APError)
        (Herror : ⊨ P ==>> ANoError (Build_ThreadEvent t (InvEv m)))
        (* invariant checks *)
        (HinvP' : ⊨ P' ==>> I)
        (HinvQ' : forall a, ⊨ Q' a ==>> I)
        (* stability checks *)
        (HstableP' : Stable R I P')
        (HstableQ' : forall a, Stable R I (Q' a))
        (* possibility updates *)
        (Hpinv : G ⊨ P [ Build_ThreadEvent t (InvEv m) ]⭆ P')
        (Hpret : forall ret, G ⊨ P' [ Build_ThreadEvent t (ResEv m ret) ]⭆ Q' ret)
        (* continuation Hoare triple *)
        (Hnext : forall ret, X (Q' ret) (k ret))
    | provable_inv_tau p'
        (Hp : p = Tau p')
        (Hnext : X Punsafe p')
    .

    Lemma HTripleProvable_invariant_sound {A} (X : @Assertion _ _ VE VF -> Prog E A -> Prop) Q :
      (forall P p, X P p -> HTripleProvable_invariant X P p Q) ->
      forall P p, X P p -> HTripleProvable P p Q.
    Proof.
      intros ?.
      cofix IH.
      intros.
      apply H in H0; clear H.
      inversion H0; subst.
      - eapply provable_ret; eauto.
      - eapply provable_vis; eauto.
      - eapply provable_tau; eauto.
    Qed.

  End ProgramLogic.
      
  Notation "[ VE , VF , R , G , I , t ] ⊢ {{ P }} c {{ Q }}" := (@HTripleProvable _ _ VE VF R G I t _ P c Q) (at level 100).

  Section DerivedRules.
    Context {E : Op.t}.
    Context {F : Op.t}.
    Context {VE : @LTS E}.
    Context {VF : @LTS F}.
    Context (M : ModuleImpl E F).
    Context (R G : @RGRelation _ _ VE VF).
    Context (I : @Assertion _ _ VE VF).
    Context (t : tid).

    Lemma provable_perror {A} : forall P P' Q (p : Prog E A)
      (HP' : ⊨ P ==>> P' \\// APError),
      [VE, VF, R, G, I, t] ⊢ {{ P' }} p {{ Q }} ->
      [VE, VF, R, G, I, t] ⊢ {{ P }} p {{ Q }}.
    Proof.
      cofix IH; intros.
      inversion H; subst.
      - eapply provable_ret with (P:=P0); eauto.
        intros ? ?.
        apply HP' in H0 as [? | ?].
        + apply Hperror; auto.
        + right; auto.
      - eapply provable_vis with (P:=P0) (P':=P'0) (Q':=Q'); eauto.
        intros ? ?.
        apply HP' in H3 as [? | ?].
        + apply Hperror; auto.
        + right; auto.
      - eapply provable_tau.
        eapply IH; eauto.
    Qed.

    Lemma provable_vis_safe {A} : forall P Q m (k : Sig.ar m -> Prog E A) P' Q'
        (Herror : ⊨ P ==>> ANoError (Build_ThreadEvent t (InvEv m)))
        (* invariant checks *)
        (HinvP' : ⊨ P' ==>> I)
        (HinvQ' : forall a, ⊨ Q' a ==>> I)
        (* stability checks *)
        (HstableP' : Stable R I P')
        (HstableQ' : forall a, Stable R I (Q' a))
        (* possibility updates *)
        (Hpinv : G ⊨ P [ Build_ThreadEvent t (InvEv m) ]⭆ P')
        (Hpret : forall ret, G ⊨ P' [ Build_ThreadEvent t (ResEv m ret) ]⭆ Q' ret),
        (forall ret, [VE, VF, R, G, I, t] ⊢ {{ Q' ret }} (k ret) {{ Q }}) ->
        [VE, VF, R, G, I, t] ⊢ {{ P }} Vis m k {{ Q }}.
    Proof.
      intros.
      eapply provable_vis; eauto.
      apply ImplDisjLeft, ImplRefl.
    Qed.

    Lemma provable_ret_safe {A} : forall (a:A) P Q
        (HP : ⊨ P ==>> Q a)
        (HinvQ : ⊨ Q a ==>> I)
        (HstableQ : Stable R I (Q a)),
        [VE, VF, R, G, I, t] ⊢ {{ P }} Ret a {{ Q }}.
    Proof.
      intros.
      eapply provable_ret; [apply ImplDisjLeft, ImplRefl| | |]; eauto.
    Qed.
    
    
    Lemma provable_conseq_weak_pre {A} : forall P Q P' (p : Prog E A)
      (HPweak : ⊨ P ==>> P'),
      [VE, VF, R, G, I, t] ⊢ {{ P' }} p {{ Q }} ->
      [VE, VF, R, G, I, t] ⊢ {{ P }} p {{ Q }}.
    Proof.
      intros.
      revert dependent P.
      revert dependent p.
      cofix IH; intros.
      inversion H; subst.
      - eapply provable_ret with (P:=P0); auto.
        eapply ImplTrans; eauto.
      - eapply provable_vis with (P':=P'0) (Q':=Q'); auto.
        eapply ImplTrans; eauto.
      - eapply provable_tau with (P:=P); auto.
    Qed.

    Lemma provable_conseq_weak_post {A} : forall P Q Q' (p : Prog E A)
      (* invariant checks *)
      (HinvQ : forall a, ⊨ Q a ==>> I)
      (* stability checks *)
      (HstableQ : forall a, Stable R I (Q a))

      (HQstren : forall a, ⊨ Q' a ==>> Q a),
      [VE, VF, R, G, I, t] ⊢ {{ P }} p {{ Q' }} ->
      [VE, VF, R, G, I, t] ⊢ {{ P }} p {{ Q }}.
    Proof.
      intros.
      revert dependent P.
      revert dependent Q.
      revert dependent p.
      cofix IH; intros.
      inversion H; subst.
      - eapply provable_ret with (P:=P0); eauto.
        eapply ImplTrans; eauto.
      - eapply provable_vis with (P':=P') (Q':=Q'0); auto.
      - constructor; auto.
    Qed.

    Lemma provable_conseq_weak {A} : forall P Q P' Q' (p : Prog E A)
      (* invariant checks *)
      (HinvQ : forall a, ⊨ Q a ==>> I)
      (* stability checks *)
      (HstableQ : forall a, Stable R I (Q a))

      (HPweak : ⊨ P ==>> P')
      (HQstren : forall a, ⊨ Q' a ==>> Q a),
      [VE, VF, R, G, I, t] ⊢ {{ P' }} p {{ Q' }} ->
      [VE, VF, R, G, I, t] ⊢ {{ P }} p {{ Q }}.
    Proof.
      intros.
      eapply provable_conseq_weak_pre; eauto.
      eapply provable_conseq_weak_post; eauto.
    Qed.

    Lemma provable_seq {A B} : forall (p : Prog E A) (k : A -> Prog E B) P Q Q',
      [VE, VF, R, G, I, t] ⊢ {{ P }} p {{ Q' }} ->
      (forall a, [VE, VF, R, G, I, t] ⊢ {{ Q' a }} k a {{ Q }}) ->
      [VE, VF, R, G, I, t] ⊢ {{ P }} bindProg p k {{ Q }}.
    Proof.
      intros.
      revert dependent Q.
      revert dependent P.
      revert dependent p.
      cofix IH; intros.
      inversion H; subst.
      - rewrite bindRetUnfold.
        eapply provable_perror; eauto.
        eapply provable_conseq_weak_pre with (P':=Q' a); auto.
      - rewrite bindVisUnfold.
        eapply provable_vis with (P':=P'); eauto.
      - rewrite bindTauUnfold.
        eapply provable_tau; auto.
    Qed.

    Lemma provable_dowhile_unroll {A} : forall (pbody piter : Prog E A) (b : A -> bool) P Q,
      [VE, VF, R, G, I, t] ⊢ {{ P }} bindProg piter
        (fun r => if b r then Tau (whileAux b pbody pbody) else Ret r) {{ Q }} ->
      [VE, VF, R, G, I, t] ⊢ {{ P }} whileAux b pbody piter {{ Q }}.
    Proof.
      cofix IH; intros.
      destruct piter.
      - rewrite whileAuxVisUnfold.
        rewrite bindVisUnfold in H.
        inversion H; subst. dependent destruction H1.
        eapply provable_vis with (P:=P0) (P':=P') (Q':=Q'); eauto.
      - rewrite whileAuxRetUnfold.
        rewrite bindRetUnfold in H.
        destruct (b r); auto.
      - rewrite whileAuxTauUnfold.
        rewrite bindTauUnfold in H.
        inversion H; subst.
        eapply provable_tau. auto.
    Qed.

    Lemma provable_dowhile {A} : forall Iloop Q b (p : Prog E A)
      (Hpost : forall a, (⊨ Q a //\\ ⌜b a = true⌝ ==>> Iloop))
      (HQinv : forall a, ⊨ Q a ==>> I)
      (HQstable : forall a, Stable R I (Q a))
      (Hbody : [VE, VF, R, G, I, t] ⊢ {{ Iloop }} p {{ Q }}),
      [VE, VF, R, G, I, t] ⊢ {{ Iloop }} Do { p } While (b x) >= x {{ fun a => Q a //\\ ⌜b a = false⌝ }}.
    Proof.
      intros.
      unfold doWhile.

      pose proof Hbody as Hiter.
      remember Iloop as P in Hiter.
      remember p as p0 in Hiter.
      rewrite <- Heqp0 at 2.
      rewrite <- HeqP.
      clear HeqP Heqp0.

      eapply HTripleProvable_invariant_sound with (X := fun P' p' =>
        (exists p0, p' = whileAux b p p0 /\ [VE, VF, R, G, I, t]⊢ {{P'}} p0 {{Q}})
        \/
        (p' = Tau (whileAux b p p) /\ ⊨ P' ==>> Iloop)
      ).
      2:{
        left. eexists; split; eauto.
      }

      clear Hiter.
      intros.
      destruct H.
      - destruct H as [? [? ?]]; subst.
        inversion H0; subst.
        + rewrite whileAuxRetUnfold.
          destruct (b a) eqn:eq.
          * eapply provable_inv_tau; eauto.
            left; eexists; split; eauto.
            eapply provable_conseq_weak_pre with (P':=Iloop \\// APError).
            ++
              eapply ImplTrans; eauto.
              intros ? [? | ?]; [|right;auto].
              left. eapply Hpost. split; unfold APure; [|exact eq].
              apply HP, H.
            ++
              eapply provable_perror; eauto. apply ImplRefl.
          * eapply provable_inv_ret; eauto; rewrite eq.
            ++
              intros ? ?. split; unfold APure; auto.
              apply HP, H.
            ++
              apply ConjLeftImpl; auto.
            ++
              apply EquivStable with (P:=Q a); auto.
              split; intros ?; unfold APure; try split; auto.
              destruct H; auto.
        + rewrite whileAuxVisUnfold.
          eapply provable_inv_vis; eauto.
        + rewrite whileAuxTauUnfold.
          eapply provable_inv_tau; eauto.
      - destruct H; subst.
        eapply provable_inv_tau; eauto.
        left. eexists; split; eauto.
        eapply provable_conseq_weak_pre; eauto.
    Qed.

    Lemma provable_doloop {TT FT} : forall Iloop Q (p : Prog E (TT + FT))
      (HQinv : forall a, ⊨ Q a ==>> I)
      (HQstable : forall a, Stable R I (Q a))
      (Hbody : [VE, VF, R, G, I, t] ⊢ {{ Iloop }} p {{ fun r => match r with | inl _ => Iloop | inr v => Q v end }}),
      [VE, VF, R, G, I, t] ⊢ {{ Iloop }} Do { p } Loop {{ Q }}.
    Proof.
      
      intros.
      unfold loop.

      pose proof Hbody as Hiter.
      remember Iloop as P in Hiter at 1.
      remember p as p0 in Hiter.
      rewrite <- Heqp0 at 2.
      rewrite <- HeqP.
      clear HeqP Heqp0.

      eapply HTripleProvable_invariant_sound with (X := fun P' p' =>
        (exists p0, p' = loopAux p p0 /\ [VE, VF, R, G, I, t]⊢ {{P'}} p0 {{ fun r => match r with | inl _ => Iloop | inr v => Q v end }})
        \/
        (p' = Tau (loopAux p p) /\ ⊨ P' ==>> Iloop)
      ).
      2:{
        left. eexists; split; eauto.
      }

      clear Hiter.
      intros.
      destruct H.
      - destruct H as [? [? ?]]; subst.
        inversion H0; subst.
        + rewrite loopAuxRetUnfold.
          destruct a eqn:eq.
          * eapply provable_inv_tau; eauto.
            left; eexists; split; eauto.
            eapply provable_conseq_weak_pre with (P':=Iloop \\// APError).
            ++
              eapply ImplTrans; eauto.
              intros ? [? | ?]; [|right;auto].
              left. eapply HP, H.
            ++
              eapply provable_perror; eauto. apply ImplRefl.
          * eapply provable_inv_ret; eauto.
        + rewrite loopAuxVisUnfold.
          eapply provable_inv_vis; eauto.
        + rewrite loopAuxTauUnfold.
          eapply provable_inv_tau; eauto.
      - destruct H; subst.
        eapply provable_inv_tau; eauto.
        left. eexists; split; eauto.
        eapply provable_conseq_weak_pre; eauto.
    Qed.

  End DerivedRules.

  Section ProgramLogic.
    Context {E : Op.t}.
    Context {F : Op.t}.
    Context (VE : @LTS E).
    Context (VF : @LTS F).
    Context (M : ModuleImpl E F).
    Context (R G : @RGRelation _ _ VE VF).
    Context (I : @Assertion _ _ VE VF).
    Context (t : tid).

    Record MethodProvable f P Q : Prop := {
      Pinv : ⊨ Ginv t f ⊚ I ==>> P;
      PI : ⊨ P ==>> I;
      Pstable : Stable R I P;
      Qret : forall ret, ⊨ Gret t f ret ⊚ Q ret ==>> I;
      Qlin : forall ret σ Δ, Q ret (σ, Δ) -> forall ρ π, Δ ρ π -> TMap.find t π = Some (ls_linr f ret);
      Triple : ([VE, VF, R, G, I, t] ⊢ {{ P }} (M f) {{ Q }});
    }.

    Lemma logic_soundness f P Q
      (HvalidRG : ValidRGI R G I t)
      (Hprovable : MethodProvable f P Q) :
      forall σ Δ
        (HI : (Ginv t f ⊚ I) (σ, Δ))
        (Hfindπ : forall ρ π, Δ ρ π -> TMap.find t π = Some (ls_inv f)),
        MethodSimulation R (G ∪ (GINV t ∪ GRET t ∪ GId)) I t f σ (M f) None Δ.
    Proof.
      intros.

      destruct HvalidRG as [HRinv].
      destruct Hprovable as [HPinv HPI HPstable HQret HQlin HTriple].

      apply HPinv in HI. clear HPinv. rename HI into HP.
      
      assert (forall (ρ : State VF) (π : tmap LinState), Δ0 ρ π -> exists ls, TMap.find t π = Some ls); eauto.
      clear Hfindπ; rename H into Hfindπ.
      remember (M f) as p; clear Heqp.

      eapply MethodSimulation_invariant_sound
      with (X:= fun σ p b (Δ : AbstractConfig VF) =>
        (forall ρ π, Δ ρ π -> exists ls : LinState, TMap.find t π = Some ls) /\
        match b with
        | None    =>
            exists P, P (σ, Δ) /\ [VE, VF, R, G, I, t]⊢ {{P}} p {{Q}}
            /\ (⊨ P ==>> I) /\ Stable R I P
        | Some m  =>
            exists k P' Q', p = Vis m k /\ P' (σ, Δ)
              /\ (forall ret, G ⊨ P' [ Build_ThreadEvent t (ResEv m ret) ]⭆ Q' ret)
              /\ (forall ret, [VE, VF, R, G, I, t]⊢ {{Q' ret}} k ret {{Q}})
              /\ (⊨ P' ==>> I) /\ (Stable R I P')
              /\ (forall ret, ⊨ Q' ret ==>> I) /\ (forall ret, Stable R I (Q' ret))
        end
      ).

      2:{
        split; auto.
        eexists; eauto.
      }

      clear - HRinv HQret HQlin.

      intros ? ? ? ? [Hfindπ H].

      (* prove stability separately *)
      assert (
        forall σ' Δ',
          R (σ0, Δ0) (σ', Δ') ->
          I (σ', Δ') ->
          (forall ρ π, Δ' ρ π -> exists ls0 : LinState, TMap.find t π = Some ls0) /\
          match b with
          | Some m0 =>
              exists
                (k : SigBase.ar m0 -> Prog E (Sig.ar f)) (P' : ProofState -> Prop) 
              (Q' : Sig.ar m0 -> Assertion),
                p = (m0 >= x => k x)%Prog /\
                P' (σ', Δ') /\
                (forall ret : Sig.ar m0,
                G ⊨ P' [ {| te_tid := t; te_ev := ResEv m0 ret |} ]⭆ Q' ret) /\
                (forall ret : Sig.ar m0, [VE, VF, R, G, I, t]⊢ {{Q' ret}} k ret {{Q}}) /\
                (⊨ P' ==>> I) /\
                Stable R I P' /\
                (forall ret : Sig.ar m0, ⊨ Q' ret ==>> I) /\
                (forall ret : Sig.ar m0, Stable R I (Q' ret))
          | None =>
              exists P : ProofState -> Prop,
                P (σ', Δ') /\
                ([VE, VF, R, G, I, t]⊢ {{P}} p {{Q}}) /\ (⊨ P ==>> I) /\ Stable R I P
          end
      ) as Hstable.
      {
        intros.
        split.
        {
          intros.
          destruct (TMap.find t π) eqn:eq; eauto.
          exfalso.
          apply HRinv in H0; eauto.
          simpl in *.
          assert (forall (ρ' : State VF) (π' : tmap LinState), Δ' ρ' π' -> TMap.find t π' = None).
          {
            intros.
            eapply ac_domexact; [| | exact eq]; eauto.
          }
          rewrite <- H0 in H3.
          pose proof ac_nonempty Δ0 as [ρ0 [π0 ?]].
          specialize (Hfindπ _ _ H4) as [ls ?].
          specialize (H3 ρ0 π0 H4). congruence.
        }
        
        destruct b.
        - destruct H as (k & P' & Q' & ? & HP' & Hupd & HTriple & HP'I & HP'stable & HQ'I & HQ'stable); subst.
          exists k, P', Q'.
          repeat (split; eauto).
          apply HP'stable.
          split; auto.
          eexists; split; eauto.
        - destruct H as (P & HP & HTriple & HPI & HPstable).
          exists P.
          repeat (split; auto).
          apply HPstable.
          split; auto.
          eexists; split; eauto.
      }

      assert (I (σ0, Δ0)) as Hinvariant.
      {
        destruct b.
        - destruct H as (k & P' & Q' & ? & HP' & Hupd & HTriple & HP'I & HP'stable & HQ'I & HQ'stable); subst.
          apply HP'I; auto.
        - destruct H as (P & HP & HTriple & HPI & HPstable).
          apply HPI; auto.
      }


      destruct b.
      (* ustep ret *)
      {
        destruct H as (k & P' & Q' & ? & HP' & Hupd & HTriple & HP'I & HP'stable & HQ'I & HQ'stable); subst.
        apply MSim_Inv_Continue; intros; auto;
        try (inversion Hstep; subst; simpl in *; congruence);
        try (destruct Hretv as [Hretv _]; inversion Hretv; subst).
        - inversion Hstep; subst.
          dependent destruction H7.
          eapply Hupd in Hstep0 as (Δ' & Hpstep & HQ' & HG); eauto.
          exists Δ'.
          split; auto.
          split; [left; auto|].
          split; eauto.
          intros.
          apply Hpstep in H. inversion H; subst.
          apply Hfindπ in Hposs as [? ?].
          eapply poss_steps_nondec; eauto.
        - exists Δ0.
          split; [apply ac_steps_refl|].
          split; [right; right; reflexivity|].
          split; eauto.
          do 3 eexists.
          split; eauto.
          split; [exact HP'|].
          do 2 (split; eauto).
        - inversion 1.
      }
      destruct H as (Pu & HPu & HTriple & HPuI & HPustable).
      revert Δ0 Hfindπ HPu Hstable Hinvariant.

      inversion HTriple; intros; subst.
      (* induction HTriple; intros; subst. *)
      (* ret *)
      {
        destruct (Hperror _ HPu) as [HP0 | ?];
        [| inversion H; subst; eapply MSim_Inv_Error; eauto].
        apply MSim_Inv_Continue; intros; auto;
        try (inversion Hstep; subst; simpl in *; congruence);
        try (destruct Hretv as [Hretv _]; inversion Hretv; subst).
        - split; [| split].
          * intros ? ? ?.
            right; left; right; eexists; eauto.
          * eapply HQret.
            eexists. split.
            + apply HP; eauto.
            + unfold Gret, LiftRelation_Δ. simpl.
              repeat (split; auto).
              eapply HQlin. apply HP; eauto.
          * eapply HQlin. apply HP; eauto.
        - exists Δ0.
          split; [apply ac_steps_refl|].
          split; [right; right; reflexivity|].
          split; eauto.
          (* exists P. split; eauto.
          split; [constructor|]; auto. *)
        - unfold not; inversion 1.
      }
      (* ustep inv *)
      {
        destruct (Hperror _ HPu) as [HP0 | ?];
        [| inversion H2; subst; eapply MSim_Inv_Error; eauto].
        apply MSim_Inv_Continue; intros; auto;
        try (inversion Hstep; subst; simpl in *; congruence);
        try (destruct Hretv as [Hretv _]; inversion Hretv; subst).
        - inversion Hstep; subst.
          dependent destruction H9.
          eapply H in Hstep0 as (Δ' & Hpstep & HP' & HG); eauto.
          exists Δ'.
          split; auto.
          split; [left; auto|].
          split.
          + intros.
            apply Hpstep in H2.
            inversion H2; subst.
            apply Hfindπ in Hposs as [? ?].
            eapply poss_steps_nondec; eauto.
          + exists k, P', Q'.
            do 3 (split; auto).
        - exists Δ0.
          split; [apply ac_steps_refl|].
          split; [right; right; reflexivity|].
          split; eauto.
        - inversion 1. dependent destruction H8; subst.
          apply Herror in HP0. auto.
      }
      (* tau *)
      {
        apply MSim_Inv_Continue; intros; auto;
        try (inversion Hstep; subst; simpl in *; congruence);
        try (destruct Hretv as [Hretv _]; inversion Hretv; subst).
        - exists Δ0.
          split; [apply ac_steps_refl|].
          split; [right; right; reflexivity|].
          split; eauto.
        - inversion Hstep; subst.
          dependent destruction H4.
          split; eauto.
        - inversion 1.
      }
    Qed.
  End ProgramLogic.

  Lemma soundness
    {E F} (VE : @LTS E) (VF : @LTS F) (M : ModuleImpl E F) (R G : tid -> RGRelation) I
    (HvalidRG : forall t, ValidRGI (R t) (G t) I t)
    (HRG : forall t1 t2 : tid, t1 <> t2 -> (G t1 ∪ (GINV t1 ∪ GRET t1 ∪ GId) ⊆ R t2)%RGRelation)
    (Hprovable : forall t f, exists P Q, MethodProvable VE VF M (R t) (G t) I t f P Q)
    σ0 ρ0
    (Hinit : I (σ0, ρ0, (@TMap.empty _)))
    :
    TPSimulation.cal M σ0 ρ0.
  Proof.
    unfold TPSimulation.cal.
    eapply rgisim_parapllel_composition with (I:=I) (G:=fun t => (G t ∪ (GINV t ∪ GRET t ∪ GId))%RGRelation); eauto.
    (* [exists ρ0, (@TMap.empty _); constructor |]. *)
    intros.
    eapply msim_sequential_composition; eauto.
    - destruct (HvalidRG t0). constructor; auto.
    - intros.
      destruct (Hprovable t0 f) as [P [Q ?]].
      eapply logic_soundness; eauto.
    - intros ? ? ? ?.
      right; do 2 left.
      unfold GINV. eauto.
    - right; right. reflexivity.
  Qed.

End RGILogic.
