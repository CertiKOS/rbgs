Require Import FMapPositive.
Require Import Relation_Operators Operators_Properties.
Require Import Coq.PArith.PArith.
Require Import Coq.Program.Equality.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Program.Program.
Require Import Logic.ProofIrrelevance.
Require Import Logic.FunctionalExtensionality.
Require Import Logic.PropExtensionality.

Require Import coqrel.LogicalRelations.
Require Import models.EffectSignatures.
Require Import LinCCAL.
Require Import LTS.
Require Import Lang.
Require Import SeparationAlgebra.
Require Import FMapPositive.

Section TMapSA.
  Context {A : Type}.

  Inductive tree_join : LinCCAL.tmap A -> LinCCAL.tmap A -> LinCCAL.tmap A -> Prop :=
  | TJ_LeafLeft : forall t, tree_join (LinCCAL.TMap.Leaf _) t t
  | TJ_LeafRight : forall t, tree_join t (LinCCAL.TMap.Leaf _) t
  | TJ_Node : forall ml ml' ml'' mr mr' mr'' o o' o'',
      tree_join ml ml' ml'' ->
      tree_join mr mr' mr'' ->
      @option_Join _ trivial_Join o o' o'' ->
      tree_join (LinCCAL.TMap.Node ml o mr)
                (LinCCAL.TMap.Node ml' o' mr')
                (LinCCAL.TMap.Node ml'' o'' mr'').
  
  Lemma tree_join_increasing:
    forall t1 t2 t, tree_join t1 t2 t ->
      forall a b, LinCCAL.TMap.find a t1 = Some b -> LinCCAL.TMap.find a t = Some b.
  Proof.
    induction 1; intros; auto.
    - destruct a; simpl in *; congruence.
    - destruct a; simpl in *; auto; subst.
      inversion H1; subst; auto.
      inversion H3.
  Qed.
  
  Lemma tree_join_none:
    forall t1 t2 t, tree_join t1 t2 t ->
      forall a, LinCCAL.TMap.find a t = None <-> (LinCCAL.TMap.find a t1 = None /\ LinCCAL.TMap.find a t2 = None).
  Proof.
    induction 1; intros.
    - split; try tauto.
      intros. split; auto.
      destruct a; auto.
    - split; try tauto.
      intros. split; auto.
      destruct a; auto.
    - destruct a; simpl; auto.
      inversion H1; subst; try tauto.
  Qed.

  #[global] Instance tmap_Join : Join (LinCCAL.tmap A) := tree_join.
  #[global] Program Instance tmap_SA : SeparationAlgebra (LinCCAL.tmap A).
  Next Obligation.
    induction H; constructor; auto.
    eapply join_comm; auto.
    Unshelve. exact (@option_SA A trivial_Join trivial_SA).
  Qed.
  Next Obligation.
    rename H0 into Hz.
    revert mz mxyz Hz.
    induction H; intros; inversion Hz; subst;
    try solve [eexists; split; econstructor; eauto].
    apply IHtree_join1 in H5 as [mlyz [? ?]].
    apply IHtree_join2 in H8 as [mryz [? ?]].
    epose proof join_assoc o o' o'0 o'' o''0 H1 H9 as [moyz [? ?]].
    exists (LinCCAL.TMap.Node mlyz moyz mryz).
    split; constructor; auto.
    Unshelve. exact (@option_SA A trivial_Join trivial_SA).
  Defined.

  #[global] Program Instance tmap_unit : SeparationAlgebraUnit (LinCCAL.tmap A) tmap_SA :=
  {| ue := LinCCAL.TMap.Leaf _ |}.
  Next Obligation.
    constructor.
  Qed.
  Next Obligation.
    intros ? ? ?.
    inversion H; subst; auto.
  Qed.
End TMapSA.

Existing Instance tmap_Join.
Existing Instance tmap_SA.
Existing Instance tmap_unit.

Module Semantics.
  Import Reg.
  Import LinCCALBase.
  Import LTSSpec.
  Import Lang.

  Section Semantics.
    Context {E : Op.t}.
    Context {F : Op.t}.
    Context {VE : @LTS E}.
    Context {VF : @LTS F}.
    Context (M : ModuleImpl E F).

    Record ThreadState := {
      (* overlay operation in process *)
      ts_op : Sig.op F;
      (* continuation *)
      ts_prog : Prog E (Sig.ar ts_op);
      (* pending underlay opertion *)
      ts_pend : option (Sig.op E);
    }.

    Definition ThreadPoolState : Type := tmap ThreadState.

    Variant ts_step (f : Sig.op F) : ThreadEvent -> State VE -> ThreadState -> State VE -> ThreadState -> Prop :=
    | ts_inv t op k s1 s2
        (Hstep : Step VE (Build_ThreadEvent t (InvEv op)) s1 s2) :
        ts_step f (Build_ThreadEvent t (InvEv op))
          s1 (Build_ThreadState f (Vis op k) None)
          s2 (Build_ThreadState f (Vis op k) (Some op))
    | ts_res t op ret k s1 s2
        (Hstep : Step VE (Build_ThreadEvent t (ResEv op ret)) s1 s2) :
        ts_step f (Build_ThreadEvent t (ResEv op ret))
          s1 (Build_ThreadState f (Vis op k) (Some op))
          s2 (Build_ThreadState f (k ret) None).
    
    Variant ts_taustep : ThreadState -> ThreadState -> Prop :=
    | ts_tau f p b :
        ts_taustep
          (Build_ThreadState f (Tau p) b)
          (Build_ThreadState f p b).
    
    Variant ts_error (f : Sig.op F) : ThreadEvent -> State VE -> ThreadState -> Prop :=
    | ts_err t op s k
        (Herror : Error VE (Build_ThreadEvent t (InvEv op)) s):
        ts_error f (Build_ThreadEvent t (InvEv op)) s (Build_ThreadState f (Vis op k) None).

    Lemma ts_step_inversion f:
      forall ev σ f' p b σ' ts', ts_step f ev σ (Build_ThreadState f' p b) σ' ts' ->
      f = f' /\
      exists p' b', ts' = Build_ThreadState f p' b'.
    Proof.
      inversion 1; subst; split; auto.
      - dependent destruction H4.
        exists (Vis op k0), (Some op). auto.
      - dependent destruction H4. eexists; eauto.
    Qed.
      
    Variant ustep (ev : ThreadEvent) (s1 : State VE) (c1 : ThreadPoolState) (s2 : State VE) (c2 : ThreadPoolState) : Prop :=
    | UStep f
        (ts1 ts2 : ThreadState)
        (Hfind : TMap.find (te_tid ev) c1 = Some ts1)
        (Hstep : ts_step f ev s1 ts1 s2 ts2)
        (Hupd : c2 = TMap.add (te_tid ev) ts2 c1).

    Variant uerror (ev : ThreadEvent) (s1 : State VE) (c1 : ThreadPoolState) : Prop :=
    | UError f
        (ts : ThreadState)
        (Hfind : TMap.find (te_tid ev) c1 = Some ts)
        (Herror : ts_error f ev s1 ts).

    Variant taustep t (c1 : ThreadPoolState) (c2 : ThreadPoolState) : Prop :=
    | TauStep
        (ts1 ts2 : ThreadState)
        (Hfind : TMap.find t c1 = Some ts1)
        (Hstep : ts_taustep ts1 ts2)
        (Hupd : c2 = TMap.add t ts2 c1).

    Variant invstep (t : tid) (f : Sig.op F) (c1 c2 : ThreadPoolState) : Prop :=
    | InvStep
        (Hfind : TMap.find t c1 = None)
        (Hupd : c2 = TMap.add t (Build_ThreadState f (M f t) None) c1).

    Variant retstep (t : tid) (f : Sig.op F) (ret : Sig.ar f) (c1 c2 : ThreadPoolState) : Prop :=
    | RetStep
        (Hfind : TMap.find t c1 = Some (Build_ThreadState f (Ret ret) None))
        (Hupd : c2 = TMap.remove t c1).

    (* Variant estep (s1 : State VE) (c1 : ThreadPoolState) (s2 : State VE) (c2 : ThreadPoolState) : Prop :=
    | estep_ustep ev
        (Hstep : ustep ev s1 c1 s2 c2)
    | estep_inv t f
        (Hstep : invstep t f c1 c2)
    | estep_ret t f ret
        (Hstep : retstep t f ret c1 c2). *)

    Variant LinState : Type :=
    | ls_inv (f : Sig.op F)
    | ls_lini (f : Sig.op F)
    | ls_linr (f : Sig.op F) (ret : Sig.ar f).

    Variant Poss : Type :=
    | PossOk (s : State VF) (π : tmap LinState)
    | PossError.

    Variant poss_step : Poss -> Poss -> Prop :=
    | ps_inv t f s1 s2 π
        (Hstep : Step VF (Build_ThreadEvent t (InvEv f)) s1 s2)
        (Hlin : TMap.find t π = Some (ls_inv f)) :
        poss_step (PossOk s1 π) (PossOk s2 (TMap.add t (ls_lini f) π))
    | ps_ret t f ret s1 s2 π
        (Hstep : Step VF (Build_ThreadEvent t (ResEv f ret)) s1 s2)
        (Hlin : TMap.find t π = Some (ls_lini f)) :
        poss_step (PossOk s1 π) (PossOk s2 (TMap.add t (ls_linr f ret) π))
    | ps_error t f s π
        (Herror : Error VF (Build_ThreadEvent t (InvEv f)) s)
        (Hlin : TMap.find t π = Some (ls_inv f)) :
        poss_step (PossOk s π) PossError.
            
    Definition poss_steps := clos_refl_trans _ poss_step.
    Definition nonemp_poss_steps := clos_trans _ poss_step.
    
    Definition linstate_atomic_step t f r (π : tmap LinState) : tmap LinState :=
      TMap.add t (Semantics.ls_linr f r) (TMap.add t (Semantics.ls_lini f) π).

    (* Lemmas *)

    Lemma ustep_local_cont : forall t ev s1 c1 s2 c2 t',
      ustep (Build_ThreadEvent t ev) s1 c1 s2 c2 ->
      t <> t' -> TMap.find t' c1 = TMap.find t' c2.
    Proof.
      inversion 1; subst.
      intros. simpl.
      rewrite PositiveMap.gso; auto.
    Qed.

    Lemma taustep_local_cont : forall t c1 c2 t',
      taustep t c1 c2 ->
      t <> t' -> TMap.find t' c1 = TMap.find t' c2.
    Proof.
      inversion 1; subst.
      intros. simpl.
      rewrite PositiveMap.gso; auto.
    Qed.

    Lemma ustep_local_determ : forall t ev s s' c1 c1' c2,
      ustep (Build_ThreadEvent t ev) s c1 s' c1' ->
      TMap.find t c1 = TMap.find t c2 ->
      exists c2',
      ustep (Build_ThreadEvent t ev) s c2 s' c2' /\
      TMap.find t c1' = TMap.find t c2'.
    Proof.
      inversion 1; subst.
      intros.
      exists (TMap.add t0 ts2 c2).
      simpl in *.
      split; auto.
      - econstructor; simpl; eauto.
        rewrite <- H0; auto.
      - do 2 rewrite PositiveMap.gss; auto.
    Qed.

    Lemma taustep_local_determ : forall t c1 c1' c2,
      taustep t c1 c1' ->
      TMap.find t c1 = TMap.find t c2 ->
      exists c2',
      taustep t c2 c2' /\
      TMap.find t c1' = TMap.find t c2'.
    Proof.
      inversion 1; subst.
      intros.
      exists (TMap.add t0 ts2 c2).
      split; auto.
      - econstructor; simpl; eauto.
        rewrite <- H0; auto.
      - do 2 rewrite PositiveMap.gss; auto.
    Qed.

    Lemma uerror_local_determ : forall t ev s c c',
      uerror (Build_ThreadEvent t ev) s c ->
      TMap.find t c = TMap.find t c' ->
      uerror (Build_ThreadEvent t ev) s c'.
    Proof.
      intros.
      inversion H; subst.
      econstructor; eauto.
      simpl in *. rewrite <- H0. auto.
    Qed.

    Lemma invstep_local_cont : forall t f c1 c2 t',
      invstep t f c1 c2 ->
      t <> t' -> TMap.find t' c1 = TMap.find t' c2.
    Proof.
      inversion 1; subst.
      intros. simpl.
      rewrite PositiveMap.gso; auto.
    Qed.

    Lemma invstep_local_determ : forall t f c1 c1' c2,
      invstep t f c1 c1' ->
      TMap.find t c1 = TMap.find t c2 ->
      exists c2',
      invstep t f c2 c2' /\
      TMap.find t c1' = TMap.find t c2'.
    Proof.
      inversion 1; subst.
      intros.
      exists (TMap.add t0 (Build_ThreadState f (M f t0) None) c2).
      simpl in *.
      split; auto.
      - econstructor; simpl; eauto.
        rewrite <- H0; auto.
      - do 2 rewrite PositiveMap.gss; auto.
    Qed.

    Lemma retstep_local_cont : forall t f ret c1 c2 t',
      retstep t f ret c1 c2 ->
      t <> t' -> TMap.find t' c1 = TMap.find t' c2.
    Proof.
      inversion 1; subst.
      intros.
      rewrite PositiveMap.gro; auto.
    Qed.

    Lemma retstep_local_determ : forall t f ret c1 c1' c2,
      retstep t f ret c1 c1' ->
      TMap.find t c1 = TMap.find t c2 ->
      exists c2',
      retstep t f ret c2 c2' /\
      TMap.find t c1' = TMap.find t c2'.
    Proof.
      inversion 1; subst.
      intros.
      exists (TMap.remove t0 c2).
      simpl in *.
      split; auto.
      - econstructor; simpl; eauto.
        rewrite <- H0; auto.
      - do 2 rewrite PositiveMap.grs; auto.
    Qed.
    
    Lemma poss_step_nondec : forall t ρ ρ' π π' ls,
      poss_step (PossOk ρ π) (PossOk ρ' π') ->
      TMap.find t π = Some ls ->
      exists ls, TMap.find t π' = Some ls.
    Proof.
      inversion 1; subst;
      destruct (Pos.eq_dec t0 t1); subst;
      intros.
      - rewrite PositiveMap.gss; eauto.
      - rewrite PositiveMap.gso; eauto.
      - rewrite PositiveMap.gss; eauto.
      - rewrite PositiveMap.gso; eauto.
    Qed.

    Lemma poss_steps_nondec : forall t ρ ρ' π π' ls,
      poss_steps (PossOk ρ π) (PossOk ρ' π') ->
      TMap.find t π = Some ls ->
      exists ls, TMap.find t π' = Some ls.
    Proof.
      intros ? ? ? ? ? ? H.
      revert ls.
      unfold poss_steps in H.
      apply clos_rt_rtn1_iff in H.
      remember (PossOk ρ π) as s1.
      remember (PossOk ρ' π') as s2.
      revert  ρ ρ' π π' Heqs1 Heqs2.
      induction H; intros; subst.
      - inversion Heqs2; subst. eauto.
      - destruct y.
        eapply (IHclos_refl_trans_n1 _ _ _ _ eq_refl eq_refl) in H1 as [? ?]; eauto.
        eapply poss_step_nondec in H1; eauto.
        inversion H.
    Qed.

  End Semantics.

  Section AbstractConfig.
    Context {F : Op.t} {VF : @LTS F}.

    
    Definition DomExact {A} (π1 π2 : tmap A) : Prop :=
      forall t, TMap.find t π1 = None <-> TMap.find t π2 = None.
      
    Program Instance Equivalence_DomExact : Equivalence (@DomExact (@LinState F)).
    Next Obligation. constructor; auto. Defined.
    Next Obligation. constructor; apply H. Defined.
    Next Obligation. constructor; unfold DomExact in *.
      - rewrite H, H0. auto.
      - rewrite H, H0. auto.
    Defined.
    
    Definition AbstractConfigProp : Type := State VF -> tmap (@LinState F) -> Prop.

    Record AbstractConfig : Type := mkAC {
      ac_prop :> State VF -> tmap (@LinState F) -> Prop;
      ac_nonempty : exists ρ π, ac_prop ρ π;
      ac_domexact : forall ρ1 π1 ρ2 π2, ac_prop ρ1 π1 -> ac_prop ρ2 π2 ->
                      DomExact π1 π2
    }.

    Definition Δ_domexact (Δ1 Δ2 : AbstractConfigProp) : Prop :=
      forall ρ1 π1 ρ2 π2, Δ1 ρ1 π1 -> Δ2 ρ2 π2 -> DomExact π1 π2.

    Definition ac_equiv (Δ1 Δ2 : AbstractConfig) : Prop :=
      forall ρ π, Δ1 ρ π <-> Δ2 ρ π.

    Program Instance Equivalence_ACEquiv : Equivalence ac_equiv.
    Next Obligation. constructor; auto. Defined.
    Next Obligation. constructor; apply H. Defined.
    Next Obligation.
      constructor.
      - unfold ac_equiv in *. intros. apply H0, H. auto.
      - unfold ac_equiv in *. intros. apply H, H0. auto.
    Defined.

    Definition ac_subset (Δ1 Δ2 : AbstractConfig) : Prop :=
      forall ρ π, Δ1 ρ π -> Δ2 ρ π.

    Definition ac_empty_prop : AbstractConfigProp :=
      fun _ _ => False.

    Variant ac_singleton_prop ρ π : AbstractConfigProp :=
    | ACSingle : ac_singleton_prop ρ π ρ π.

    Program Definition ac_singleton ρ π : AbstractConfig :=
      {| ac_prop := ac_singleton_prop ρ π |}.
    Next Obligation. exists ρ, π. constructor. Qed.
    Next Obligation.
      inversion H; inversion H0; subst.
      intro. reflexivity.
    Qed.

    Variant ac_union_prop (Δ1 Δ2 : AbstractConfigProp) : AbstractConfigProp :=
    | ACUnionLeft ρ π: Δ1 ρ π -> ac_union_prop Δ1 Δ2 ρ π
    | ACUnionRight ρ π: Δ2 ρ π -> ac_union_prop Δ1 Δ2 ρ π.
    Program Definition ac_union (Δ1 Δ2 : AbstractConfig) {Hdomexact: Δ_domexact Δ1 Δ2} : AbstractConfig :=
      {| ac_prop := ac_union_prop Δ1 Δ2 |}.
    Next Obligation.
      pose proof ac_nonempty Δ1 as [ρ [π ?]].
      exists ρ, π.
      apply ACUnionLeft; auto.
    Qed.
    Next Obligation.
     (* eapply ac_domexact Δ1. *)
      inversion H; inversion H0; subst.
      - eapply (ac_domexact Δ1); eauto.
      - eapply Hdomexact; eauto.
      - symmetry. eapply Hdomexact; eauto.
      - eapply (ac_domexact Δ2); eauto.
    Defined.

    Variant ac_intersect_prop (Δ1 Δ2 : AbstractConfigProp) : AbstractConfigProp :=
    | ACIntersect ρ π: Δ1 ρ π -> Δ2 ρ π -> ac_intersect_prop Δ1 Δ2 ρ π.

    Variant ac_inv_prop (Δ : AbstractConfigProp) t f : AbstractConfigProp :=
    | ACInv ρ π (Hposs : Δ ρ π) :
        ac_inv_prop Δ t f ρ (TMap.add t (ls_inv f) π).
      
    Program Definition ac_inv (Δ : AbstractConfig) t f : AbstractConfig :=
      {| ac_prop := ac_inv_prop Δ t f |}.
    Next Obligation.
      destruct (ac_nonempty Δ) as [ρ [π H]].
      exists ρ, (TMap.add t0 (ls_inv f) π). constructor. auto.
    Qed.
    Next Obligation.
      intros ?.
      inversion H; inversion H0; subst.
      destruct (Pos.eq_dec t1 t0); subst.
      - do 2 rewrite PositiveMap.gss. split; discriminate.
      - do 2 (rewrite PositiveMap.gso; auto).
        rewrite (ac_domexact Δ _ _ _ _ Hposs Hposs0 t1).
        reflexivity.
    Qed.

    Variant ac_res_prop (Δ : AbstractConfigProp) t : AbstractConfigProp :=
    | ACRes ρ π (Hposs : Δ ρ π):
        ac_res_prop Δ t ρ (TMap.remove t π).
    
    Program Definition ac_res (Δ : AbstractConfig) t : AbstractConfig :=
      {| ac_prop := ac_res_prop Δ t |}.
    Next Obligation.
      destruct (ac_nonempty Δ) as [ρ [π H]].
      exists ρ, (TMap.remove t0 π). constructor. auto.
    Qed.
    Next Obligation.
      intros ?.
      inversion H; inversion H0; subst.
      destruct (Pos.eq_dec t1 t0); subst.
      - do 2 rewrite PositiveMap.grs. split; auto.
      - do 2 (rewrite PositiveMap.gro; auto).
        rewrite (ac_domexact Δ _ _ _ _ Hposs Hposs0 t1).
        reflexivity.
    Qed.

    Variant ac_steps_prop (Δ : AbstractConfigProp) : AbstractConfigProp :=
    | ACSteps ρ π ρ' π' (Hposs : Δ ρ π)
        (Hpstep : poss_steps (PossOk ρ π) (PossOk ρ' π')):
        ac_steps_prop Δ ρ' π'.

    Lemma poss_step_domexact : forall ρ π ρ' π',
      @poss_step _ VF (PossOk ρ π) (PossOk ρ' π') ->
      DomExact π π'.
    Proof.
      inversion 1; subst; intro;
      (destruct (Pos.eq_dec t1 t0); subst;
        [rewrite PositiveMap.gss
        | rewrite PositiveMap.gso]; auto;
        split; try congruence).
    Qed.

    Lemma poss_steps_domexact : forall ρ π ρ' π',
      @poss_steps _ VF (PossOk ρ π) (PossOk ρ' π') ->
      DomExact π π'.
    Proof.
      intros.
      remember (PossOk ρ π) as p.
      remember (PossOk ρ' π') as p'.
      revert ρ' π' Heqp'.
      apply clos_rt_rtn1 in H.
      induction H; intros; subst.
      - inversion Heqp'; subst. reflexivity.
      - inversion H; subst;
        specialize (IHclos_refl_trans_n1 _ _ eq_refl);
        (eapply Equivalence_Transitive; eauto;
          intro;
          destruct (Pos.eq_dec t1 t0); subst;
          [rewrite PositiveMap.gss
          | rewrite PositiveMap.gso]; auto;
          split; intros; try congruence).
    Qed.

    Program Definition ac_steps (Δ : AbstractConfig) : AbstractConfig :=
      {| ac_prop := ac_steps_prop Δ |}.
    Next Obligation.
      destruct (ac_nonempty Δ) as [ρ [π H]].
      exists ρ, π. econstructor; eauto. apply rt_refl.
    Qed.
    Next Obligation.
      inversion H; inversion H0; subst. clear H H0.
      apply poss_steps_domexact in Hpstep, Hpstep0.
      pose proof (ac_domexact _ _ _ _ _ Hposs Hposs0).
      do 2 (eapply Equivalence_Transitive; eauto).
      symmetry. auto.
    Qed.

    Lemma ac_steps_refl : forall Δ, ac_subset Δ (ac_steps Δ).
    Proof.
      intros. intros ? ? ?.
      econstructor; eauto.
      apply rt_refl.
    Qed.

    Variant ac_steps_π_prop (Δ : AbstractConfigProp) t ls1 ls2 ρf
      (Hpstep : forall ρ π, Δ ρ π -> poss_steps (PossOk ρ π) (PossOk (ρf ρ) (TMap.add t ls2 (TMap.add t ls1 π)))) : AbstractConfigProp :=
    | ACSteps_π ρ π (Hposs : Δ ρ π):
        ac_steps_π_prop Δ t ls1 ls2 ρf Hpstep (ρf ρ) (TMap.add t ls2 (TMap.add t ls1 π)).
    
    Program Definition ac_steps_π (Δ : AbstractConfig) t ls1 ls2 ρf Hpstep : AbstractConfig :=
      {| ac_prop := ac_steps_π_prop Δ t ls1 ls2 ρf Hpstep |}.
    Next Obligation.
      pose proof ac_nonempty Δ as [? [? ?]].
      do 2 eexists. econstructor; eauto.
    Qed.
    Next Obligation.
      inversion H; inversion H0; subst.
      pose proof (Hpstep _ _ Hposs).
      pose proof (Hpstep _ _ Hposs0).
      eapply poss_steps_domexact in H1, H2.
      pose proof ac_domexact _ _ _ _ _ Hposs Hposs0.
      do 2 (eapply Equivalence_Transitive; eauto).
      symmetry. auto.
    Defined.

    Variant ac_branch_prop (Δ : AbstractConfigProp) ρ π ρ' π' : AbstractConfigProp :=
    | ACBranch
      (Hposs : Δ ρ π)
      (Hpstep : poss_steps (PossOk ρ π) (PossOk ρ' π')):
      ac_branch_prop Δ ρ π ρ' π' ρ' π'.
    
      Program Definition ac_branch (Δ : AbstractConfig) ρ π ρ' π' 
        (Hposs : Δ ρ π)
        (Hpstep : poss_steps (PossOk ρ π) (PossOk ρ' π')): AbstractConfig :=
        {| ac_prop := ac_branch_prop Δ ρ π ρ' π' |}.
      Next Obligation.
        exists ρ', π'.
        econstructor; eauto.
      Qed.
      Next Obligation.
        inversion H; inversion H0; subst.
        reflexivity.
      Defined.

    Lemma ac_branch_subset_steps : forall (Δ : AbstractConfig) ρ π ρ' π' 
        Hposs Hpstep,
      ac_subset (ac_branch Δ ρ π ρ' π' Hposs Hpstep) (ac_steps Δ).
    Proof.
      intros. intros ? ? ?.
      inversion H; subst.
      econstructor; eauto.
    Qed.

    Variant ac_trylin_choice (Δ : AbstractConfig) : (option AbstractConfig) -> Prop :=
    | ACTrylinContinue Δ' :
      ac_subset Δ' (ac_steps Δ) ->
      ac_trylin_choice Δ (Some Δ')
    | ACTrylinFinish :
      ac_trylin_choice Δ None.

    Program Definition ac_trylin (Δ : AbstractConfig) ρ π ρ' π' 
        Hposs Hpstep
        (oΔ' : option AbstractConfig)
        (Htrylinchoice : ac_trylin_choice Δ oΔ') : AbstractConfig :=
      {| ac_prop := match oΔ' with
                    | Some Δ' => ac_union_prop Δ' (ac_branch Δ ρ π ρ' π' Hposs Hpstep)
                    | None => ac_branch Δ ρ π ρ' π' Hposs Hpstep
                    end |}.
    Next Obligation.
      destruct oΔ'.
      - exists ρ', π'. right. econstructor; eauto.
      - exists ρ', π'. econstructor; eauto.
    Qed.
    Next Obligation.
      inversion Htrylinchoice; subst; simpl in *.
      - inversion H; inversion H0; subst.
        + eapply (ac_domexact Δ'); eauto.
        + apply H1 in H2.
          inversion H2; inversion H5; subst.
          apply poss_steps_domexact in Hpstep0, Hpstep1.
          eapply (ac_domexact Δ) in Hposs0; eauto.
          etransitivity; eauto.
          symmetry. etransitivity; eauto.
        + apply H1 in H5.
          inversion H2; inversion H5; subst.
          apply poss_steps_domexact in Hpstep0, Hpstep1.
          eapply (ac_domexact Δ) in Hposs1; [|exact Hposs0].
          etransitivity; eauto.
          etransitivity; eauto. symmetry; auto.
        + eapply (ac_domexact (ac_branch Δ ρ π ρ' π' Hposs Hpstep)); eauto.
      - eapply (ac_domexact (ac_branch Δ ρ π ρ' π' Hposs Hpstep)); eauto.
    Defined.

    Lemma ac_trylin_single : forall Δ ρ π ρ' π' Hposs Hstep Hnext,
      ac_equiv (ac_trylin Δ ρ π ρ' π' Hposs Hstep None Hnext) (ac_singleton ρ' π').
    Proof.
      intros. split; inversion 1; subst; try constructor; eauto.
    Qed.

    Lemma ac_trylin_subset_steps (Δ : AbstractConfig) ρ π ρ' π'
        Hposs Hpstep
        (oΔ' : option AbstractConfig)
        Htrylinchoice :
      ac_subset (ac_trylin Δ ρ π ρ' π' Hposs Hpstep oΔ' Htrylinchoice) (ac_steps Δ).
    Proof.
      intros.
      intros ? ? ?.
      inversion Htrylinchoice; subst; simpl in *.
      - inversion H; subst.
        + apply H0; auto.
        + apply ac_branch_subset_steps in H1; auto.
      - apply ac_branch_subset_steps in H; auto.
    Qed.

    Section ACSA.
      Context `{FJ : Join (State VF)} {FSA : SeparationAlgebra (State VF)} {Funit : SeparationAlgebraUnit (State VF) FSA}.

      (* Record ac_join (ac1 ac2 ac3 : AbstractConfig) : Prop :=
      {
        ACJoin: forall ρ1 ρ2 π1 π2, ac1 ρ1 π1 -> ac2 ρ2 π2 ->
            exists ρ π, ac3 ρ π /\ join ρ1 ρ2 ρ /\ @join _ tmap_Join π1 π2 π;
        ACSplit: forall ρ π, ac3 ρ π -> exists ρ1 ρ2 π1 π2, ac1 ρ1 π1 /\ ac2 ρ2 π2
                                /\ join ρ1 ρ2 ρ /\ @join _ tmap_Join π1 π2 π
      }.
      Instance ac_Join : Join AbstractConfig := ac_join.
      Program Instance : SeparationAlgebra AbstractConfig.
      Next Obligation.
        inversion H.
        constructor; intros.
        - specialize (ACJoin0 _ _ _ _ H1 H0) as [? [? [? [? ?]]]].
          apply join_comm in H3.
          apply (@join_comm _ _ tmap_SA) in H4. eauto.
        - apply ACSplit0 in H0 as [? [? [? [? [? [? [? ?]]]]]]].
          apply join_comm in H2.
          apply (@join_comm _ _ tmap_SA) in H3.
          do 4 eexists; eauto.
      Qed.
      Next Obligation.
        inversion H; inversion H0.
        eauto. *)

      (* Definition ac_disjoint (ac1 ac2 : AbstractConfigProp) : Prop :=
        forall ρ1 ρ2 π1 π2, ac1 ρ1 π1 -> ac2 ρ2 π2 ->
          exists ρ π, join ρ1 ρ2 ρ /\ @join _ tmap_Join π1 π2 π. *)

      Definition ac_disjoint (ac1 ac2 : AbstractConfigProp) : Prop :=
        exists ρ1 ρ2 ρ π1 π2 π, ac1 ρ1 π1 /\ ac2 ρ2 π2 /\
          join ρ1 ρ2 ρ /\ @join _ tmap_Join π1 π2 π.

      Ltac destruct_disjoint H := destruct H as (?ρ1&?ρ2&?ρ&?π1&?π2&?π&?&?&?&?).
      
      Lemma ac_disjoint_symm: forall ac1 ac2,
        ac_disjoint ac1 ac2 -> ac_disjoint ac2 ac1.
      Proof.
        intros.
        destruct_disjoint H.
        apply join_comm in H1. apply (@join_comm _ _ tmap_SA) in H2.
        do 6 eexists; eauto.
      Qed.

      Variant ac_join_prop (ac1 ac2 : AbstractConfigProp) : AbstractConfigProp :=
      | ACJoinProp : forall ρ1 ρ2 π1 π2 ρ π,
          ac1 ρ1 π1 -> ac2 ρ2 π2 ->
          join ρ1 ρ2 ρ -> @join _ tmap_Join π1 π2 π ->
          ac_join_prop ac1 ac2 ρ π.
      Program Definition ac_join (ac1 ac2 : AbstractConfig)
        (Hdisjoint : ac_disjoint ac1 ac2) : AbstractConfig :=
        {| ac_prop := ac_join_prop ac1 ac2 |}.
      Next Obligation.
        destruct_disjoint Hdisjoint.
        do 2 eexists; econstructor; eauto.
      Qed.
      Next Obligation.
        inversion H; inversion H0; subst.
        pose proof ac_domexact _ _ _ _ _ H1 H7.
        pose proof ac_domexact _ _ _ _ _ H2 H8.
        clear dependent ρ0. clear dependent ρ1.
        clear dependent ρ2. clear dependent ρ3.
        clear dependent ρ4. clear dependent ρ5.
        intros ?. specialize (H5 t0). specialize (H6 t0).
        eapply tree_join_none with (a:=t0) in H4, H10.
        tauto.
      Qed.

      Lemma ac_join_comm: forall ac1 ac2 Hd1 Hd2 ρ π,
        ac_join ac1 ac2 Hd1 ρ π -> ac_join ac2 ac1 Hd2 ρ π.
      Proof.
        intros. inversion H; subst.
        econstructor; eauto.
        apply join_comm; auto.
      Qed.

      Lemma ac_disjoint_distr: forall 
        (mx my mz mxy mxyz: AbstractConfig)
        (x: ac_disjoint mx my)
        (H1: ac_equiv mxy (ac_join mx my x))
        (x0: ac_disjoint mxy mz)
        (H2: ac_equiv mxyz (ac_join mxy mz x0)),
        ac_disjoint my mz.
      Proof.
        intros.
        (* pose proof x.
        destruct_disjoint H. *)
        pose proof x0.
        destruct_disjoint H.
        apply H1 in H.
        inversion H; subst.
        pose proof join_assoc _ _ _ _ _ H7 H3 as [? [? ?]].
        pose proof @join_assoc _ _ tmap_SA _ _ _ _ _ H8 H4 as [? [? ?]].
        do 6 eexists; eauto.
      Qed.

      #[global] Instance ac_Join : Join AbstractConfig :=
        fun ac1 ac2 ac => 
          exists (Hdisjoint : ac_disjoint ac1 ac2),
          ac_equiv ac (ac_join ac1 ac2 Hdisjoint).

      #[global] Program Instance ac_SA : SeparationAlgebra AbstractConfig.
      Next Obligation.
        inversion H.
        pose proof x.
        apply ac_disjoint_symm in H1.
        exists H1.
        unfold ac_equiv in *.
        split; intros.
        - apply H0 in H2. eapply ac_join_comm; eauto.
        - apply H0. eapply ac_join_comm; eauto.
      Qed.
      Next Obligation.
        inversion H. inversion H0.
        clear H H0.

        assert (ac_disjoint my mz).
        {
          eapply ac_disjoint_distr; eauto.
        }
        assert (ac_disjoint mx (ac_join my mz H)).
        {
          pose proof x0.
          destruct_disjoint H0.
          apply H1 in H0.
          inversion H0; subst.
          pose proof join_assoc _ _ _ _ _ H8 H4 as [? [? ?]].
          pose proof @join_assoc _ _ tmap_SA _ _ _ _ _ H9 H5 as [? [? ?]].
          do 6 eexists; split; eauto. split; eauto.
          econstructor; eauto.
        }
        exists (ac_join my mz H).
        split.
        - exists H. reflexivity.
        - exists H0.
          etransitivity; eauto.
          split; intros.
          + inversion H3; subst.
            apply H1 in H4.
            inversion H4; subst.
            pose proof join_assoc _ _ _ _ _ H10 H6 as [? [? ?]].
            pose proof @join_assoc _ _ tmap_SA _ _ _ _ _ H11 H7 as [? [? ?]].
            econstructor; eauto.
            econstructor; eauto.
          + inversion H3; subst.
            inversion H5; subst.
            apply join_comm in H6, H10. apply (@join_comm _ _ tmap_SA) in H7, H11.
            pose proof join_assoc _ _ _ _ _ H10 H6 as [? [? ?]].
            pose proof @join_assoc _ _ tmap_SA _ _ _ _ _ H11 H7 as [? [? ?]].
            apply join_comm in H13, H12. apply (@join_comm _ _ tmap_SA) in H15, H14.
            econstructor; eauto.
            apply H1. econstructor; eauto.
      Defined.

      Lemma ac_unit_join : forall n : AbstractConfig,
        join n (ac_singleton ue (LinCCAL.TMap.Leaf LinState)) n.
      Proof.
        econstructor. Unshelve.
        split; intros.
        - econstructor; eauto; try constructor.
        - inversion H; subst.
          inversion H1; subst.
          apply join_comm, unit_spec in H2; subst.
          apply (@join_comm _ _ tmap_SA), (@unit_spec _ _ _ tmap_unit) in H3; subst.
          auto.
        - pose proof ac_nonempty n as [? [? ?]].
          do 6 eexists.
          split; eauto.
          split; constructor.
          + apply unit_join.
          + apply (@unit_join _ _ _ tmap_unit).
      Qed.

      #[global] Program Instance ac_unit : SeparationAlgebraUnit AbstractConfig ac_SA :=
        {| ue := ac_singleton ue (LinCCAL.TMap.Leaf _) |}.
      Next Obligation.
        apply ac_unit_join.
      Qed.
      Next Obligation.
        intros ? ? ?.
        inversion H; subst.
        destruct n. destruct n'.
        simpl in *.
        assert (ac_prop0 = ac_prop1).
        {
          apply functional_extensionality_dep; intros ρ.
          apply functional_extensionality_dep; intros π.
          apply propositional_extensionality.
          unfold ac_equiv in H0. simpl in H0.
          rewrite H0.
          split; intros.
          - econstructor; eauto.
            + constructor.
            + apply (@join_comm _ _ tmap_SA), (@unit_join _ _ tmap_SA tmap_unit π).
        - inversion H1; subst.
            inversion H2; subst.
            apply unit_spec in H4; subst.
            apply (@unit_spec _ _ _ tmap_unit) in H5; subst; auto.
        }
        subst.
        f_equal; apply proof_irrelevance.
      Defined.
    End ACSA.

  End AbstractConfig.

  Arguments AbstractConfigProp {F} VF.
  Arguments AbstractConfig {F} VF.

  #[global] Existing Instance Equivalence_DomExact.
  #[global] Existing Instance Equivalence_ACEquiv.

  Delimit Scope ac_scope with AbstractConfig.
  Bind Scope ac_scope with AbstractConfig.

  Notation "[( ρ , π )]" := (ac_singleton ρ π) (at level 10) : ac_scope.
  Notation "Δ1 ⊆ Δ2" := (ac_subset Δ1 Δ2) (at level 70) : ac_scope.
  Notation "Δ1 ≡ Δ2" := (ac_equiv Δ1 Δ2) (at level 70) : ac_scope.
  Notation "Δ1 ∪ Δ2" := (ac_union Δ1 Δ2) (at level 50) : ac_scope.
  Notation "Δ1 ∩ Δ2" := (ac_intersect_prop Δ1 Δ2) (at level 40) : ac_scope.
  
  Delimit Scope poss_scope with Poss.
  Bind Scope poss_scope with Poss.
  
  Notation "( ρ , π )" := (PossOk ρ π) : poss_scope.

End Semantics.
