Require Import FMapPositive.
Require Import Relation_Operators Operators_Properties.
Require Import Coq.PArith.PArith.
Require Import Coq.Program.Equality.

Require Import coqrel.LogicalRelations.
Require Import models.EffectSignatures.
Require Import LinCCAL.
Require Import LTS.
Require Import Lang.


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
        (Hupd : c2 = TMap.add t (Build_ThreadState f (M f) None) c1).

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
      exists (TMap.add t0 (Build_ThreadState f (M f) None) c2).
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

  Notation "( ρ , π )" := (PossOk ρ π).

End Semantics.
