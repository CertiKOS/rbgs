Require Import Coq.Program.Equality.
Require Import Classical.
Require Import models.EffectSignatures.
Require Import models.LinCCAL.

(* A small LinCCAL case study: an atomic boolean flip protected by a lock and
   register, built using existing components from LinCCALExample. *)
Module LinCCALFlip.
  Import LinCCAL.
  Import LinCCALExample.
  Module Sig := EffectSignatures.Sig.
  Import (coercions, canonicals, notations) Sig.
  Import (canonicals) Sig.Plus.
  Import (notations) LinCCAL.
  Open Scope term_scope.

  Variant Eflip_op :=
    | flip.

  Canonical Structure Eflip :=
    {|
      Sig.op := Eflip_op;
      Sig.ar _ := bool;
    |}.

  Definition Σflip : LinCCAL.Spec.lts Eflip bool :=
    fun b _ 'flip => LinCCAL.Spec.ret (m:=flip) b (negb b).

  Definition Lflip : LinCCAL.t :=
    {| LinCCAL.li_spec := LinCCAL.Spec.gen Σflip false |}.

  Definition flip_impl :
    Sig.term (LinCCAL.li_sig (LinCCALExample.Llock * LinCCALExample.Lreg false)%obj) bool :=
    inl LinCCALExample.acq >= _ =>
    inr LinCCALExample.get >= b =>
    inr (LinCCALExample.set (negb b)) >= _ =>
    inl LinCCALExample.rel >= _ =>
    Sig.var b.

  Variant flip_threadstate (i : LinCCAL.tid) h :
    bool -> option (LinCCAL.threadstate _ _) -> Prop :=
    | flip_rdy b :
      h <> Some i ->
      flip_threadstate i h b None
    | flip_acq b :
      h <> Some i ->
      flip_threadstate i h b (Some (LinCCAL.mkts flip flip_impl None))
    | flip_get b :
      h = Some i ->
      flip_threadstate i h b
        (Some (LinCCAL.mkts flip (inr LinCCALExample.get >= b =>
                                     inr (LinCCALExample.set (negb b)) >= _ =>
                                     inl LinCCALExample.rel >= _ =>
                                     Sig.var b) None))
    | flip_set b :
      h = Some i ->
      flip_threadstate i h b
        (Some (LinCCAL.mkts flip (inr (LinCCALExample.set (negb b)) >= _ =>
                                     inl LinCCALExample.rel >= _ =>
                                     Sig.var b) None))
    | flip_rel b :
      h = Some i ->
      flip_threadstate i h (negb b)
        (Some (LinCCAL.mkts flip (inl LinCCALExample.rel >= _ =>
                                     Sig.var b) (Some b)))
    | flip_ret b b' :
      h <> Some i ->
      flip_threadstate i h b'
        (Some (LinCCAL.mkts flip (Sig.var b) (Some b))).

  Variant flip_state : _ -> Prop :=
    flip_state_intro h b s :
      (forall i, flip_threadstate i h b (LinCCAL.TMap.find i s)) ->
      flip_state (LinCCAL.mkst (LinCCAL.Spec.gen Σflip b)
                               s
                               (LinCCAL.Spec.gen Σlock h *
                                LinCCAL.Spec.gen (Σreg _) b)).

  Lemma flip_threadstate_convert i h h' b b' s :
    flip_threadstate i h b s ->
    h <> Some i ->
    h' <> Some i ->
    flip_threadstate i h' b' s.
  Proof.
    destruct 1; intros; try congruence; constructor; auto.
  Qed.

  Program Definition Mflip :
    LinCCAL.m (LinCCALExample.Llock * LinCCALExample.Lreg false) Lflip :=
    {| LinCCAL.li_impl 'flip := flip_impl |}.
  Next Obligation.
    eapply LinCCAL.correctness_invariant_sound with (P := flip_state).
    - split.
      + intros _ [h b s Hs] _ i q r R Hsi. cbn in *.
        specialize (Hs i).
        dependent destruction Hs; unfold flip_impl in *; try congruence.
        rewrite Hsi in x. dependent destruction x. reflexivity.
      + intros _ [h b s Hs] _ i q m k R Hsi. cbn in Hsi |- *.
        specialize (Hs i). cbn in Hs. rewrite Hsi in Hs.
        dependent destruction Hs; cbn; try congruence.
        * destruct h; cbn; try congruence.
          destruct LinCCAL.TMap.E.eq_dec; congruence.
        * destruct LinCCAL.TMap.E.eq_dec; congruence.
      + intros _ [h b s Hs] _ [t Ht]. cbn in *.
        destruct h as [i | ].
        * exists i; cbn. specialize (Hs i). clear Ht.
          dependent destruction Hs;
            rewrite <- x; cbn;
            try destruct LinCCAL.TMap.E.eq_dec;
            try congruence; eauto.
        * exists t; cbn. specialize (Hs t).
          destruct LinCCAL.TMap.find as [st | ]; try tauto.
          dependent destruction Hs; cbn; eauto.
      + intros _ [h b s Hs] _ s' Hs'.
        dependent destruction Hs'.
        * destruct q.
          pose proof (Hs t0) as Hst. rewrite H in Hst. dependent destruction Hst.
          apply LinCCAL.reachable_base. constructor.
          intro i. destruct (classic (i = t0)); subst.
          -- rewrite LinCCAL.TMap.gss. constructor; auto.
          -- rewrite LinCCAL.TMap.gso; auto.
        * destruct q.
          pose proof (Hs t0) as Hst. dependent destruction Hst; try congruence.
          -- rewrite H in x. dependent destruction x.
             cbn in H0.
             destruct h; try discriminate. cbn in H0.
             destruct LinCCAL.TMap.E.eq_dec; try discriminate.
             cbn in H0. dependent destruction H0.
             apply LinCCAL.reachable_base. constructor.
             intros i. destruct (classic (i = t0)); subst.
             ++ rewrite LinCCAL.TMap.gss. constructor. auto.
             ++ rewrite LinCCAL.TMap.gso; auto.
                eapply flip_threadstate_convert; eauto; congruence.
          -- rewrite H in x. dependent destruction x.
             apply LinCCAL.reachable_base. constructor.
             intros i. destruct (classic (i = t0)); subst.
             ++ rewrite LinCCAL.TMap.gss. constructor. auto.
             ++ rewrite LinCCAL.TMap.gso; auto.
          -- rewrite H in x. dependent destruction x.
             eapply LinCCAL.reachable_step.
             2: {
               eapply (LinCCAL.lcommit t0 flip b); eauto.
               ** rewrite LinCCAL.TMap.gss. reflexivity.
               ** cbn. reflexivity.
             }
             apply LinCCAL.reachable_base. constructor.
             intros i. destruct (classic (i = t0)); subst.
             ++ rewrite LinCCAL.TMap.gss. constructor. auto.
             ++ rewrite !LinCCAL.TMap.gso; auto.
                eapply flip_threadstate_convert; eauto; congruence.
          -- rewrite H in x. dependent destruction x.
             cbn in H0.
             destruct LinCCAL.TMap.E.eq_dec; cbn in H0; try congruence.
             dependent destruction H0.
             apply LinCCAL.reachable_base. constructor.
             intros i. destruct (classic (i = t0)); subst.
             ++ rewrite LinCCAL.TMap.gss. constructor. congruence.
             ++ rewrite !LinCCAL.TMap.gso; auto.
                eapply flip_threadstate_convert; eauto; congruence.
        * destruct q.
          pose proof (Hs t0) as Hst. rewrite H in Hst. dependent destruction Hst.
          apply LinCCAL.reachable_base. constructor.
          intro i. destruct (classic (i = t0)); subst.
          -- rewrite LinCCAL.TMap.grs. constructor; auto.
          -- rewrite LinCCAL.TMap.gro; auto.
    - constructor.
      intro i.
      rewrite LinCCAL.TMap.gempty.
      constructor.
      congruence.
  Qed.

End LinCCALFlip.
