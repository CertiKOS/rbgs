Require Import Classical.
Require Import FunctionalExtensionality.
Require Import Program.Equality.
Require Import LogicalRelations.
Require Import Poset.
Require Import Lattice.
Require Import Downset.

Require Import IntStrat.

Lemma or_elim (P Q: Prop): (~ P -> Q) -> P \/ Q.
Proof. intros. destruct (classic P); firstorder. Qed.

Section IRC.
  Context {E1 E2 : esig}.
  Obligation Tactic := cbn.

  Inductive ircp {I: Type} {J : I -> Type} :=
  | ircp_allow (i: I) (m1: E1) (m2: E2)
  | ircp_forbid (i: I) (m1: E1) (m2: E2) (j: J i) (n1: ar m1) (n2: ar m2)
  | ircp_cont (i: I) (m1: E1) (m2: E2) (j: J i) (n1: ar m1) (n2: ar m2) (k: ircp).

  Inductive ircp_ref {I J} : relation (@ircp I J) :=
    | ircp_allow_ref i m1 m2 :
        ircp_ref (ircp_allow i m1 m2) (ircp_allow i m1 m2)
    | ircp_allow_cont_ref i m1 m2 j n1 n2 k :
        ircp_ref (ircp_allow i m1 m2) (ircp_cont i m1 m2 j n1 n2 k)
    | ircp_allow_forbid_ref i m1 m2 j n1 n2 :
        ircp_ref (ircp_allow i m1 m2) (ircp_forbid i m1 m2 j n1 n2)
    | ircp_cont_ref i m1 m2 j n1 n2 k k' :
        ircp_ref k k' -> ircp_ref (ircp_cont i m1 m2 j n1 n2 k) (ircp_cont i m1 m2 j n1 n2 k')
    | ircp_cont_forbid_ref i m1 m2 j n1 n2 k :
        ircp_ref (ircp_cont i m1 m2 j n1 n2 k) (ircp_forbid i m1 m2 j n1 n2)
    | ircp_forbid_ref i m1 m2 j n1 n2 :
        ircp_ref (ircp_forbid i m1 m2 j n1 n2) (ircp_forbid i m1 m2 j n1 n2).

  Program Canonical Structure ircp_poset {I J} : poset :=
    {|
      poset_carrier := @ircp I J;
      ref := @ircp_ref I J;
    |}.
  Next Obligation.
    split.
    - intro w. induction w; constructor; auto.
    - intros x y z Hxy. revert z.
      induction Hxy; intros z Hyz;
        dependent destruction Hyz; constructor; auto.
  Qed.
  Next Obligation.
    intros ? p w1 w2 Hw12 Hw21.
    induction Hw12; dependent destruction Hw21; firstorder congruence.
  Qed.

  Definition irc I J := poset_carrier (downset (@ircp_poset I J)).

  Program Definition ircnext {I J} (i: I) q1 q2 (j: J i) r1 r2 (R : irc I J) : irc I J :=
    {| Downset.has w := Downset.has R (ircp_cont i q1 q2 j r1 r2 w) |}.
  Next Obligation.
    intros I J i j q1 q2 r1 r2 R s t Hst Hs.
    eapply Downset.closed; eauto.
    eapply ircp_cont_ref; auto.
  Qed.

  Record iconv :=
    {
      question_index: Type;
      answer_index : question_index -> Type;
      iconv_carrier: @irc question_index answer_index;
    }.

  Lemma conv_has_cont_allow {I J} iq q1 q2 ir r1 r2 k (R: irc I J) :
    Downset.has R (ircp_cont iq q1 q2 ir r1 r2 k) ->
    Downset.has R (ircp_allow iq q1 q2).
  Proof.
    apply Downset.closed. constructor.
  Qed.

End IRC.

Arguments ircp : clear implicits.
Arguments irc : clear implicits.
Arguments iconv : clear implicits.
Coercion iconv_carrier : iconv >-> irc.

Section REF.
  Context {E1 E2: esig}.

  Fixpoint irc_has {I1 J1 I2 J2} (R: irc E1 E2 I1 J1) (s: ircp E1 E2 I2 J2): Prop :=
    match s with
    | ircp_allow i2 m1 m2 => exists i1, Downset.has R (ircp_allow i1 m1 m2)
    | ircp_forbid i2 m1 m2 j2 n1 n2 => exists i1 j1, Downset.has R (ircp_forbid i1 m1 m2 j1 n1 n2)
    | ircp_cont i2 m1 m2 j2 n1 n2 k =>
        exists i1 j1, Downset.has R (ircp_forbid i1 m1 m2 j1 n1 n2) \/
                   irc_has (ircnext i1 m1 m2 j1 n1 n2 R) k
    end.

  Definition irc_ref {I1 J1 I2 J2} (R1: irc E1 E2 I1 J1) (R2: irc E1 E2 I2 J2): Prop :=
    forall p, Downset.has R1 p -> irc_has R2 p.

  Definition iconv_ref (R1 R2: iconv E1 E2): Prop := irc_ref R1 R2.
  Definition iconv_eqv (R1 R2: iconv E1 E2): Prop := irc_ref R1 R2 /\ irc_ref R2 R1.
End REF.

Section VCOMP.
  Context {E1 E2 E3: esig} {I1 I2: Type} {J1: I1 -> Type} {J2: I2 -> Type}.
  Obligation Tactic := cbn.
  Let I := (I1 * I2 * op E2)%type.
  Let J : I -> Type := fun '(i1, i2, m2) => (J1 i1 * J2 i2 * ar m2)%type.

  Fixpoint ivcomp_has (R: irc E1 E2 I1 J1) (S: irc E2 E3 I2 J2) (s: ircp E1 E3 I J) : Prop :=
    match s with
    | ircp_allow (i1, i2, m2) m1 m3 =>
        Downset.has R (ircp_allow i1 m1 m2) /\ Downset.has S (ircp_allow i2 m2 m3)
    | ircp_forbid (i1, i2, m2) m1 m3 (j1, j2, n2) n1 n3 =>
        Downset.has R (ircp_allow i1 m1 m2) /\ Downset.has S (ircp_allow i2 m2 m3) /\
          (Downset.has R (ircp_forbid i1 m1 m2 j1 n1 n2) \/
             Downset.has S (ircp_forbid i2 m2 m3 j2 n2 n3))
    | ircp_cont (i1, i2, m2) m1 m3 (j1, j2, n2) n1 n3 s =>
        Downset.has R (ircp_allow i1 m1 m2) /\ Downset.has S (ircp_allow i2 m2 m3) /\
          (Downset.has R (ircp_forbid i1 m1 m2 j1 n1 n2) \/
             Downset.has S (ircp_forbid i2 m2 m3 j2 n2 n3) \/
             ivcomp_has (ircnext i1 m1 m2 j1 n1 n2 R) (ircnext i2 m2 m3 j2 n2 n3 S) s)
    end.

  Global Instance vcomp_has_ref :
    Monotonic ivcomp_has (ref ++> ref ++> ircp_ref --> impl).
  Proof.
    intros R1 R2 HR S1 S2 HS u v Huv.
    revert R1 R2 HR S1 S2 HS. cbn. unfold impl.
    induction Huv as [ [[i1 i2] m2] m1 m3
                     | [[i1 i2] m2] m1 m3 [[j1 j2] n2] n1 n3
                     | [[i1 i2] m2] m1 m3 [[j1 j2] n2] n1 n3
                     | [[i1 i2] m2] m1 m3 [[j1 j2] n2] n1 n3 k k' Hk IHk
                     | [[i1 i2] m2] m1 m3 [[j1 j2] n2] n1 n3 k
                     | [[i1 i2] m2] m1 m3 [[j1 j2] n2] n1 n3 ]; cbn.
    - firstorder.
    - firstorder.
    - firstorder.
    - intros R1 R2 HR S1 S2 HS (Hm12 & Hm23 & Hn).
      repeat (split; auto).
      destruct Hn as [Hn12 | [Hn23 | Hk']]; eauto.
      right. right. revert Hk'. eapply IHk; cbn; eauto.
    - intros R1 R2 HR S1 S2 HS (Hm12 & Hm23 & Hn).
      repeat (split; auto).
      specialize Hn as [Hn12 | Hn23]; eauto.
    - intros R1 R2 HR S1 S2 HS (Hm12 & Hm23 & Hn).
      repeat (split; auto).
      specialize Hn as [Hn12 | Hn23]; eauto.
  Qed.

  Program Definition irc_vcomp (R: irc E1 E2 I1 J1) (S: irc E2 E3 I2 J2) : irc E1 E3 I J :=
    {| Downset.has w := ivcomp_has R S w |}.
  Next Obligation.
    intros until 1. rauto.
  Qed.

  Hint Constructors ircp_ref : core.

  Lemma ircnext_vcomp (R: irc E1 E2 I1 J1) (S: irc E2 E3 I2 J2) i1 i2 j1 j2 m1 m2 m3 n1 n2 n3:
    (* Downset.has R (ircp_allow i1 m1 m2) -> *)
    (* Downset.has S (ircp_allow i2 m2 m3) -> *)
    ~ Downset.has R (ircp_forbid i1 m1 m2 j1 n1 n2) ->
    ~ Downset.has S (ircp_forbid i2 m2 m3 j2 n2 n3) ->
    ircnext (i1, i2, m2) m1 m3 (j1, j2, n2) n1 n3 (irc_vcomp R S) =
       irc_vcomp (ircnext i1 m1 m2 j1 n1 n2 R) (ircnext i2 m2 m3 j2 n2 n3 S).
  Proof.
    intros Hr1 Hs1. apply antisymmetry; intros p Hp.
    - firstorder eauto.
    - destruct p.
      + cbn in *. destruct i as [[? ?] ?].
        firstorder eauto 10 using conv_has_cont_allow.
      + cbn in *. destruct i as [[? ?] ?]. destruct j as [[? ?] ?].
        firstorder eauto 10 using conv_has_cont_allow.
      + cbn in *. destruct i as [[? ?] ?]. destruct j as [[? ?] ?].
        firstorder eauto 10 using conv_has_cont_allow.
  Qed.

End VCOMP.

Definition ivcomp {E1 E2 E3} (R: iconv E1 E2) (S: iconv E2 E3) : iconv E1 E3 :=
  {|
    question_index := (question_index R * question_index S * op E2)%type;
    answer_index := fun '(i1, i2, m2) => (answer_index R i1 * answer_index S i2 * ar m2)%type;
    iconv_carrier := irc_vcomp R S;
  |}.

Section VCOMP_ASSOC.

  Context {E1 E2 E3 E4: esig}.

  Section IRC_ASSOC.

    Context I1 I2 I3 J1 J2 J3 (R: irc E1 E2 I1 J1) (S: irc E2 E3 I2 J2) (T: irc E3 E4 I3 J3).

    Lemma irc_vcomp_assoc_1:
      irc_ref (irc_vcomp R (irc_vcomp S T)) (irc_vcomp (irc_vcomp R S) T).
    Proof.
      intros p. revert R S T. induction p.
      - rename m2 into m4.
        destruct i as [[i1 [[i2 i3] m3]] m2].
        intros R S T (H1 & H2 & H3).
        eexists ((i1, i2, m2), i3, m3).
        firstorder eauto.
      - rename m2 into m4, n2 into n4.
        destruct i as [[i1 [[i2 i3] m3]] m2].
        destruct j as [[j1 [[j2 j3] n3]] n2].
        intros R S T (H1 & (H2 & H3) & Hr).
        eexists ((i1, i2, m2), i3, m3), ((j1, j2, n2), j3, n3).
        firstorder eauto.
      - rename m2 into m4, n2 into n4.
        destruct i as [[i1 [[i2 i3] m3]] m2].
        destruct j as [[j1 [[j2 j3] n3]] n2].
        intros R S T (H1 & (H2 & H3) & Hr).
        eexists ((i1, i2, m2), i3, m3), ((j1, j2, n2), j3, n3).
        destruct Hr as [Hr|[(Hr1 & Hr2 & [Hr|Hr])|Hr]];
          try solve [ cbn; intuition eauto ].
        apply or_elim. intros Ht. cbn in Ht.
        rewrite ircnext_vcomp in Hr;
          try solve [ cbn; intuition eauto ].
        rewrite (ircnext_vcomp (irc_vcomp R S) T);
          try solve [ cbn; intuition eauto ].
        rewrite ircnext_vcomp; cbn; intuition eauto.
    Qed.

    Lemma irc_vcomp_assoc_2 :
      irc_ref (irc_vcomp (irc_vcomp R S) T) (irc_vcomp R (irc_vcomp S T)).
    Proof.
      intros p. revert R S T. induction p.
      - rename m2 into m4.
        destruct i as [[[[i1 i2] m2] i3] m3].
        intros R S T ((H1 & H2) & H3).
        eexists (i1, (i2, i3, m3), m2).
        firstorder eauto.
      - rename m2 into m4, n2 into n4.
        destruct i as [[[[i1 i2] m2] i3] m3].
        destruct j as [[[[j1 j2] n2] j3] n3].
        intros R S T ((H1 & H2) & (H3 & H4)).
        eexists (i1, (i2, i3, m3), m2), (j1, (j2, j3, n3), n2).
        firstorder eauto.
      - rename m2 into m4, n2 into n4.
        destruct i as [[[[i1 i2] m2] i3] m3].
        destruct j as [[[[j1 j2] n2] j3] n3].
        intros R S T ((H1 & H2) & (H3 & Hr)).
        eexists (i1, (i2, i3, m3), m2), (j1, (j2, j3, n3), n2).
        destruct Hr as [(Hr1 & Hr2 & [Hr|Hr])|[Hr|Hr]];
          try solve [ cbn; intuition eauto ].
        apply or_elim. intros Ht. cbn in Ht.
        rewrite ircnext_vcomp in Hr;
          try solve [ cbn; intuition eauto ].
        rewrite (ircnext_vcomp R (irc_vcomp S T));
          try solve [ cbn; intuition eauto ].
        rewrite ircnext_vcomp; cbn; intuition eauto.
    Qed.

  End IRC_ASSOC.

  Lemma ivcomp_assoc (R: iconv E1 E2) (S: iconv E2 E3) (T: iconv E3 E4):
    iconv_eqv (ivcomp R (ivcomp S T)) (ivcomp (ivcomp R S) T).
  Proof.
    split. apply irc_vcomp_assoc_1. apply irc_vcomp_assoc_2.
  Qed.

End VCOMP_ASSOC.

Section RSQ.

  Context {E1 E2 F1 F2 : esig}.

  Section RSP.

    Context {I1 I2: Type} {J1: I1 -> Type} {J2: I2 -> Type}.

    Inductive rsp (R: irc E1 E2 I1 J1) (S: irc F1 F2 I2 J2):
      forall {p1 p2}, rspos p1 p2 -> @play E1 F1 p1 -> strat E2 F2 p2 -> Prop :=
    | rsp_ready τ :
      Downset.has τ pnil_ready ->
      rsp R S rs_ready pnil_ready τ
    | rsp_oq q1 s τ :
      Downset.has τ pnil_ready ->
      (forall iq q2, Downset.has S (ircp_allow iq q1 q2) ->
                rsp R S (rs_running q1 q2) s (next (oq q2) τ)) ->
      rsp R S rs_ready (oq q1 :: s) τ
    | rsp_pq q1 q2 im m1 m2 s τ :
      Downset.has R (ircp_allow im m1 m2) ->
      rsp R S (rs_suspended q1 q2 m1 m2) s (next (pq m2) τ) ->
      rsp R S (rs_running q1 q2) (pq m1 :: s) τ
    | rsp_suspended q1 q2 m1 m2 τ :
      Downset.has τ (pnil_suspended q2 m2) ->
      rsp R S (rs_suspended q1 q2 m1 m2) (pnil_suspended q1 m1) τ
    | rsp_oa q1 q2 m1 m2 n1 s τ :
      Downset.has τ (pnil_suspended q2 m2) ->
      (forall im jn n2, ~ Downset.has R (ircp_forbid im m1 m2 jn n1 n2) ->
         rsp (sup im, inf jn, ircnext im m1 m2 jn n1 n2 R) S (rs_running q1 q2) s (next (oa n2) τ)) ->
      rsp R S (rs_suspended q1 q2 m1 m2) (oa n1 :: s) τ
    | rsp_pa q1 q2 r1 s τ :
      (forall iq, exists jr r2, ~ Downset.has S (ircp_forbid iq q1 q2 jr r1 r2) /\
      rsp R (sup iq, inf jr, ircnext iq q1 q2 jr r1 r2 S) rs_ready s (next (pa r2) τ)) ->
      rsp R S (rs_running q1 q2) (pa r1 :: s) τ.

    Definition rsq_when (R: irc E1 E2 I1 J1) (S: irc F1 F2 I2 J2)
      {p1 p2} p (σ : strat E1 F1 p1) (τ : strat E2 F2 p2) : Prop :=
      forall s, Downset.has σ s -> rsp R S p s τ.

    Lemma rsp_ready_inv_nil R S s τ :
      rsp R S rs_ready s τ ->
      Downset.has τ pnil_ready.
    Proof.
      intro H. dependent destruction H; auto.
    Qed.

    Lemma rsp_suspended_inv_nil R S q1 q2 m1 m2 s τ :
      rsp R S (rs_suspended q1 q2 m1 m2) s τ ->
      Downset.has τ (pnil_suspended q2 m2).
    Proof.
      intro H. dependent destruction H; auto.
    Qed.

    Hint Resolve rsp_ready_inv_nil rsp_suspended_inv_nil : determinism.

    Lemma rsq_next_oq {R: irc E1 E2 I1 J1} {S: irc F1 F2 I2 J2} {σ τ} i q1 q2 :
      rsq_when R S rs_ready σ τ ->
      Downset.has S (ircp_allow i q1 q2) ->
      rsq_when R S (rs_running q1 q2) (next (oq q1) σ) (next (oq q2) τ).
    Proof.
      intros Hστ Hq s Hs. cbn in *.
      specialize (Hστ _ Hs).
      dependent destruction Hστ.
      eauto.
    Qed.

    Lemma rsq_next_pq {R S q1 q2 σ τ} `{!Deterministic τ} m1 :
      rsq_when R S (rs_running q1 q2) σ τ ->
      Downset.has σ (pq m1 :: pnil_suspended q1 m1) ->
      exists im m2,
        Downset.has R (ircp_allow im m1 m2) /\
          Downset.has τ (pq m2 :: pnil_suspended q2 m2) /\
          rsq_when R S (rs_suspended q1 q2 m1 m2) (next (pq m1) σ) (next (pq m2) τ).
    Proof.
      intros Hστ H.
      apply Hστ in H.
      dependent destruction H. exists im, m2. split; auto.
      dependent destruction H0. cbn in H0. split; auto.
      intros s Hs. cbn in Hs.
      apply Hστ in Hs.
      dependent destruction Hs.
      determinism m2 m3.
      subst. auto.
    Qed.

    Lemma rsq_next_oa {R S q1 q2 im m1 m2 σ τ} jn n1 n2 :
      rsq_when R S (rs_suspended q1 q2 m1 m2) σ τ ->
      ~ Downset.has R (ircp_forbid im m1 m2 jn n1 n2) ->
      rsq_when (ircnext im m1 m2 jn n1 n2 R) S (rs_running q1 q2) (next (oa n1) σ) (next (oa n2) τ).
    Proof.
      intros Hστ Hn s Hs.
      specialize (Hστ _ Hs).
      dependent destruction Hστ.
      eauto.
    (* Qed. *)
    Admitted.

    Lemma rsq_next_pa {R S q1 q2 σ τ} `{!Deterministic τ} r1 :
      rsq_when R S (rs_running q1 q2) σ τ ->
      Downset.has σ (pa r1 :: pnil_ready) ->
      forall iq, exists jr r2,
        ~ Downset.has S (ircp_forbid iq q1 q2 jr r1 r2) /\
          Downset.has τ (pa r2 :: pnil_ready) /\
          rsq_when R (ircnext iq q1 q2 jr r1 r2 S) rs_ready (next (pa r1) σ) (next (pa r2) τ).
    Proof.
      intros Hστ H.
      apply Hστ in H.
      dependent destruction H.
      (* exists iq, jr, r2. split; auto. *)
      (* dependent destruction H0. cbn in H0. split; auto. *)
      (* intros s Hs. cbn in Hs. *)
      (* apply Hστ in Hs. *)
      (* dependent destruction Hs. *)
      (* determinism r2 r3. *)
      (* assumption. *)
    (* Qed. *)
    Admitted.

  End RSP.

  Definition rsq (R S: iconv _ _) σ τ :=
    rsq_when R S rs_ready σ τ.

End RSQ.

Section RSVCOMP.
  Context {E1 F1 E2 F2 E3 F3 : esig}.

  Variant rsvpos:
    forall {p1 p2 p3}, @rspos E1 E2 F1 F2 p1 p2 ->
                  @rspos E2 E3 F2 F3 p2 p3 ->
                  @rspos E1 E3 F1 F3 p1 p3 -> Type :=
    | rsv_ready :
        rsvpos rs_ready rs_ready rs_ready
    | rsv_running q1 q2 q3 :
        rsvpos (rs_running q1 q2)
               (rs_running q2 q3)
               (rs_running q1 q3)
    | rsv_suspended q1 q2 q3 m1 m2 m3 :
        rsvpos (rs_suspended q1 q2 m1 m2)
               (rs_suspended q2 q3 m2 m3)
               (rs_suspended q1 q3 m1 m3).

  Section VCOMP.
    Context {I1 J1 I1' J1' I2 J2 I2' J2'}
        (R : irc E1 E2 I1 J1) (R' : irc E2 E3 I1' J1')
        (S : irc F1 F2 I2 J2) (S' : irc F2 F3 I2' J2').

    Lemma rsp_vcomp
      {p1 p2 p3 p12 p23 p13} (p : rsvpos p12 p23 p13) :
      forall (s1 : @play E1 F1 p1) (σ2 : strat E2 F2 p2) (σ3 : strat E3 F3 p3)
       `{Hσ3 : !Deterministic σ3},
        rsp R S p12 s1 σ2 ->
        rsq_when R' S' p23 σ2 σ3 ->
        match p with
        | rsv_ready
        | rsv_running _ _ _ =>
            rsp (irc_vcomp R R') (irc_vcomp S S') p13 s1 σ3
        | rsv_suspended _ _ _ m1 m2 m3 =>
            (exists im12, Downset.has R (ircp_allow im12 m1 m2)) ->
            (exists im23, Downset.has R' (ircp_allow im23 m2 m3)) ->
            rsp (irc_vcomp R R') (irc_vcomp S S') p13 s1 σ3
        end.
    Proof.
      intros s1 σ2 σ3 Hσ3 H12 Hσ23.
      revert p3 p23 p13 p R' S' σ3 Hσ3 Hσ23.
      induction H12; intros; dependent destruction p.
      - (* ready *)
        pose proof (Hσ23 _ H) as Hnil.
        dependent destruction Hnil.
        constructor; auto.
      - (* incoming question *)
        pose proof (Hσ23 _ H) as Hnil.
        dependent destruction Hnil.
        constructor; auto.
        intros [[i2 i2'] q2] q3 [Hq12 Hq13].
        eapply (H1 i2 q2 Hq12 _ _ _ (rsv_running q1 q2 q3)); eauto with typeclass_instances.
        eapply rsq_next_oq; eauto.
      - (* outgoing question *)
        rename q4 into q3.
        assert (Hm2 : Downset.has τ (pq m2 :: pnil_suspended q2 m2))
          by (dependent destruction H12; cbn in *; auto).
        edestruct @rsq_next_pq as (i1' & m3 & Hm23 & Hm3 & Hnext); eauto.
        econstructor. { instantiate (2 := (_, _, _)). cbn. eauto. }
        eapply (IHrsp _ _ _ (rsv_suspended q1 q2 q3 m1 m2 m3));
          eauto with typeclass_instances.
      - (* suspended *)
        rename q4 into q3, m4 into m3.
        pose proof (Hσ23 _ H) as Hnil.
        dependent destruction Hnil.
        constructor; auto.
      - (* environment answer *)
        rename q4 into q3, m4 into m3.
        pose proof (Hσ23 _ H) as Hnil.
        dependent destruction Hnil.
        intros (im12 & Hm12) (im23 & Hm23).
        (* apply (rsp_inf (rs_suspended q1 q3 m1 m3)). { typeclasses eauto. } *)
        (* split. { eauto using None. } *)
        (* intros xn2. *)
        constructor; auto.
        intros [[i1 i1'] m2x] [[j1 j1'] n2] n3 Hn13. cbn in Hn13.
        apply not_and_or in Hn13 as [ | Hn13]; try tauto.
        apply not_and_or in Hn13 as [ | Hn13]; try tauto.
        (* apply not_all_ex_not in Hn13 as [n2 Hn13]. *)
        (* apply imply_to_and in Hn13 as [Hxn2 Hn13]. subst xn2. *)
        apply not_or_and in Hn13 as [Hn12 Hn23].
        rewrite ircnext_vcomp by auto.
        eapply (H1 j1 n2 Hn12  _ _ _ (rsv_running _ _ q1 q2 q3)); eauto with typeclass_instances.
        apply rsq_next_oa; auto.
      - (* component answer *)
        rename q4 into q3, H into Hr12.
        (* rewrite (inf_lb (Some r2)). *)
        destruct (rsq_next_pa r2 Hσ23) as (j2' & r3 & Hr23 & Hr3 & H23). {
          dependent destruction H12; auto.
        }
        econstructor. { instantiate (2 := (_, _, _)). cbn.
                        intros (Hq12 & Hq23 & [Hr | Hr]); eauto. }
        rewrite ircnext_vcomp; eauto.
        eapply (IHrsp _ _ _ rsv_ready); eauto with typeclass_instances.
    Qed.

    Lemma rsq_vcomp_when
      {p1 p2 p3 p12 p23 p13} (p : rsvpos p12 p23 p13) :
      forall (σ1 : strat E1 F1 p1) (σ2 : strat E2 F2 p2) (σ3 : strat E3 F3 p3)
        `{Hσ3 : !Deterministic σ3},
        rsq_when R S p12 σ1 σ2 ->
        rsq_when R' S' p23 σ2 σ3 ->
        match p with
        | rsv_ready
        | rsv_running _ _ _ _ _ =>
            rsq_when (irc_vcomp R R') (irc_vcomp S S') p13 σ1 σ3
        | rsv_suspended _ _ _ _ _ im12 im23 m1 m2 m3 =>
            Downset.has R (ircp_allow im12 m1 m2) ->
            Downset.has R' (ircp_allow im23 m2 m3) ->
            rsq_when (irc_vcomp R R') (irc_vcomp S S') p13 σ1 σ3
        end.
    Proof.
      intros.
      pose proof (rsp_vcomp p).
      destruct p; cbn in *; intros; intro; eauto.
    Qed.

  End VCOMP.

  Lemma rsq_vcomp R R' S S' (σ1 : E1 ->> F1) (σ2 : E2 ->> F2) (σ3 : E3 ->> F3) `{Hσ3 : !Deterministic σ3}:
    rsq R S σ1 σ2 ->
    rsq R' S' σ2 σ3 ->
    rsq (ivcomp R R') (ivcomp S S') σ1 σ3.
  Proof.
    apply (rsq_vcomp_when _ _ _ _ rsv_ready); auto.
  Qed.

End RSVCOMP.
