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

  Lemma ircnext_vcomp (R: irc E1 E2 I1 J1) (S: irc E2 E3 I2 J2) i1 i2 j1 j2 m1 m2 m3 n1 n2 n3:
    Downset.has R (ircp_allow i1 m1 m2) ->
    Downset.has S (ircp_allow i2 m2 m3) ->
    ~ Downset.has R (ircp_forbid i1 m1 m2 j1 n1 n2) ->
    ~ Downset.has S (ircp_forbid i2 m2 m3 j2 n2 n3) ->
    ircnext (i1, i2, m2) m1 m3 (j1, j2, n2) n1 n3 (irc_vcomp R S) =
       irc_vcomp (ircnext i1 m1 m2 j1 n1 n2 R) (ircnext i2 m2 m3 j2 n2 n3 S).
  Proof.
    intros Hr Hs Hr1 Hs1. apply antisymmetry; intros p Hp; firstorder eauto.
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
