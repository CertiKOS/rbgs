Require Import Classical.
Require Import FunctionalExtensionality.
Require Import Program.Equality.
Require Import LogicalRelations.
Require Import Poset.
Require Import Lattice.
Require Import Downset.

Require Import IntStrat.

(*

Consider R has play:
  n1n2 q1q2 ⊥
  n1n2'q1q2'⊥

Consider S has play:
  n2n3 q2q3  ⊥
  n2'n3q2'q3'⊥

Consider T has play:
  n3n4 q3q4 ⊥
  n3n4 q3'q4⊥

When R and S are associated first,
n1 and n3 can be related via either n2 or n2'.
If n2 is chosen, q1 and q3 can be related via either q2.
If n2' is chosen, q1 and q3' can be related via either q2'.
But if the choice of n2 or n2' is defered,
q1 can no longer be related with either q3 or q3'.
So in case of (R ;; S) ;; T,
no questions can be related in the next round.

When S and T are associated first,
both n2 and n2' can be related with n4 via n3.
And since n3 is the only choice,
we have the following plays in S ;; T:
  n2n4 q2q4 ⊥
  n2'n4q2'q4⊥

Then when it compose with R,
q1 and q4 are related because they are related
on both paths q1q2q4 and q1q2'q4.
*)

Lemma or_elim (P Q: Prop): (~ P -> Q) -> P \/ Q.
Proof. intros. destruct (classic P); firstorder. Qed.

Section IRC.
  Context {E1 E2 : esig}.
  Obligation Tactic := cbn.

  Inductive ircp {I: Type} :=
  | ircp_allow (i: I) (m1: E1) (m2: E2)
  | ircp_forbid (i: I) (m1: E1) (m2: E2) (n1: ar m1) (n2: ar m2)
  | ircp_cont (i: I) (m1: E1) (m2: E2) (n1: ar m1) (n2: ar m2) (k: ircp).

  Inductive ircp_ref {I} : relation (@ircp I) :=
    | ircp_allow_ref i m1 m2 :
        ircp_ref (ircp_allow i m1 m2) (ircp_allow i m1 m2)
    | ircp_allow_cont_ref i m1 m2 n1 n2 k :
        ircp_ref (ircp_allow i m1 m2) (ircp_cont i m1 m2 n1 n2 k)
    | ircp_allow_forbid_ref i m1 m2 n1 n2 :
        ircp_ref (ircp_allow i m1 m2) (ircp_forbid i m1 m2 n1 n2)
    | ircp_cont_ref i m1 m2 n1 n2 k k' :
        ircp_ref k k' -> ircp_ref (ircp_cont i m1 m2 n1 n2 k) (ircp_cont i m1 m2 n1 n2 k')
    | ircp_cont_forbid_ref i m1 m2 n1 n2 k :
        ircp_ref (ircp_cont i m1 m2 n1 n2 k) (ircp_forbid i m1 m2 n1 n2)
    | ircp_forbid_ref i m1 m2 n1 n2 :
        ircp_ref (ircp_forbid i m1 m2 n1 n2) (ircp_forbid i m1 m2 n1 n2).

  Program Canonical Structure ircp_poset {I} : poset :=
    {|
      poset_carrier := @ircp I;
      ref := @ircp_ref I;
    |}.
  Next Obligation.
    split.
    - intro w. induction w; constructor; auto.
    - intros x y z Hxy. revert z.
      induction Hxy; intros z Hyz;
        dependent destruction Hyz; constructor; auto.
  Qed.
  Next Obligation.
    intros p w1 w2 Hw12 Hw21.
    induction Hw12; dependent destruction Hw21; firstorder congruence.
  Qed.

  Definition irc I := poset_carrier (downset (@ircp_poset I)).

  Program Definition ircnext {I} (i: I) q1 q2 r1 r2 (R : irc I) : irc I :=
    {| Downset.has w := Downset.has R (ircp_cont i q1 q2 r1 r2 w) |}.
  Next Obligation.
    intros i q1 q2 r1 r2 R s t Hst Hs.
    eapply Downset.closed; eauto.
    eapply ircp_cont_ref; auto.
  Qed.

  Lemma ircnext_inf {I J} (i: I) q1 q2 r1 r2 (R: J -> irc I):
    ircnext i q1 q2 r1 r2 (linf R) = linf (fun j => ircnext i q1 q2 r1 r2 (R j)).
  Proof.
    apply antisymmetry; intros; cbn; eauto.
  Qed.

  Record iconv :=
    {
      index: Type;
      iconv_carrier: @irc index;
    }.

End IRC.

Arguments ircp : clear implicits.
Arguments irc : clear implicits.
Arguments iconv : clear implicits.
Coercion iconv_carrier : iconv >-> irc.

Section REF.
  Context {E1 E2: esig}.

  Fixpoint has_ircp {I J: Type} (f: J -> I) (R: irc E1 E2 I) (s: ircp E1 E2 J): Prop :=
    match s with
    | ircp_allow j m1 m2 => Downset.has R (ircp_allow (f j) m1 m2)
    | ircp_forbid j m1 m2 n1 n2 => Downset.has R (ircp_forbid (f j) m1 m2 n1 n2)
    | ircp_cont j m1 m2 n1 n2 k =>
        (* This is wrong. We need Downset.has R (ircp_forbid (f j) m1 m2 n1 n2) \/ .. *)
        has_ircp f (ircnext (f j) m1 m2 n1 n2 R) k
    end.

  Definition irc_ref {I J: Type} (R: irc E1 E2 I) (S: irc E1 E2 J): Prop :=
    exists f, forall p1, Downset.has R p1 -> has_ircp f S p1.

  Definition iconv_ref (R S: iconv E1 E2): Prop := irc_ref R S.
  Definition iconv_eqv (R S: iconv E1 E2): Prop := irc_ref R S /\ irc_ref S R.

  Lemma has_ircp_inf {I J K: Type} f (R: K -> irc E1 E2 I) (s: ircp E1 E2 J):
    (forall k, has_ircp f (R k) s) -> has_ircp f (linf R) s.
  Proof.
    revert R. induction s; cbn -[linf]; intros; eauto.
    rewrite ircnext_inf. apply IHs. eauto. 
  Qed.

End REF.

Section VCOMP.
  Context {E1 E2 E3: esig} {I J: Type}.
  Obligation Tactic := cbn.

  Fixpoint ivcomp_has (R: irc E1 E2 I) (S: irc E2 E3 J) (s: ircp E1 E3 (I * J * op E2)) : Prop :=
    match s with
    | ircp_allow (i, j, m2) m1 m3 =>
        Downset.has R (ircp_allow i m1 m2) /\ Downset.has S (ircp_allow j m2 m3)
    | ircp_forbid (i, j, m2) m1 m3 n1 n3 =>
        Downset.has R (ircp_allow i m1 m2) /\ Downset.has S (ircp_allow j m2 m3) /\
          forall n2, Downset.has R (ircp_forbid i m1 m2 n1 n2) \/
                  Downset.has S (ircp_forbid j m2 m3 n2 n3)
    | ircp_cont (i, j, m2) m1 m3 n1 n3 s =>
        Downset.has R (ircp_allow i m1 m2) /\ Downset.has S (ircp_allow j m2 m3) /\
          forall n2, Downset.has R (ircp_forbid i m1 m2 n1 n2) \/
                  Downset.has S (ircp_forbid j m2 m3 n2 n3) \/
                  ivcomp_has (ircnext i m1 m2 n1 n2 R) (ircnext j m2 m3 n2 n3 S) s
    end.

  Program Definition irc_vcomp (R: irc E1 E2 I) (S: irc E2 E3 J) : irc E1 E3 (I * J * op E2) :=
    {| Downset.has w := ivcomp_has R S w |}.
  Next Obligation.
  Admitted.

  Lemma ircnext_vcomp (R: irc E1 E2 I) (S: irc E2 E3 J) i j m1 m2 m3 n1 n3:
    Downset.has R (ircp_allow i m1 m2) ->
    Downset.has S (ircp_allow j m2 m3) ->
    ircnext (i, j, m2) m1 m3 n1 n3 (irc_vcomp R S) =
      inf { n2 | ~ Downset.has R (ircp_forbid i m1 m2 n1 n2) /\
                   ~ Downset.has S (ircp_forbid j m2 m3 n2 n3) }, irc_vcomp (ircnext i m1 m2 n1 n2 R) (ircnext j m2 m3 n2 n3 S).
  Proof.
    intros Hr Hs. apply antisymmetry.
    - intros p (Hp1 & Hp2 & Hp3) (n2 & Hn1 & Hn2). cbn in *.
      specialize (Hp3 n2) as [Hp|[Hp|Hp]]; easy.
    - intros p Hp. cbn. repeat apply conj; eauto.
      intros n2.
      destruct (classic (Downset.has R (ircp_forbid i m1 m2 n1 n2))) as [|Ha]; eauto.
      destruct (classic (Downset.has S (ircp_forbid j m2 m3 n2 n3))) as [|Hb]; eauto.
      cbn in Hp. right. right.
      specialize (Hp (exist _ n2 (conj Ha Hb))). apply Hp.
  Qed.

  Lemma irc_vcomp_inf_l {K} (R: K -> irc E1 E2 I) (S: irc E2 E3 J):
    inhabited K ->
    inf k, irc_vcomp (R k) S [= irc_vcomp (linf R) S.
  Proof.
    intros HK.
    (* apply antisymmetry. *)
    (* - intros p Hp k. revert R S Hp k. induction p. *)
    (*   + rename m2 into m3. *)
    (*     intros. destruct i as [[i j] m2]. cbn in *. firstorder. *)
    (*   + rename m2 into m3, n2 into n3. *)
    (*     intros. destruct i as [[i j] m2]. cbn in *. firstorder. *)
    (*   + rename m2 into m3, n2 into n3. *)
    (*     intros. destruct i as [[i j] m2]. cbn -[linf] in *. *)
    (*     destruct Hp as (Hp1 & Hp2 & Hp). repeat apply conj; eauto. *)
    (*     intros n2. specialize (Hp n2) as [Hp|[Hp|Hp]]. *)
    (*     { left. eauto. } *)
    (*     { right. left. eauto. } *)
    (*     rewrite ircnext_inf in Hp. specialize (IHp _ _ Hp). *)
    (*     right. right. eauto. *)
    - intros p Hp. revert R S Hp. induction p.
      + rename m2 into m3.
        intros. destruct i as [[i j] m2]. cbn in *.
        firstorder eauto.
      + rename m2 into m3, n2 into n3.
        intros. destruct i as [[i j] m2]. cbn in *.
        split. firstorder eauto.
        split. firstorder eauto.
        intros n2.
        destruct (classic (Downset.has S (ircp_forbid j m2 m3 n2 n3)));
          firstorder eauto.
      + rename m2 into m3, n2 into n3.
        intros. destruct i as [[i j] m2]. cbn -[linf] in *. cbn in Hp.
        split. firstorder eauto.
        split. firstorder eauto.
        intros n2.
        apply or_elim. intros Hn2.
        apply or_elim. intros Hn3.
        rewrite ircnext_inf. eapply IHp. intros k.
        specialize (Hp k) as (Hp1 & Hp2 & Hp3).
        specialize (Hp3 n2). firstorder eauto.
        cbn in Hn2.
  Admitted.

  Lemma has_ircp_irc_vcomp_inf_l {K} (R: K -> irc E1 E2 I) (S: irc E2 E3 J) p:
    (exists k, Downset.has (irc_vcomp (R k) S) p) ->
    (forall k, Downset.has (irc_vcomp (R k) S) p) ->
    Downset.has (irc_vcomp (linf R) S) p.
  Proof.
    revert R S. induction p.
    - rename m2 into m3. intros R S (k & Hk) Hk'. cbn in *.
      destruct i as [[i j] m2].
      firstorder eauto.
    - rename m2 into m3, n2 into n3. intros R S (k & Hk) Hk'. cbn in *.
      destruct i as [[i j] m2].
      repeat apply conj; firstorder eauto. admit.
    - rename m2 into m3, n2 into n3. intros R S (k & Hk) Hk'. cbn -[linf] in *.
      destruct i as [[i j] m2]. destruct Hk as (Hk1 & Hk2 & Hk3).
      split. firstorder eauto.
      split. firstorder eauto.
      intros n2.
      apply or_elim. intros Hn2.
      apply or_elim. intros Hn3.
      rewrite ircnext_inf. eapply IHp.
      + exists k. admit.
      + intros k'.

      rewrite ircnext_vcomp. 2-3: admit.
      apply has_ircp_inf. intros (n2 & Hn1 & Hn2). cbn -[linf].
      rewrite ircnext_inf. apply IHp.
      + exists k. rewrite ircnext_vcomp in Hk. 2-3: admit.


End VCOMP.

Program Definition ivcomp {E1 E2 E3} (R: iconv E1 E2) (S: iconv E2 E3) : iconv E1 E3 :=
  {|
    index := index R * index S * op E2;
    iconv_carrier := irc_vcomp R S;
  |}.

Section VCOMP_ASSOC.

  Context {E1 E2 E3 E4: esig}
    (R: iconv E1 E2) (S: iconv E2 E3) (T: iconv E3 E4).

  Lemma ivcomp_assoc:
    iconv_eqv (ivcomp R (ivcomp S T)) (ivcomp (ivcomp R S) T).
  Proof.
    split.
    - exists (fun '(i, (j, k, m3), m2) => (i, j, m2, k, m3)).
      intros p1. induction p1; cbn.
      + rename m2 into m4. destruct i as [[i [[j k] m3]] m2].
        firstorder eauto.
      + rename m2 into m4, n2 into n4. destruct i as [[i [[j k] m3]] m2].
        intros (H1 & (H2 & H3) & Hr).
        repeat apply conj; eauto.
        intros n3.
        destruct (classic (Downset.has (iconv_carrier T) (ircp_forbid k m3 m4 n3 n4))) as [HT|HT].
        { right; eauto. }
        left. firstorder eauto.
      + rename m2 into m4, n2 into n4. destruct i as [[i [[j k] m3]] m2].
        intros (H1 & (H2 & H3) & Hr).
        rewrite ircnext_vcomp. 2-3: cbn; eauto.
        apply has_ircp_inf.
        intros (n3 & Ha & Hb). cbn. cbn in Ha.
        rewrite ircnext_vcomp; eauto.


End VCOMP_ASSOC.
