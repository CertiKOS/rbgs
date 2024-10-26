Require Import Classical.
Require Import FunctionalExtensionality.
Require Import Program.Equality.
Require Import LogicalRelations.
Require Import Poset.
Require Import Lattice.
Require Import Downset.

Require Import IntStrat.

Section RC.
  Obligation Tactic := cbn.

  Context {E1 E2 : esig}.
  Variant rcpos :=
    | rc_ready
    | rc_pending (m1: op E1) (m2: op E2).

  Inductive rcplay : rcpos -> Type :=
  | rc_question_bot (m1: op E1) (m2: op E2): rcplay rc_ready (* m1m2\bot *)
  | rc_question (m1: op E1) (m2: op E2):                     (* m1m2t *)
    rcplay (rc_pending m1 m2) -> rcplay rc_ready
  | rc_answer_top m1 m2 (n1: ar m1) (n2: ar m2): rcplay (rc_pending m1 m2) (* n1n2\top *)
  | rc_answer m1 m2 (n1: ar m1) (n2: ar m2):
    rcplay rc_ready -> rcplay (rc_pending m1 m2). (* n1n2s *)

  Inductive rcplay_ref : forall {p: rcpos}, rcplay p -> rcplay p -> Prop :=
  | rcplay_question_ref1 m1 m2:
    rcplay_ref (rc_question_bot m1 m2) (rc_question_bot m1 m2)
  | rcplay_question_ref2 m1 m2 s:
    rcplay_ref (rc_question_bot m1 m2) (rc_question m1 m2 s)
  | rcplay_question_cont_ref m1 m2 s1 s2:
    rcplay_ref s1 s2 ->
    rcplay_ref (rc_question m1 m2 s1) (rc_question m1 m2 s2)
  | rcplay_answer_ref1 m1 m2 n1 n2:
    rcplay_ref (rc_answer_top m1 m2 n1 n2) (rc_answer_top m1 m2 n1 n2)
  | rcplay_answer_ref2 m1 m2 n1 n2 s:
    rcplay_ref (rc_answer m1 m2 n1 n2 s) (rc_answer_top m1 m2 n1 n2)
  | rcplay_answer_cont_ref m1 m2 n1 n2 s1 s2:
    rcplay_ref s1 s2 ->
    rcplay_ref (rc_answer m1 m2 n1 n2 s1) (rc_answer m1 m2 n1 n2 s2).

  Program Canonical Structure rcplay_poset (p : rcpos) : poset :=
    {|
      poset_carrier := rcplay p;
      ref := rcplay_ref;
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

  Definition rc p := poset_carrier (downset (rcplay_poset p)).

  Definition match_question (R: rc rc_ready) q1 q2 : Prop :=
    Downset.has R (rc_question_bot q1 q2).

  Program Definition after_question (R: rc rc_ready) q1 q2 : rc (rc_pending q1 q2) :=
    {| Downset.has s := Downset.has R (rc_question q1 q2 s) |}.
  Next Obligation.
    intros * Hxy Hy. eapply Downset.closed; eauto.
    constructor; auto.
  Qed.

  Definition match_answer {q1 q2} (R: rc _) (n1: ar q1) (n2: ar q2) : Prop :=
    ~ Downset.has R (rc_answer_top q1 q2 n1 n2).

  Program Definition after_answer {q1: op E1} {q2: op E2}
    (R: rc (rc_pending q1 q2)) (n1: ar q1) (n2: ar q2)  : rc rc_ready :=
    {| Downset.has s := Downset.has R (rc_answer q1 q2 n1 n2 s) |}.
  Next Obligation.
    intros * Hxy Hy. eapply Downset.closed; eauto.
    constructor; auto.
  Qed.

End RC.

Arguments rcpos : clear implicits.
Arguments rc : clear implicits.
Arguments rc_ready {E1 E2}.
Arguments rc_pending {E1 E2} _ _.

Lemma after_question_sup {E1 E2} {I: Type} q1 q2 (R: I -> rc E1 E2 rc_ready):
  after_question (lsup R) q1 q2 = lsup (fun i => after_question (R i) q1 q2).
Proof. apply antisymmetry; cbn; eauto. Qed.

Section RSQ.

Section VCOMP.

  Context {E1 E2 E3: esig}.
  Variant vpos : rcpos E1 E2 -> rcpos E2 E3 -> rcpos E1 E3 -> Type :=
    | vpos_ready : vpos rc_ready rc_ready rc_ready
    | vpos_pending (m1: op E1) (m2: op E2) (m3: op E3):
        vpos (rc_pending m1 m2) (rc_pending m2 m3) (rc_pending m1 m3).

  Inductive vcomp_has:
    forall {i j k} (p: vpos i j k), rc E1 E2 i -> rc E2 E3 j -> rcplay k -> Prop := 
  | vcomp_question_bot R S m1 m2 m3:
    Downset.has R (rc_question_bot m1 m2) ->
    Downset.has S (rc_question_bot m2 m3) ->
    vcomp_has vpos_ready R S (rc_question_bot m1 m3)
  | vcomp_question R S m1 m2 m3 v R' S':
    R' = after_question R m1 m2 ->
    S' = after_question S m2 m3 ->
    (R' = bot -> Downset.has R (rc_question_bot m1 m2)) ->
    (S' = bot -> Downset.has S (rc_question_bot m2 m3)) ->
    vcomp_has (vpos_pending m1 m2 m3) R' S' v ->
    vcomp_has vpos_ready R S (rc_question m1 m3 v)
  | vcomp_answer_top m1 m2 m3 R S n1 n3:
    (forall n2, Downset.has R (rc_answer_top m1 m2 n1 n2) \/
             Downset.has S (rc_answer_top m2 m3 n2 n3)) ->
    vcomp_has (vpos_pending m1 m2 m3) R S (rc_answer_top m1 m3 n1 n3)
  | vcomp_answer m1 m2 m3 R S n1 n3 v:
    (forall n2 R' S',
        R' = after_answer R n1 n2 ->
        S' = after_answer S n2 n3 ->
        (R' = top -> ~ Downset.has R (rc_answer_top m1 m2 n1 n2)) ->
        (S' = top -> ~ Downset.has S (rc_answer_top m2 m3 n2 n3)) ->
        vcomp_has vpos_ready R' S' v) ->
    vcomp_has (vpos_pending m1 m2 m3) R S (rc_answer m1 m3 n1 n3 v).

  Program Definition vcomp_when {i j k} (p: vpos i j k)
    (R: rc E1 E2 i) (S: rc E2 E3 j) : rc E1 E3 k :=
    {| Downset.has w := vcomp_has p R S w |}.
  Next Obligation. Admitted.

  Inductive vcomp_at_question_has (m2: op E2):
    forall {i j k}, rc E1 E2 i -> rc E2 E3 j -> rcplay k -> Prop :=
  | vcomp_at_question_question_bot R S m1 m3:
    Downset.has R (rc_question_bot m1 m2) ->
    Downset.has S (rc_question_bot m2 m3) ->
    vcomp_at_question_has m2 R S (rc_question_bot m1 m3)
  | vcomp_at_question_question R S m1 m3 v R' S':
    R' = after_question R m1 m2 ->
    S' = after_question S m2 m3 ->
    (R' = bot -> Downset.has R (rc_question_bot m1 m2)) ->
    (S' = bot -> Downset.has S (rc_question_bot m2 m3)) ->
    vcomp_has (vpos_pending m1 m2 m3) R' S' v ->
    vcomp_at_question_has m2 R S (rc_question m1 m3 v).

  Inductive vcomp_at_answer_has m1 m2 m3 (xn2: option (ar m2)):
    forall {i j k}, rc E1 E2 i -> rc E2 E3 j -> rcplay k -> Prop :=
  | vcomp_at_answer_answer_top R S n1 n3:
    (forall n2, xn2 = Some n2 ->
             Downset.has R (rc_answer_top m1 m2 n1 n2) \/
             Downset.has S (rc_answer_top m2 m3 n2 n3)) ->
    vcomp_at_answer_has m1 m2 m3 xn2 R S (rc_answer_top m1 m3 n1 n3)
  | vcomp_at_answer_answer R S n1 n3 v:
    (forall n2 R' S',
        xn2 = Some n2 ->
        R' = after_answer R n1 n2 ->
        S' = after_answer S n2 n3 ->
        (R' = top -> ~ Downset.has R (rc_answer_top m1 m2 n1 n2)) ->
        (S' = top -> ~ Downset.has S (rc_answer_top m2 m3 n2 n3)) ->
        vcomp_has vpos_ready R' S' v) ->
    vcomp_at_answer_has m1 m2 m3 xn2 R S (rc_answer m1 m3 n1 n3 v).
  (* | vcomp_at_answer_answer R S n1 n3 v: *)
  (*   (forall n2, xn2 = Some n2 -> *)
  (*            Downset.has R (rc_answer_top m1 m2 n1 n2) \/ *)
  (*            Downset.has S (rc_answer_top m2 m3 n2 n3) \/ *)
  (*            vcomp_has vpos_ready (after_answer R n1 n2) (after_answer S n2 n3) v) -> *)
  (*   vcomp_at_answer_has m1 m2 m3 xn2 R S (rc_answer m1 m3 n1 n3 v). *)

  Program Definition vcomp_at_question m2 {i j k}
    (R: rc E1 E2 i) (S: rc E2 E3 j) : rc E1 E3 k :=
    {| Downset.has w := vcomp_at_question_has m2 R S w |}.
  Next Obligation. Admitted.

  Lemma vcomp_after_question m1 m2 m3 R S:
    match_question R m1 m2 ->
    match_question S m2 m3 ->
    after_question (vcomp_at_question m2 R S) m1 m3 =
      vcomp_when (vpos_pending m1 m2 m3) (after_question R m1 m2) (after_question S m2 m3).
  Admitted.

  Program Definition vcomp_at_answer m1 m2 m3 (n2: option (ar m2))
    {i j k} (R: rc E1 E2 i) (S: rc E2 E3 j) : rc E1 E3 k :=
    {| Downset.has w := vcomp_at_answer_has m1 m2 m3 n2 R S w |}.
  Next Obligation. Admitted.

  Lemma vcomp_after_answer m1 m2 m3 (n1: ar m1) (n2: ar m2) (n3: ar m3) R S :
    match_answer R n1 n2 ->
    match_answer S n2 n3 ->
    after_answer (vcomp_at_answer m1 m2 m3 (Some n2) R S) n1 n3 =
      vcomp_when vpos_ready (after_answer R n1 n2) (after_answer S n2 n3).
  Admitted.

  Lemma vcomp_expand {i j k} (p: vpos i j k) R S :
    vcomp_when p R S =
      match p with
      | vpos_ready => sup m2, vcomp_at_question m2 R S
      | vpos_pending m1 m2 m3 => inf xn2, vcomp_at_answer m1 m2 m3 xn2 R S
      end.
  Admitted.

  Hint Constructors vcomp_has : core.

  Lemma vcomp_sup_l {i j k} (p: vpos i j k) {I} (R: I -> _) S c:
    (exists i, vcomp_has p (R i) S c) <-> vcomp_has p (lsup R) S c.
  Proof.
    split; intros H.
    - revert p R S H. induction c; intros.
      + destruct H as (x & H). dependent destruction H.
        econstructor; cbn; eauto.
      + admit.
      + admit.
      + admit.
    - revert i j p R S H. induction c; intros.
      + dependent destruction H. destruct H as (x & H). eauto.
      + dependent destruction H. 
        destruct (classic (after_question (sup j, R j) m1 m3 = bot)).
        * setoid_rewrite H in H3.
          specialize (H1 H) as (x & H1). exists x.
          econstructor; eauto. admit.
        * rewrite after_question_sup in H3.
          edestruct (IHc _ _ _ _ _ H3) as (x & Hx).
          exists x. econstructor; eauto. intros. admit.
      + dependent destruction H.
        admit.
      + admit.
  Admitted.

  Lemma vcomp_sup_r {i j k} (p: vpos i j k) {I} R (S: I -> _) c:
    (exists i, vcomp_has p R (S i) c) -> vcomp_has p R (lsup S) c.
  Proof. Admitted.

  (* Lemma vcomp_at_question_sup_l m2 {i j k} {I} (R: I -> _) S c: *)
  (*   @vcomp_at_question_has m2 i j k (lsup R) S c -> *)
  (*   exists i, vcomp_at_question_has m2 (R i) S c. *)
  (* Proof. *)
  (*   revert m2 R S. dependent induction c; intros. *)
  (*   - dependent destruction H. *)
  (*     destruct H as (i & H). exists i. constructor; eauto. *)
  (*   - dependent destruction H. *)
  (*     rewrite after_question_sup in H3. *)
  (*     match goal with *)
  (*     | [ H: context C[vcomp_has ?p ?R ?S ?s] |- _ ] => *)
  (*       let P := context C[Downset.has (vcomp_when p R S) s] in change P in H *)
  (*     end. *)
  (*     (* edestruct IHc as (i & Hi). *) *)
  (*   (* - dependent destruction Hc. cbn in H. *) *)
  (*   (*   destruct H as (i & H). exists i. constructor. *) *)
  (* Admitted. *)

End VCOMP.

Notation vcomp := (vcomp_when vpos_ready).

Ltac refold :=
  repeat
    match goal with
    | |- context C[vcomp_has ?p ?R ?S ?s] =>
        let P := context C[Downset.has (vcomp_when p R S) s] in change P
    | [ H: context C[vcomp_has ?p ?R ?S ?s] |- _ ] =>
        let P := context C[Downset.has (vcomp_when p R S) s] in change P in H
    end.

Section VCOMP_ASSOC.

  Context {E1 E2 E3 E4: esig}.
  Variant vvpos :
    forall {p1 p2 p3 p12 p23 p123}, @vpos E1 E2 E3 p1 p2 p12 ->
                                    @vpos E2 E3 E4 p2 p3 p23 ->
                                    @vpos E1 E3 E4 p12 p3 p123 ->
                                    @vpos E1 E2 E4 p1 p23 p123 -> Type :=
    | vvpos_ready : vvpos vpos_ready vpos_ready vpos_ready vpos_ready
    | vvpos_pending m1 m2 m3 m4:
        vvpos (vpos_pending m1 m2 m3) (vpos_pending m2 m3 m4)
              (vpos_pending m1 m3 m4) (vpos_pending m1 m2 m4).

  Hint Constructors vcomp_has : core.

  Lemma vcomp_assoc_when p1 p2 p3 p12 p23 p123
                         (vp12: vpos p1 p2 p12)
                         (vp23: vpos p2 p3 p23)
                         (vp12_3: vpos p12 p3 p123)
                         (vp1_23: vpos p1 p23 p123)
    (R1: rc E1 E2 p1) (R2: rc E2 E3 p2) (R3: rc E3 E4 p3)
    (p: vvpos vp12 vp23 vp12_3 vp1_23):
    vcomp_when vp12_3 (vcomp_when vp12 R1 R2) R3 =
      vcomp_when vp1_23 R1 (vcomp_when vp23 R2 R3).
  Proof.
    apply antisymmetry.
    - intros c Hc. rewrite !vcomp_expand. rewrite !vcomp_expand in Hc.
      revert p1 p2 p3 p12 p23 vp12 vp23 vp12_3 vp1_23 p R1 R2 R3 Hc.
      induction c.
      + intros. dependent destruction p. rename m2 into m4.
        destruct Hc as (m3 & Hc). cbn in Hc. dependent destruction Hc.
        destruct H as (m2 & H). cbn in H. dependent destruction H.
        exists m2. econstructor; eauto. exists m3. econstructor; eauto.
      + intros. dependent destruction p. rename m2 into m4.
        destruct Hc as (m3 & Hc). cbn -[lsup] in Hc. dependent destruction Hc.
        rewrite after_question_sup in H3. apply vcomp_sup_l in H3 as (m2 & H3).
        destruct (classic (after_question (sup m2 : E2, vcomp_at_question m2 R1 R2) m1 m3 = bot)) as [HX|HX].
        { admit. }
        exists m2. econstructor; eauto.
        { admit. }
        { admit. }
        rewrite after_question_sup. apply vcomp_sup_r.
        exists m3. rewrite vcomp_after_question. 2-3: admit.
        specialize (IHc _ _ _ _ _ _ _ _ _ (vvpos_pending m1 m2 m3 m4)).
        cbn iota in IHc.
        specialize (IHc (after_question R1 m1 m2) (after_question R2 m2 m3) (after_question R3 m3 m4)).
        refold. rewrite !vcomp_expand. apply IHc. clear IHc.
        rewrite vcomp_after_question in H3. 2-3: admit.
        rewrite !vcomp_expand in H3. eauto.
      + intros. dependent destruction p.
        rename m2 into m4, m4 into m3, m3 into m2. rename n2 into n4.
        intros [n2|].
        2: { constructor; intros; easy. }
        constructor. intros n2' Hn2. inversion Hn2. subst n2'. clear Hn2.
        destruct (classic (Downset.has R1 (rc_answer_top m1 m2 n1 n2))). left; eauto.
        right. intros [n3|].
        2: { constructor; intros; easy. }
        constructor. intros n3' Hn3. inversion Hn3. subst n3'. clear Hn3.
        specialize (Hc (Some n3)). cbn -[linf] in Hc.
        dependent destruction Hc. specialize (H _ eq_refl). destruct H; eauto.
        specialize (H (Some n2)). cbn in H.
        dependent destruction H. specialize (H _ eq_refl). destruct H; eauto. easy.
      + intros. dependent destruction p.
        rename m2 into m4, m4 into m3, m3 into m2. rename n2 into n4.
        specialize (IHc _ _ _ _ _ _ _ _ _ vvpos_ready). cbn iota in IHc.
        intros [n2|].
        2: { constructor; intros; easy. }
        constructor. intros n2' Hn2. inversion Hn2. subst n2'. clear Hn2.
        destruct (classic (Downset.has R1 (rc_answer_top m1 m2 n1 n2))) as [|A].
        left; easy. right.
        destruct (classic (Downset.has (inf xn2 : option (ar m3), vcomp_at_answer m2 m3 m4 xn2 R2 R3) (rc_answer_top m2 m4 n2 n4))) as [|B].
        left; easy. right.
        cbn in B. apply not_all_ex_not in B as (xn3 & B). destruct xn3 as [n3|].
        2: { exfalso. apply B. constructor. intros. easy. }
        specialize (Hc (Some n3)). cbn -[linf] in Hc.
        dependent destruction Hc. specialize (H _ eq_refl). destruct H as [H|[H|H]].
        { cbn in H. admit. }
        { admit. }


  Lemma vcomp_assoc
    (R1: rc E1 E2 rc_ready) (R2: rc E2 E3 rc_ready) (R3: rc E3 E4 rc_ready):
    vcomp (vcomp R1 R2) R3 = vcomp R1 (vcomp R2 R3).
  Proof.
    apply antisymmetry.
    - intros c Hc. cbn in *.
      destruct Hc as (c12 & c3 & (c1 & c2 & H1 & H2 & H12) & H3 & H123).
      edestruct (vcomp_has_assoc_1 c1 c2 c12 c3 c vvpos_ready); eauto.


End VCOMP_ASSOC.

Section RSQ.

  Context {E1 E2 F1 F2: esig}.

  Variant rspos : @position E1 F1 -> @position E2 F2 -> rcpos E1 E2 -> rcpos F1 F2 -> Type :=
    | rspos_ready : rspos ready ready rc_ready rc_ready
    | rspos_running q1 q2:
      rspos (running q1) (running q2) rc_ready (rc_pending q1 q2)
    | rspos_suspended q1 q2 m1 m2:
      rspos (suspended q1 m1) (suspended q2 m2) (rc_pending m1 m2) (rc_pending q1 q2).

  Inductive rsp:
    forall {i1 i2 j1 j2}, rspos i1 i2 j1 j2 -> rc E1 E2 j1 -> rc F1 F2 j2 ->
    @play E1 F1 i1 -> strat E2 F2 i2 -> Prop :=
  | rsp_ready R S τ :
    Downset.has τ pnil_ready ->
    rsp rspos_ready R S pnil_ready τ
  | rsp_oq R S q1 s τ :
    Downset.has τ pnil_ready ->
    (forall q2, match_question S q1 q2 ->
           rsp (rspos_running q1 q2) R (after_question S q1 q2) s (next (oq q2) τ)) ->
    rsp rspos_ready R S (oq q1 :: s) τ
  | rsp_pq R q1 q2 S m1 m2 s τ :
    match_question R m1 m2 ->
    rsp (rspos_suspended q1 q2 m1 m2) (after_question R m1 m2) S s (next (pq m2) τ) ->
    rsp (rspos_running q1 q2) R S (pq m1 :: s) τ
  | rsp_suspended q1 q2 S m1 m2 R τ :
    Downset.has τ (pnil_suspended q2 m2) ->
    rsp (rspos_suspended q1 q2 m1 m2) R S (pnil_suspended q1 m1) τ
  | rsp_oa q1 q2 S m1 m2 R n1 s τ :
    Downset.has τ (pnil_suspended q2 m2) ->
    (forall n2,
        match_answer R n1 n2 ->
        rsp (rspos_running q1 q2) (after_answer R n1 n2) S s (next (oa n2) τ)) ->
    rsp (rspos_suspended q1 q2 m1 m2) R S (oa n1 :: s) τ
  | rsp_pa q1 q2 S r1 r2 R s τ:
    match_answer S r1 r2 ->
    rsp rspos_ready R (after_answer S r1 r2) s (next (pa r2) τ) ->
    rsp (rspos_running q1 q2) R S (pa r1 :: s) τ.

  Definition rsq_when {i1 i2 j1 j2} p
    (R: rc E1 E2 j1) (S: rc F1 F2 j2) (σ: strat E1 F1 i1) (τ: strat E2 F2 i2) : Prop :=
    forall s, Downset.has σ s -> rsp p R S s τ.

  Definition rsq R S σ τ := rsq_when rspos_ready R S σ τ.

  Global Instance rsp_ref {i1 i2 j1 j2}:
    Monotonic (@rsp i1 i2 j1 j2) (- ==> ref ++> ref --> ref --> ref ++> impl).
  Proof.
  Admitted.

End RSQ.



(* Lemma vcomp_after_question {E1 E2 E3} (R: rc E1 E2 rc_ready) (R': rc E2 E3 rc_ready) q1 q2 q3: *)
(*   after_question (vcomp R R') q1 q3 = vcomp_when (vpos_pending q1 q2 q3) (after_question R q1 q2) (after_question R' q2 q3). *)
(* Proof. *)
(*   apply antisymmetry. *)


Section RSVCOMP.

  Context {E1 F1 E2 F2 E3 F3 : esig}.

  Variant rsvpos : forall {p1 p2 p3 v1 v2 v u1 u2 u},
      @vpos E1 E2 E3 v1 v2 v ->
      @vpos F1 F2 F3 u1 u2 u ->
      @rspos E1 E2 F1 F2 p1 p2 v1 u1 ->
      @rspos E2 E3 F2 F3 p2 p3 v2 u2 ->
      @rspos E1 E3 F1 F3 p1 p3 v u -> Type :=
    | rsv_ready:
      rsvpos vpos_ready vpos_ready
        rspos_ready rspos_ready rspos_ready
    | rsv_running q1 q2 q3:
      rsvpos vpos_ready (vpos_pending q1 q2 q3)
        (rspos_running q1 q2) (rspos_running q2 q3) (rspos_running q1 q3)
    | rsv_suspended q1 q2 q3 m1 m2 m3:
      rsvpos (vpos_pending m1 m2 m3) (vpos_pending q1 q2 q3)
        (rspos_suspended q1 q2 m1 m2)
        (rspos_suspended q2 q3 m2 m3)
        (rspos_suspended q1 q3 m1 m3).

  Lemma rsp_vcomp {p1 p2 p3 v1 v2 v u1 u2 u c1 c2 i j k}
    (p: @rsvpos p1 p2 p3 v1 v2 v u1 u2 u c1 c2 i j k)
    R R' S S' s1 σ2 σ3 :
    rsp i R S s1 σ2 ->
    rsq_when j R' S' σ2 σ3 ->
    rsp k (vcomp_when c1 R R') (vcomp_when c2 S S') s1 σ3.
  Proof.
    intros H12 H23. revert p3 v2 v u2 u j k c1 c2 p R' S' σ3 H23.
    induction H12; intros; dependent destruction p.
    - (* ready *)
      pose proof (H23 _ H) as Hnil.
      dependent destruction Hnil.
      constructor; auto.
    - (* incoming question *)
      pose proof (H23 _ H) as Hnil.
      dependent destruction Hnil.
      constructor; auto.
      intros q3 Hq13.
      dependent destruction Hq13; rename m2 into q2.
      + 
      unfold match_question in Hq13. cbn in Hq13.


End RSVCOMP.
