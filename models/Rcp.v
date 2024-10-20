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
  | rc_question_bot (m1: op E1) (m2: op E2): rcplay rc_ready
  | rc_question (m1: op E1) (m2: op E2):
    rcplay (rc_pending m1 m2) -> rcplay rc_ready
  | rc_answer_top m1 m2 (n1: ar m1) (n2: ar m2): rcplay (rc_pending m1 m2)
  | rc_answer m1 m2 (n1: ar m1) (n2: ar m2):
    rcplay rc_ready -> rcplay (rc_pending m1 m2).

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

Section RSQ.

Section VCOMP.

  Context {E1 E2 E3: esig}.
  Variant vpos : rcpos E1 E2 -> rcpos E2 E3 -> rcpos E1 E3 -> Type :=
    | vpos_ready : vpos rc_ready rc_ready rc_ready
    | vpos_pending (m1: op E1) (m2: op E2) (m3: op E3):
        vpos (rc_pending m1 m2) (rc_pending m2 m3) (rc_pending m1 m3).

  Inductive vcomp_has :
    forall {i j k} (p: vpos i j k), rc E1 E2 i -> rc E2 E3 j -> rcplay k -> Prop :=
  | vcomp_question_bot R S m1 m2 m3:
    Downset.has R (rc_question_bot m1 m2) ->
    Downset.has S (rc_question_bot m2 m3) ->
    vcomp_has vpos_ready R S (rc_question_bot m1 m3)
  | vcomp_question R S m1 m2 m3 v:
    Downset.has R (rc_question_bot m1 m2) ->
    Downset.has S (rc_question_bot m2 m3) ->
    vcomp_has (vpos_pending m1 m2 m3) (after_question R m1 m2) (after_question S m2 m3) v ->
    vcomp_has vpos_ready R S (rc_question m1 m3 v)
  | vcomp_answer_top m1 m2 m3 R S n1 n3:
    (forall n2, Downset.has R (rc_answer_top m1 m2 n1 n2) \/
             Downset.has S (rc_answer_top m2 m3 n2 n3)) ->
    vcomp_has (vpos_pending m1 m2 m3) R S (rc_answer_top m1 m3 n1 n3)
  | vcomp_answer m1 m2 m3 R S n1 n3 v:
    (forall n2, Downset.has R (rc_answer_top m1 m2 n1 n2) \/
             Downset.has S (rc_answer_top m2 m3 n2 n3) \/
             vcomp_has vpos_ready (after_answer R n1 n2) (after_answer S n2 n3) v) ->
    vcomp_has (vpos_pending m1 m2 m3) R S (rc_answer m1 m3 n1 n3 v).

  Program Definition vcomp_when {i j k} (p: vpos i j k)
    (R: rc E1 E2 i) (S: rc E2 E3 j) : rc E1 E3 k :=
    {| Downset.has w := vcomp_has p R S w |}.
  Next Obligation. Admitted.

  Inductive vcomp_at_has (m2: op E2):
    forall {i j k} (p: vpos i j k), rc E1 E2 i -> rc E2 E3 j -> rcplay k -> Prop :=
  | vcomp_at_question_bot R S m1 m3:
    Downset.has R (rc_question_bot m1 m2) ->
    Downset.has S (rc_question_bot m2 m3) ->
    vcomp_at_has m2 vpos_ready R S (rc_question_bot m1 m3)
  | vcomp_at_question R S m1 m3 v:
    Downset.has R (rc_question_bot m1 m2) ->
    Downset.has S (rc_question_bot m2 m3) ->
    vcomp_has (vpos_pending m1 m2 m3) (after_question R m1 m2) (after_question S m2 m3) v ->
    vcomp_at_has m2 vpos_ready R S (rc_question m1 m3 v)
  | vcomp_at_answer_top m1 m3 R S n1 n3:
    (forall n2, Downset.has R (rc_answer_top m1 m2 n1 n2) \/
             Downset.has S (rc_answer_top m2 m3 n2 n3)) ->
    vcomp_at_has m2 (vpos_pending m1 m2 m3) R S (rc_answer_top m1 m3 n1 n3)
  | vcomp_at_answer m1 m3 R S n1 n3 v:
    (forall n2, Downset.has R (rc_answer_top m1 m2 n1 n2) \/
             Downset.has S (rc_answer_top m2 m3 n2 n3) \/
             vcomp_has vpos_ready (after_answer R n1 n2) (after_answer S n2 n3) v) ->
    vcomp_at_has m2 (vpos_pending m1 m2 m3) R S (rc_answer m1 m3 n1 n3 v).


End VCOMP.

Notation vcomp := (vcomp_when vpos_ready).

Section VCOMP_ASSOC.

  Context {E1 E2 E3 E4: esig}.
  (* E F G H *)
  Variant vvpos :
    forall {p1 p2 p3 p12 p23 p123}, @vpos E1 E2 E3 p1 p2 p12 ->
                                    @vpos E2 E3 E4 p2 p3 p23 ->
                                    @vpos E1 E3 E4 p12 p3 p123 ->
                                    @vpos E1 E2 E4 p1 p23 p123 -> Type :=
    | vvpos_ready : vvpos vpos_ready vpos_ready vpos_ready vpos_ready
    | vvpos_pending m1 m2 m3 m4:
        vvpos (vpos_pending m1 m2 m3) (vpos_pending m2 m3 m4)
              (vpos_pending m1 m3 m4) (vpos_pending m1 m2 m4).

  Hint Constructors rcplay_ref vcomp_has : core.

(*   Lemma vcomp_has_assoc_1 *)
(*     {p1 p2 p3 p12 p23 p123} *)
(*     {vp12: vpos p1 p2 p12} *)
(*     {vp23: vpos p2 p3 p23} *)
(*     {vp12_3: vpos p12 p3 p123} *)
(*     {vp1_23: vpos p1 p23 p123} c1 c2 c12 c3 c123 *)
(*     (p: vvpos vp12 vp23 vp12_3 vp1_23): *)
(*     vcomp_has vp12 c1 c2 c12 -> *)
(*     vcomp_has vp12_3 c12 c3 c123 -> *)

(* . *)
(*   Proof. *)
(*     intros HA HB. *)
(*     revert p3 p23 p123 vp23 vp12_3 vp1_23 p c3 c123 HB. *)
(*     induction HA; intros; cbn. *)
(*     - dependent destruction p; dependent destruction HB. *)
(*       dependent destruction HC0; eauto. *)
(*     - dependent destruction p; dependent destruction HB. *)
(*       + dependent destruction HC1; eauto. *)
(*       + rename m5 into m4. *)
(*         specialize (IHHA _ _ _ _ _ _ (vvpos_pending m1 m2 m3 m4) _ _ HB) *)
(*           as (c23 & Hc23). *)
(*         dependent destruction v12; eauto. *)
(*         * dependent destruction Hc23. *)
(*           -- eexists (rc_question m2 m4 (rc_answer_top m2 m4 _ _)). split; eauto. *)
(*         * destruct Hc23; eauto. *)
(*     - dependent destruction p; dependent destruction HB; eauto. *)
(*       rename m6 into m4, n0 into n1', n2 into n4. *)
(*       destruct HC as [HC|HC]; dependent destruction HC. *)
(*         destruct HC0 as [HC0|HC0]; dependent destruction HC0; eauto. *)
(*       +  *)

(*     - dependent destruction p; dependent destruction HB; eauto 10. *)
(*     - dependent destruction p; dependent destruction HB; eauto 10. *)
(*     - *)
(*   Admitted. *)

  Lemma vcomp_assoc_when p1 p2 p3 p12 p23 p123
                         (vp12: vpos p1 p2 p12)
                         (vp23: vpos p2 p3 p23)
                         (vp12_3: vpos p12 p3 p123)
                         (vp1_23: vpos p1 p23 p123)
    (R1: rc E1 E2 p1) (R2: rc E2 E3 p2) (R3: rc E3 E4 p3):
    vcomp_when vp12_3 (vcomp_when vp12 R1 R2) R3 =
      vcomp_when vp1_23 R1 (vcomp_when vp23 R2 R3).
  Proof.
    apply antisymmetry.
    - intros c Hc. cbn in *.
      destruct Hc as (c12 & c3 & (c1 & c2 & H1 & H2 & H12) & H3 & H123).
      cbn.

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
