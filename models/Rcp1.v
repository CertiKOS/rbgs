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

  Inductive rcplay {I: Type} {J: I -> Type} : rcpos -> Type :=
  | rc_question_bot (i: I) (m1: op E1) (m2: op E2): rcplay rc_ready
  | rc_question (i: I) (m1: op E1) (m2: op E2):
    rcplay (rc_pending m1 m2) -> rcplay rc_ready
  | rc_answer_top (i: I) (j: J i) m1 m2 (n1: ar m1) (n2: ar m2): rcplay  (rc_pending m1 m2)
  | rc_answer (i: I) (j: J i) m1 m2 (n1: ar m1) (n2: ar m2):
    rcplay rc_ready -> rcplay (rc_pending m1 m2).

  Inductive rcplay_ref {I: Type} {J: I -> Type} : forall {p: rcpos}, @rcplay I J p -> @rcplay I J p -> Prop := 
  | rcplay_question_ref1 m1 m2 i:
    rcplay_ref (rc_question_bot i m1 m2) (rc_question_bot i m1 m2)
  | rcplay_question_ref2 m1 m2 s i:
    rcplay_ref (rc_question_bot i m1 m2) (rc_question i m1 m2 s)
  | rcplay_question_cont_ref m1 m2 s1 s2 i:
    rcplay_ref s1 s2 ->
    rcplay_ref (rc_question i m1 m2 s1) (rc_question i m1 m2 s2)
  | rcplay_answer_ref1 m1 m2 n1 n2 i j:
    rcplay_ref (rc_answer_top i j m1 m2 n1 n2) (rc_answer_top i j m1 m2 n1 n2)
  | rcplay_answer_ref2 m1 m2 n1 n2 s i j:
    rcplay_ref (rc_answer i j m1 m2 n1 n2 s) (rc_answer_top i j m1 m2 n1 n2)
  | rcplay_answer_cont_ref m1 m2 n1 n2 s1 s2 i j:
    rcplay_ref s1 s2 ->
    rcplay_ref (rc_answer i j m1 m2 n1 n2 s1) (rc_answer i j m1 m2 n1 n2 s2).

  Program Canonical Structure rcplay_poset I J (p : rcpos) : poset :=
    {|
      poset_carrier := @rcplay I J p;
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
    induction Hw12; dependent destruction Hw21;
      intros A B; dependent destruction A; dependent destruction B;
      firstorder congruence.
  Qed.

  Definition rc I J p := poset_carrier (downset (rcplay_poset I J p)).

  Record irc :=
    {
      question_index: Type;
      answer_index: question_index -> Type;
      rc_carrier: rc question_index answer_index rc_ready;
    }.

  Program Definition after_question {I J} (R: rc I J rc_ready) i q1 q2 : rc I J (rc_pending q1 q2) :=
    {| Downset.has s := Downset.has R (rc_question i q1 q2 s) |}.
  Next Obligation.
    intros * Hxy Hy. eapply Downset.closed; eauto.
    constructor; auto.
  Qed.

  Program Definition after_answer {I J} {i} {q1: op E1} {q2: op E2}
    (R: rc I J (rc_pending q1 q2)) j (n1: ar q1) (n2: ar q2)  : rc I J rc_ready :=
    {| Downset.has s := Downset.has R (rc_answer i j q1 q2 n1 n2 s) |}.
  Next Obligation.
    intros * Hxy Hy. eapply Downset.closed; eauto.
    constructor; auto.
  Qed.

End RC.

Arguments rcpos : clear implicits.
Arguments rc : clear implicits.
Arguments irc : clear implicits.
Arguments rc_ready {E1 E2}.
Arguments rc_pending {E1 E2} _ _.

Section REF.
  Context {E1 E2: esig}.

  Inductive irc_ref {I1 I2: Type} {J1: I1 -> Type} {J2: I2 -> Type}:
    forall {p: rcpos E1 E2}, @rcplay E1 E2 I1 J1 p -> @rcplay E1 E2 I2 J2 p -> Prop := .


  (* Definition irc_eqv (R: irc E1 E2) (S: irc E1 E2): Prop := *)
  (*   irc_ref (rc_carrier R) (rc_carrier S). *)

End REF.

Section VCOMP.

  Context {E1 E2 E3: esig} (IR: irc E1 E2) (IS: irc E2 E3).
  Variant vpos : rcpos E1 E2 -> rcpos E2 E3 -> rcpos E1 E3 -> Type :=
    | vpos_ready : vpos rc_ready rc_ready rc_ready
    | vpos_pending (m1: op E1) (m2: op E2) (m3: op E3):
        vpos (rc_pending m1 m2) (rc_pending m2 m3) (rc_pending m1 m3).

  Let RI := question_index IR.
  Let RJ := answer_index IR.
  Let SI := question_index IS.
  Let SJ := answer_index IS.
  Let I := (RI * SI * op E2)%type.
  Let J : I -> Type := fun '(ri, si, m2) => (RJ ri * SJ si * ar m2)%type.

  Inductive vcomp_has:
    forall {i j k} (p: vpos i j k),
      rc E1 E2 RI RJ i -> rc E2 E3 SI SJ j -> @rcplay E1 E3 I J k -> Prop :=
  | vcomp_question_bot R S ri si m1 m2 m3:
    Downset.has R (rc_question_bot ri m1 m2) ->
    Downset.has S (rc_question_bot si m2 m3) ->
    vcomp_has vpos_ready R S (rc_question_bot (ri, si, m2) m1 m3)
  | vcomp_question R S ri si m1 m2 m3 v:
    Downset.has R (rc_question_bot ri m1 m2) ->
    Downset.has S (rc_question_bot si m2 m3) ->
    vcomp_has (vpos_pending m1 m2 m3)
      (after_question R ri m1 m2) (after_question S si m2 m3) v ->
    vcomp_has vpos_ready R S (rc_question (ri, si, m2) m1 m3 v)
  | vcomp_answer_top ri si m1 m2 m3 R S rj sj n1 n2 n3:
    (Downset.has R (rc_answer_top ri rj m1 m2 n1 n2) \/
       Downset.has S (rc_answer_top si sj m2 m3 n2 n3)) ->
    vcomp_has (vpos_pending m1 m2 m3) R S
      (rc_answer_top (ri, si, m2) (rj, sj, n2) m1 m3 n1 n3)
  | vcomp_answer ri si m1 m2 m3 R S rj sj n1 n2 n3 v:
    ~ Downset.has R (rc_answer_top ri rj m1 m2 n1 n2) ->
    ~ Downset.has S (rc_answer_top si sj m2 m3 n2 n3) ->
    vcomp_has vpos_ready (after_answer R rj n1 n2) (after_answer S sj n2 n3) v ->
    vcomp_has (vpos_pending m1 m2 m3) R S
      (rc_answer (ri, si, m2) (rj, sj, n2) m1 m3 n1 n3 v).

  Program Definition vcomp_when {i j k} (p: vpos i j k)
    (R: rc E1 E2 RI RJ i) (S: rc E2 E3 SI SJ j) : rc E1 E3 I J k :=
    {| Downset.has w := vcomp_has p R S w |}.
  Next Obligation. Admitted.

  Definition ivcomp : irc E1 E3 :=
    {|
      question_index := I;
      answer_index := J;
      rc_carrier := vcomp_when vpos_ready (rc_carrier IR) (rc_carrier IS)
    |}.

End VCOMP.

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

  Context (IR: irc E1 E2) (IS: irc E2 E3) (IT: irc E3 E4).
  Lemma vcomp_assoc_when p1 p2 p3 p12 p23 p123
                         (vp12: vpos p1 p2 p12)
                         (vp23: vpos p2 p3 p23)
                         (vp12_3: vpos p12 p3 p123)
                         (vp1_23: vpos p1 p23 p123)
    (R1: rc E1 E2 p1) (R2: rc E2 E3 p2) (R3: rc E3 E4 p3)
    (p: vvpos vp12 vp23 vp12_3 vp1_23):
    vcomp_when vp12_3 (vcomp_when vp12 R1 R2) R3 =
      vcomp_when vp1_23 R1 (vcomp_when vp23 R2 R3).



End VCOMP_ASSOC.
