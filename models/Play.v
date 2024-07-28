Require Import structures.Effects.

Set Asymmetric Patterns.

(* Inductive play {E F: esig} (A: Type) : Type := *)
(* | pr: A -> play A *)
(* | prq {A'}: A -> F A' -> play A' -> play A *)
(* | pm {B}: E B -> play A *)
(* | pmn {B}: E B -> B -> play A -> play A. *)

Inductive play {E : esig} {V: Type} :=
| pret: V -> play
| pmove: forall {X}, E X -> play
| pcons: forall {X}, E X -> X -> play -> play.
Arguments play: clear implicits.

Inductive plays {E F : esig} :=
| pnil: plays
| prun: forall {X}, F X -> play E (X * plays) -> plays.
Arguments plays: clear implicits.

Require Import Poset.

Module Downset.
  Record downset {C : poset} :=
    {
      has : C -> Prop;
      closed x y : x [= y -> has y -> has x;
    }.

  Arguments downset : clear implicits.

  Program Definition emb {C : poset} (c : C) : downset C :=
    {|
      has x := ref x c;
    |}.
  Next Obligation. etransitivity; eauto. Qed.
End Downset.

Inductive plays_ref {E F} : plays E F -> plays E F -> Prop := .
Program Definition plays_poset E F : poset :=
  {|
    poset_carrier := plays E F;
    ref := plays_ref;
  |}.
Next Obligation. Admitted.
Next Obligation. Admitted.

Definition s E F := Downset.downset (plays_poset E F).

Definition events (E: esig) := @play E unit.

Inductive run_play {E X}: play E X -> events E -> option X -> Prop :=
| run_pret v : run_play (pret v) (pret tt) (Some v)
| run_pmove {X_m} (m: E X_m) : run_play (pmove m) (pmove m) None
| run_pcons {X'} (m: E X') n p e (v: option X):
  run_play p e v ->
  run_play (pcons m n p) (pcons m n e) v.

Inductive concat_events {E}: events E -> events E -> events E -> Prop :=
| concat_pret e: concat_events (pret tt) e e
| concat_pmove {X} (m: E X) e: concat_events (pmove m) e (pmove m)
| concat_pcons {X} (m: E X) n e1 e2 e:
  concat_events e1 e2 e -> concat_events (pcons m n e1) e2 (pcons m n e).

Inductive run_plays {E F}: plays E F -> events F -> events E -> option (plays E F) -> Prop :=
| runs_nil st: run_plays st (pret tt) (pret tt) (Some st)
| runs_cons' {X} (m_f: F X) play_e es res:
  run_play play_e es res -> run_plays (prun m_f play_e) (pmove m_f) es None
| runs_cons {X} (m_f: F X) n_f play_e st_ef st_ef' es_e1 es_e2 es_e es_f:
  run_play play_e es_e1 (Some (n_f, st_ef)) ->
  run_plays st_ef es_f es_e2 st_ef' ->
  concat_events es_e1 es_e2 es_e ->
  run_plays (prun m_f play_e) (pcons m_f n_f es_f) es_e st_ef'.

Inductive compose_plays {E F G}: plays F G -> plays E F -> plays E G -> Prop :=
| compose_nil st: compose_plays pnil st pnil
| compose_prun {X} play_e play_f es_f es_e (m_g: G X) n_g st_fg' st_ef st_ef' st_eg':
  compose_plays st_fg' st_ef' st_eg' ->
  run_play play_f es_f (Some (n_g, st_fg')) ->
  run_plays st_ef es_f es_e (Some st_ef') ->
  run_play play_e es_e (Some (n_g, st_eg')) ->
  compose_plays (prun m_g play_f) st_ef (prun m_g play_e)
| compose_prun_none {X} play_e play_f es_f es_e (m_g: G X) st_ef res:
  run_play play_f es_f None ->
  run_plays st_ef es_f es_e res ->
  run_play play_e es_e None ->
  compose_plays (prun m_g play_f) st_ef (prun m_g play_e)
| compose_prun_none' {X} play_e play_f es_f es_e (m_g: G X) st_ef res:
  run_play play_f es_f res ->
  run_plays st_ef es_f es_e None ->
  run_play play_e es_e None ->
  compose_plays (prun m_g play_f) st_ef (prun m_g play_e).

Include Downset.

Inductive id_plays {E}: plays E E -> Prop := 
| id_plays_intro {X} (m: E X) n s:
  id_plays s -> id_plays (prun m (pcons m n (pret (n, s)))).

Program Definition id {E}: s E E :=
  {| has p := id_plays p |}.
Next Obligation. Admitted.

Program Definition compose {E F G} (s1: s F G) (s2: s E F): s E G :=
  {|
    has p := exists p1 p2, has s1 p1 /\ has s2 p2 /\ compose_plays p1 p2 p;
  |}.
Next Obligation. Admitted.

Lemma s_ext {E F} (s1 s2: s E F): (forall p, has s1 p <-> has s2 p) -> s1 = s2.
Proof.
Admitted.

From compcert Require Import Coqlib.
Require Import Classical_Prop.

Ltac subst_dep :=
  subst;
  lazymatch goal with
  | H: existT ?P ?x _ = existT ?P ?x _ |- _ =>
      apply inj_pair2 in H; subst_dep
  | _ => idtac
  end.

Lemma plays_left_unit1 {E F} pid (pa: plays E F) pb:
  id_plays pid ->
  compose_plays pid pa pb ->
  pa = pb.
Proof.
  intros Hid Hp. revert pa pb Hp. induction Hid.
  intros. inv Hp.
  - subst_dep. inv H3.
    subst_dep. inv H6.
    subst_dep. f_equal.
    inv H9. specialize (IHHid _ _ H2). subst.
    inv H11.
Admitted.

Lemma left_unit {E F} (t: s E F): compose id t = t.
Proof.
  apply s_ext. intros p. split.
  - intros (p1 & p2 & Hp1 & Hp2 & Hpp).
    cbn in Hp1.
Admitted.

Inductive refconv_play {E F} :=
| refconv_ques: forall {X Y}, E X -> F Y -> refconv_play
| refconv_answ: forall {X Y}, E X -> F Y -> X -> Y -> refconv_play
| refconv_cons: forall {X Y}, E X -> F Y -> X -> Y -> refconv_play -> refconv_play.
Arguments refconv_play: clear implicits.

Inductive refconv_ref {E F} : refconv_play E F -> refconv_play E F -> Prop :=
| ques_ref {X Y} (m1: E X) (m2: F Y) n1 n2 s:
  refconv_ref (refconv_ques m1 m2) (refconv_cons m1 m2 n1 n2 s)
| answ_ref {X Y} (m1: E X) (m2: F Y) n1 n2 s:
  refconv_ref (refconv_cons m1 m2 n1 n2 s) (refconv_answ m1 m2 n1 n2)
| cons_ref {X Y} (m1: E X) (m2: F Y) n1 n2 s1 s2:
  refconv_ref s1 s2 ->
  refconv_ref (refconv_cons m1 m2 n1 n2 s1) (refconv_cons m1 m2 n1 n2 s2).

Program Definition refconv_poset E F : poset :=
  {|
    poset_carrier := refconv_play E F;
    ref := refconv_ref;
  |}.
Next Obligation. Admitted.
Next Obligation. Admitted.

Definition r E F := downset (refconv_poset E F).

Inductive refconv_play_next {E F X Y} (m1: E X) (m2: F Y) (n1: X) (n2: Y):
                             refconv_play E F -> refconv_play E F -> Prop :=
| refconv_play_next_intro s:
  refconv_play_next m1 m2 n1 n2 (refconv_cons m1 m2 n1 n2 s) s.

Program Definition r_next {E F} (rc: r E F)
  {X Y} (m1: E X) (m2: F Y) (n1: X) (n2: Y): r E F :=
  {| has p := exists p', has rc p' /\ refconv_play_next m1 m2 n1 n2 p' p |}.
Next Obligation. Admitted.

Definition match_ques {E F X Y} (rc: r E F) (m1: E X) (m2: F Y) :=
  has rc (refconv_ques m1 m2).

Definition match_answ {E F X Y} (rc: r E F)
  (m1: E X) (m2: F Y) (n1: X) (n2: Y) :=
  not (has rc (refconv_answ m1 m2 n1 n2)).

Definition p X E F := play E (X * plays E F) -> Prop.

Definition initial_state {E F X} (t: s E F) (m: F X) (p: p X E F): Prop :=
  forall p', p p' -> has t (prun m p').
Definition at_external {E F X Y} (p: p X E F) (m: E Y): Prop := p (pmove m).
Definition after_external {E F X Y} (p1: p X E F) (m: E Y) (n: Y) (p2: p X E F): Prop :=
  forall p, p2 p -> p1 (pcons m n p).
Definition final_state {E F X} (p: p X E F) (r: X) (s: s E F): Prop :=
  forall p', has s p' -> p (pret (r, p')).

Section SIM.
  Context {E1 E2 F1 F2: esig}.

  Inductive sim_p {X1 X2} (q1: F1 X1) (q2: F2 X2) (rf: r F1 F2)
    (sim_s: r E1 E2 -> r F1 F2 -> s E1 F1 -> s E2 F2 -> Prop):
    r E1 E2 -> p X1 E1 F1 -> p X2 E2 F2 -> Prop :=
  | sim_p_intro re p1 p2
      (match_final:
        forall r1 s1, final_state p1 r1 s1 ->
        exists r2 s2, final_state p2 r2 s2 /\ match_answ rf q1 q2 r1 r2 /\
        sim_s re rf s1 s2)
      (match_external:
        forall {Y1} (m1: E1 Y1), at_external p1 m1 ->
        exists {Y2} (m2: E2 Y2), at_external p2 m2 /\ match_ques re m1 m2 /\
        forall n1 n2, match_answ re m1 m2 n1 n2 ->
        forall p1', after_external p1 m1 n1 p1' ->
        exists p2', after_external p2 m2 n2 p2' /\
        sim_p q1 q2 rf sim_s (r_next re m1 m2 n1 n2) p1' p2'):
    sim_p q1 q2 rf sim_s re p1 p2.

  Inductive sim_s (re: r E1 E2) (rf: r F1 F2)
    (s1: s E1 F1) (s2: s E2 F2) : Prop :=
  | sim_s_intro
    (match_initial:
      forall {X1 X2} (mf1: F1 X1) (mf2: F2 X2),
        match_ques rf mf1 mf2 ->
      forall p1, initial_state s1 mf1 p1 ->
      exists p2, initial_state s2 mf2 p2 /\
      sim_p mf1 mf2 rf sim_s re p1 p2):
    sim_s re rf s1 s2.

End SIM.

Generalizable All Variables.

Section HCOMP.
  Context `(s1: s F1 G1) `(s2: s E1 F1) `(t1: s F2 G2) `(t2: s E2 F2)
    (re: r E1 E2) (rf: r F1 F2) (rg: r G1 G2)
    (sim1: sim_s rf rg s1 t1) (sim2: sim_s re rf s2 t2).

  Theorem hcomp: sim_s re rg (compose s1 s2) (compose t1 t2).
  Proof.
    constructor. intros * Hq * Hi.
    unfold initial_state in Hi. cbn in Hi.

End HCOMP.
