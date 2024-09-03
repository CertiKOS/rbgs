Require Import structures.Effects.
Require Import Poset.
Require Import Downset.
From structures Require Import Lattice.
From lattices Require Import LatticeProduct.

Set Asymmetric Patterns.

Lemma bot_elim {C: poset} (t: C):
  down t [= bot -> False.
Proof.
  Local Transparent bot. unfold bot.
  intros H. apply Downset.emb_join_prime in H.
  destruct H as ([] & _).
Qed.

Lemma fsup_mor {L M: cdlattice} {f: L -> M} `{Sup.Morphism _ _ f}:
  forall {I} (P : I -> Prop) (M: I -> L), f (sup {x | P x}, M x) = sup {x | P x}, f (M x).
Proof. intros. unfold fsup. eapply Sup.mor. Qed.

Inductive play {E F: esig} (A: Type) : Type :=
| pr: A -> play A
| prq {A'}: A -> F A' -> play A' -> play A
| pm {B}: E B -> play A
| pmn {B}: E B -> B -> play A -> play A.
Arguments play: clear implicits.
Arguments pr {E F A} r.
Arguments prq {E F A A'} r q next.
Arguments pm {E F A B} m.
Arguments pmn {E F A B} m n next.

Inductive play_ref {E F A} : play E F A -> play E F A -> Prop :=
| play_ref_pr1 r:
  play_ref (pr r) (pr r)
| play_ref_pr2 {A'} r (q: F A') next:
  play_ref (pr r) (prq r q next)
| play_ref_prq {A'} r (q: F A') next next':
  play_ref next next' ->
  play_ref (prq r q next) (prq r q next')
| play_ref_pm1 {B} (m: E B):
  play_ref (pm m) (pm m)
| play_ref_pm2 {B} (m: E B) n next:
  play_ref (pm m) (pmn m n next)
| play_ref_pmn {B} (m: E B) n next next':
  play_ref next next' ->
  play_ref (pmn m n next) (pmn m n next').

Lemma play_ref_preo {E F A}: PreOrder (@play_ref E F A).
Admitted.

Lemma play_ref_antisym {E F A}: Antisymmetric _ eq (@play_ref E F A).
Admitted.

Canonical Structure play_poset E F A : poset :=
  {|
    poset_carrier := play E F A;
    ref := play_ref;
    ref_preo := play_ref_preo;
    ref_po := play_ref_antisym;
  |}.

Definition t E F A : cdlattice := downset (play_poset E F A).

Definition s (E F : esig) : cdlattice := pi A, t E F A ^ F A.

Definition initial_state {E F A} (s: s E F) (q: F A): t E F A := s _ q.
Definition at_external {E F A B} (p: t E F A) (m: E B): Prop :=
  down (pm m) [= p.
Definition after_external {E F A B} (p: t E F A) (m: E B) (n: B): t E F A :=
  sup {p' | down (pmn m n p') [= p}, down p'.
Definition at_final {E F A} (p: t E F A) (r: A): Prop :=
  down (pr r) [= p.
Definition after_final {E F A A'} (p: t E F A) (r: A) (q: F A'): t E F A' :=
  sup {p' | down (prq r q p') [= p}, down p'.

Program Fixpoint compose_play2  {E F G A B} (k: B -> s E F -> t E G A) (t2: play E F B): t E G A :=
  match t2 with
  | pm _ m => down (pm m)
  | pmn _ m n p_next =>
      down (pm m) ||
      Downset.map (fun p => pmn m n p) (compose_play2 k p_next)
  | pr r => k r (fun _ _ => bot)
  | prq A r q p_next =>
      k r (fun A' q' => _)
  end.
Next Obligation.
  refine (sup HA: A = A', _). subst A'.
  refine (sup H: q = q', down p_next).
Defined.

Definition compose_t2 {E F G A B} (k: B -> s E F -> t E G A) (t2: t E F B): t E G A :=
  Downset.ext (compose_play2 k) t2.

Fixpoint compose_play1 {E F G A} (s2: s E F) (p1: play F G A): t E G A :=
  match p1 with
  | pr r => down (pr r)
  | prq _ r q p_next =>
      down (pr r) ||
      Downset.map (fun p => prq r q p) (compose_play1 s2 p_next)
  | pm _ m => compose_t2 (fun _ _ => bot) (s2 _ m)
  | pmn _ m n p_next =>
      compose_t2 (fun n' t2' => sup H : n' = n, compose_play1 t2' p_next) (s2 _ m)
  end.

Definition compose_t1 {E F G A} (t1: t F G A) (t2: s E F): t E G A :=
  Downset.ext (compose_play1 t2) t1.

Definition compose {E F G} (s1: s F G) (s2: s E F): s E G :=
  fun A q => compose_t1 (s1 _ q) s2.

Inductive id_play {E A} : E A -> play E E A -> Prop :=
| id_play_intro m m' n p:
  id_play m' p ->
  id_play m (pmn m n (prq n m' p)).

Definition id_t {E A} (q: E A): t E E A :=
  sup p, sup H: id_play q p, down p.

Definition id {E}: s E E := fun A q => id_t q.

From compcert Require Import Coqlib.
Require Import Classical_Prop.

Ltac subst_dep :=
  subst;
  lazymatch goal with
  | H: existT ?P ?x _ = existT ?P ?x _ |- _ =>
      apply inj_pair2 in H; subst_dep
  | _ => idtac
  end.

Lemma left_unit {E F} (t: s E F): compose id t = t.
Proof.
  apply antisymmetry.
  - unfold compose, id. intros A q.
    unfold compose_t1. unfold id_t.
    rewrite Sup.mor. apply sup_iff. intros p.
    rewrite Sup.mor. apply sup_iff. intros H.
    rewrite @Downset.ext_ana. 2: admit.
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


Lemma refconv_ref_preo {E F}: PreOrder (@refconv_ref E F).
Admitted.

Lemma refconv_ref_antisym {E F}: Antisymmetric _ eq (@refconv_ref E F).
Admitted.

Canonical Structure refconv_poset E F : poset :=
  {|
    poset_carrier := refconv_play E F;
    ref := refconv_ref;
    ref_preo := refconv_ref_preo;
    ref_po := refconv_ref_antisym;
  |}.

Definition r E F := downset (refconv_poset E F).

Definition match_ques {E F X Y} (rc: r E F) (m1: E X) (m2: F Y) :=
  down (refconv_ques m1 m2) [= rc.

Definition match_answ {E F X Y} (rc: r E F)
  (m1: E X) (m2: F Y) (n1: X) (n2: Y) :=
  not (down (refconv_answ m1 m2 n1 n2) [= rc).

Program Definition r_next {E F} (rc: r E F)
  {X Y} (m1: E X) (m2: F Y) (n1: X) (n2: Y): r E F :=
  sup s, sup H: down (refconv_cons m1 m2 n1 n2 s) [= rc, down s.

Section SIM.
  Context {E1 E2 F1 F2: esig}.

  Fixpoint sim_play
    {X1 X2} (q1: F1 X1) (q2: F2 X2) (re: r E1 E2)
    (rf: r F1 F2) (p1: play E1 F1 X1) (s2: t E2 F2 X2): Prop :=
    match p1 with
    | pr r1 => exists r2, at_final s2 r2 /\ match_answ rf q1 q2 r1 r2
    | prq X1' r1 q1' p_next =>
        exists r2, at_final s2 r2 /\ match_answ rf q1 q2 r1 r2 /\
        forall X2' (q2': F2 X2'),
        match_ques (r_next rf q1 q2 r1 r2) q1' q2' ->
        sim_play q1' q2' re (r_next rf q1 q2 r1 r2) p_next (after_final s2 r2 q2')
    | pm Y1 m1 => exists Y2 (m2: E2 Y2), at_external s2 m2 /\ match_ques re m1 m2
    | pmn Y1 m1 n1 p_next =>
        exists Y2 (m2: E2 Y2), at_external s2 m2 /\ match_ques re m1 m2 /\
        forall n2, match_answ re m1 m2 n1 n2 ->
        sim_play q1 q2 (r_next re m1 m2 n1 n2) rf p_next (after_external s2 m2 n2)
    end.

  Definition sim_t
    {X1 X2} (q1: F1 X1) (q2: F2 X2) (re: r E1 E2)
    (rf: r F1 F2) (s1: t E1 F1 X1) (s2: t E2 F2 X2): Prop :=
    forall p1, down p1 [= s1 -> sim_play q1 q2 re rf p1 s2.

  (* Inductive sim_t: *)
  (*   forall {X1 X2}, F1 X1 -> F2 X2 -> r E1 E2 -> r F1 F2 -> t E1 F1 X1 -> t E2 F2 X2 -> Prop := *)
  (* | sim_t_intro X1 X2 (q1: F1 X1) (q2: F2 X2) re rf p1 p2 *)
  (*     (match_final: *)
  (*       forall r1, at_final p1 r1 -> *)
  (*       exists r2, at_final p2 r2 /\ match_answ rf q1 q2 r1 r2 /\ *)
  (*       forall {X1' X2'} (q1': F1 X1') (q2': F2 X2'), *)
  (*         match_ques (r_next rf q1 q2 r1 r2) q1' q2' -> *)
  (*       forall p1', after_final p1 r1 q1' p1' -> *)
  (*       exists p2', after_final p2 r2 q2' p2' /\ *)
  (*         sim_t q1' q2' re (r_next rf q1 q2 r1 r2) p1' p2') *)
  (*     (match_external: *)
  (*       forall {Y1} (m1: E1 Y1), at_external p1 m1 -> *)
  (*       exists {Y2} (m2: E2 Y2), at_external p2 m2 /\ match_ques re m1 m2 /\ *)
  (*       forall n1 n2, match_answ re m1 m2 n1 n2 -> *)
  (*       forall p1', after_external p1 m1 n1 p1' -> *)
  (*       exists p2', after_external p2 m2 n2 p2' /\ *)
  (*         sim_t q1 q2 (r_next re m1 m2 n1 n2) rf p1' p2'): *)
  (*   sim_t q1 q2 re rf p1 p2. *)

  Definition sim_s (re: r E1 E2) (rf: r F1 F2)
    (s1: s E1 F1) (s2: s E2 F2) : Prop :=
    forall {X1 X2} (qf1: F1 X1) (qf2: F2 X2), match_ques rf qf1 qf2 ->
    sim_t qf1 qf2 re rf (s1 _ qf1) (s2 _ qf2).

  Instance sim_play_propers {re rf X1 X2} (q1: F1 X1) (q2: F2 X2):
    Proper (play_ref --> ref ==> impl) (sim_play q1 q2 re rf).
  Proof.
    intros p1 p2 Hp. intros t1 t2 Ht. intros H.
    unfold flip in Hp.
    revert X2 t1 t2 Ht q1 q2 re rf H.
    induction Hp; intros.
    - destruct H as (r2 & Hf & Hr). exists r2. split; eauto.
      unfold at_final in *.
      etransitivity; eauto.
    - destruct H as (r2 & Hf & Hr & Hnext). exists r2. split; eauto.
      unfold at_final in *.
      etransitivity; eauto.
    - destruct H as (r2 & Hf & Hr & Hnext).
      exists r2. split. unfold at_final in *; eauto.
      etransitivity; eauto.
      split; eauto.
      intros. eapply IHHp. 2: apply Hnext; eauto.
      unfold after_final.
      apply sup_iff. intros (i & Hi). cbn.
      eapply (fsup_at i). etransitivity; eauto. reflexivity.
    - destruct H as (A2 & m2 & He & Hm).
      eexists _, m2. split; eauto.
      unfold at_external in *. etransitivity; eauto.
    - destruct H as (A2 & m2 & He & Hm & Hnext).
      eexists _, m2. split; eauto.
      unfold at_external in *. etransitivity; eauto.
    - destruct H as (A2 & m2 & He & Hm & Hnext).
      eexists _, m2. split. unfold at_external in *.
      etransitivity; eauto.
      split; eauto.
      intros. eapply IHHp. 2: apply Hnext; eauto.
      unfold after_external.
      apply sup_iff. intros (i & Hi). cbn.
      eapply (fsup_at i). etransitivity; eauto. reflexivity.
  Qed.

  Instance sim_propers {re rf}:
    Proper (ref --> ref ==> impl) (sim_s re rf).
  Proof.
    intros s1 s2 Hs. intros t1 t2 Ht. unfold flip in Hs.
    intros Hp. unfold sim_s. intros * Hq.
    specialize (Hp _ _ _ _ Hq). clear Hq.
    unfold sim_t in *. intros p1 Hp1.
    specialize (Hs X1 qf1).
    eapply sim_play_propers.
    - reflexivity.
    - apply Ht.
    - apply Hp. etransitivity; eauto.
  Qed.

End SIM.

Generalizable All Variables.

Instance prq_mor {E F A A'} (r: A) (q: F A'):
  PosetMorphism (fun a : play E F A' => down (prq r q a)).
Proof.
  constructor. intros x y Hxy.
  apply Downset.emb_mor. constructor; eauto.
Qed.

Instance pmn_mor {E F A B} (m: E B) (n: B):
  PosetMorphism (fun a : play E F A => down (pmn m n a)).
Proof.
  constructor. intros x y Hxy.
  apply Downset.emb_mor. constructor; eauto.
Qed.

Lemma ext_mor' {C: poset} {L: cdlattice} (f g: C -> L)  {Hf: PosetMorphism f} {Hg: PosetMorphism g} t:
  (forall c, f c [= g c) ->
  Downset.ext f t [= Downset.ext g t.
Proof.
  intros Hc.
  pose proof (Downset.emb_join_dense t).
  rewrite H.
  rewrite !fsup_mor.
  apply sup_iff. intros (i & Hi).
  eapply (fsup_at i); eauto. cbn.
  rewrite !Downset.ext_ana. apply Hc.
Qed.


Instance compose_play1_mor {E F G A} (t2: s E F):
  PosetMorphism (@compose_play1 E F G A t2).
Proof.
  constructor. intros x y Hxy.
  induction Hxy; cbn; try easy.
  - apply join_l. reflexivity.
  - unfold Downset.map.
    Local Transparent join. unfold join.
    apply sup_iff. intros b.
    apply (sup_at b). destruct b. reflexivity.
    rewrite IHHxy. easy.
  - unfold compose_t2. eapply ext_mor'.
    admit. admit. admit.
  - admit.
Admitted.

Instance compose_play2_mor {E F G A B} (k: B -> s E F -> t E G A):
  PosetMorphism (@compose_play2 E F G A B k).
Proof.
Admitted.

(* Instance compose_play2_mor {E F G A B} (k: B -> s E F -> t E G A): *)
(*   (forall b, PosetMorphism (k b)) -> *)
(*   PosetMorphism (@compose_play2 E F G A B k). *)
(* Proof. *)
(*   intros Hk. constructor. intros x y Hxy. *)
(*   induction Hxy; try easy. *)
(*   - cbn. apply Hk. *)
(*     intros X x. apply bot_lb. *)
(*   - cbn. apply Hk. *)
(*     intros X x. *)
(*     unfold compose_play2_obligation_1. *)
(*     apply sup_iff. intros <-. *)
(*     eapply sup_at. Unshelve. 2: reflexivity. *)
(*     unfold eq_rect. *)
(*     apply sup_iff. intros <-. *)
(*     eapply sup_at. reflexivity. *)
(*     apply Downset.emb_mor. apply Hxy. *)
(*   - cbn. *)
(*     admit. *)
(*   - cbn. unfold Downset.map. *)
(*     rewrite IHHxy. reflexivity. *)
(*     apply Hk. *)
(* Abort. *)

Section HCOMP.

  Lemma map_prq_elim A A' `(s: t E F A')
    (p: play E F A) (r: A) (q: F A'):
    down p [= Downset.map (fun p => prq r q p) s ->
    exists next, p [= prq r q next /\ down next [= s.
  Proof.
    intros Hp. unfold Downset.map in Hp.
    pose proof (Downset.emb_join_dense s).
    rewrite H in Hp. clear H.
    setoid_rewrite Sup.mor in Hp.
    apply Downset.emb_join_prime in Hp.
    destruct Hp as ((i & Hi) & Hp). cbn in Hp.
    rewrite Downset.ext_ana in Hp. 
    apply (iff_sym (Downset.emb_mor _ _)) in Hp.
    exists i. split; eauto.
  Qed.

  Lemma map_pmn_elim A B `(s: t E F A)
    (p: play E F A) (m: E B) (n: B):
    down p [= Downset.map (fun p => pmn m n p) s ->
    exists next, p [= pmn m n next /\ down next [= s.
  Proof.
    intros Hp. unfold Downset.map in Hp.
    pose proof (Downset.emb_join_dense s).
    rewrite H in Hp. clear H.
    setoid_rewrite Sup.mor in Hp. 
    apply Downset.emb_join_prime in Hp.
    destruct Hp as ((i & Hi) & Hp). cbn in Hp.
    rewrite Downset.ext_ana in Hp.
    apply (iff_sym (Downset.emb_mor _ _)) in Hp.
    exists i. split; eauto.
  Qed.

  Lemma at_final_intro_t `(t1: t F G A) `(t2: s E F) r:
    at_final t1 r -> at_final (compose_t1 t1 t2) r.
  Proof.
    unfold at_final, compose_t1. intros Hp.
    rewrite <- Hp. rewrite Downset.ext_ana. 
    cbn. reflexivity.
  Qed.

  Lemma after_final_compose_t
    `(t1: t F G X) `(t2: s E F) r1 `(q2: G X'):
    (compose_t1 (after_final t1 r1 q2) t2) [=
      after_final (compose_t1 t1 t2) r1 q2.
  Proof.
    unfold after_final.
    unfold compose_t1 at 1. rewrite fsup_mor.
    apply sup_iff. intros (i & Hi). cbn.
    rewrite Downset.ext_ana.
    pose proof (Downset.emb_join_dense (compose_play1 t2 i)) as Hp.
    rewrite Hp. apply sup_iff. intros (k & Hk). cbn.
    apply (fsup_at k). 2: reflexivity.
    unfold compose_t1. rewrite <- Hi.
    rewrite Downset.ext_ana. cbn.
    apply join_r.
    unfold Downset.map. rewrite <- Hk.
    rewrite Downset.ext_ana. cbn. reflexivity.
  Qed.

  Lemma at_external_compose_t `(p: t F G A) {E X Y} (s: s E F) (m0: F X) (m: E Y):
    at_external (s X m0) m ->
    at_external p m0 ->
    at_external (compose_t1 p s) m.
  Proof.
    unfold at_external, compose_t1.
    intros Hp1 Hp2.
    rewrite <- Hp2. rewrite Downset.ext_ana. cbn.
    unfold compose_t2. rewrite <- Hp1.
    rewrite Downset.ext_ana. cbn. reflexivity.
  Qed.

  Definition filter_m `(p: t F G A): t F G A :=
    sup { p' | (exists B (m: F B), pm m [= p') /\ down p' [= p }, down p'.

  Lemma filter_m_at_external `(p: t E F A) `(m: E B):
    at_external p m ->
    at_external (filter_m p) m.
  Proof.
    unfold at_external, filter_m.
    intros. apply (fsup_at (pm m)); try easy.
    split; eauto. eexists _, m. easy.
  Qed.

  Lemma filter_m_after_external `(p: t E F A) `(m: E B) n:
    after_external p m n =
    after_external (filter_m p) m n.
  Proof.
    unfold after_external, filter_m.
    apply antisymmetry.
    - apply sup_iff. intros (x & Hx). cbn.
      apply (fsup_at x); try easy.
      apply (fsup_at (pmn m n x)); try easy.
      split; eauto. eexists _, m. constructor.
    - apply sup_iff. intros (x & Hx). cbn.
      apply (fsup_at x); try easy.
      apply Downset.emb_join_prime in Hx as ((i & Hi) & Hk).
      cbn in Hk. destruct Hi.
      etransitivity; eauto.
  Qed.

  Lemma after_external_compose_t `(p: t F G A) {E X} (s: s E F) (m: E X) n:
    compose_t1 (filter_m p) (fun Y q => after_external (s _ q) m n) [=
    after_external (compose_t1 p s) m n.
  Proof.
    unfold compose_t1 at 1, filter_m.
    setoid_rewrite Sup.mor. apply sup_iff.
    intros (i & Ha & Hb). cbn. rewrite Downset.ext_ana. 
    destruct Ha as (? & q & Hq).
    pose proof (Downset.emb_join_dense (compose_play1 (fun (Y : Type) (q0 : F Y) => after_external (s Y q0) m n) i)) as Hp.
    rewrite Hp. apply sup_iff. intros (k & Hk). cbn.
    unfold after_external.
    apply (fsup_at k). 2: reflexivity.
    unfold compose_t1.
    rewrite <- Hb. rewrite Downset.ext_ana. cbn.
    inv Hq; subst_dep; cbn.
    - cbn in Hk. unfold compose_t2 in Hk.
      setoid_rewrite Sup.mor in Hk.
      apply Downset.emb_join_prime in Hk as ((i & Hi) & Hk).
      rewrite Downset.ext_ana in Hk. cbn in Hk.
      unfold compose_t2. rewrite <- Hi.
      rewrite Downset.ext_ana. cbn.
      unfold Downset.map. apply join_r. rewrite <- Hk.
      rewrite Downset.ext_ana. reflexivity.
    - cbn in Hk. unfold compose_t2 in Hk.
      setoid_rewrite Sup.mor in Hk.
      apply Downset.emb_join_prime in Hk as ((i & Hi) & Hk).
      rewrite Downset.ext_ana in Hk. cbn in Hk.
      unfold compose_t2. rewrite <- Hi.
      rewrite Downset.ext_ana. cbn.
      unfold Downset.map. apply join_r. rewrite <- Hk.
      rewrite Downset.ext_ana. reflexivity.
  Qed.

  Lemma at_final_compose2 `(t1: t F G A) `(t2: s E F) `(m: F B) n r:
    at_final (after_external t1 m n) r ->
    at_final (t2 _ m) n ->
    at_final (compose_t1 t1 t2) r.
  Proof.
    intros H1 H2. unfold at_final, after_external in *.
    apply Downset.emb_join_prime in H1.
    destruct H1 as ((i & Hi) & Hp). cbn in Hp.
    apply (iff_sym (Downset.emb_mor _ _)) in Hp.
    unfold compose_t1. rewrite <- Hi.
    rewrite Downset.ext_ana. cbn.
    unfold compose_t2. rewrite <- H2.
    rewrite Downset.ext_ana. cbn.
    assert (Hn: n = n) by reflexivity.
    apply (sup_at Hn).
    inv Hp; cbn. reflexivity.
    apply join_l. reflexivity.
  Qed.

  Definition filter_r `(p: t F G A): t F G A :=
    sup { p' | (exists r, pr r [= p') /\ down p' [= p }, down p'.

  Lemma after_external_compose_t2 `(p: t F G A) `(t2: s E F) `(m1: F B) n1:
    at_final (t2 _ m1) n1 ->
    compose_t1 (after_external p m1 n1)
      (fun X (m2 : F X) => after_final (t2 _ m1) n1 m2) [= compose_t1 p t2.
  Proof.
    assert (filter_r (t2 _ m1) [= t2 _ m1) as Ht2.
    { unfold filter_r. apply sup_iff. intros (i & Hi). cbn. apply Hi. }
    intros Hf. unfold compose_t1 at 1.
    unfold after_external.
    setoid_rewrite Sup.mor. apply sup_iff. intros (i & Hi). cbn.
    rewrite Downset.ext_ana. 
    unfold compose_t1. rewrite <- Hi. clear Hi.
    rewrite Downset.ext_ana. 
    cbn. unfold compose_t2. rewrite <- Ht2.  clear Ht2.
    clear p. induction i.
    - cbn. unfold filter_r.
      rewrite fsup_mor. eapply (fsup_at (pr n1)).
      split. exists n1. reflexivity. apply Hf.
      rewrite Downset.ext_ana. 
      cbn. eapply sup_at. reflexivity. reflexivity.
    - cbn. apply join_lub.
      {
        unfold filter_r.
        rewrite fsup_mor. eapply (fsup_at (pr n1)).
        split. exists n1. reflexivity. apply Hf.
        rewrite Downset.ext_ana.
        cbn. eapply sup_at. reflexivity.
        apply join_l. reflexivity.
      }
      unfold Downset.map. rewrite IHi. clear IHi.
      rewrite @Downset.ext_ext. 2-3: typeclasses eauto.
      unfold filter_r.
      setoid_rewrite Sup.mor.
      apply sup_iff. intros (x & Hx). apply (sup_at (exist _ x Hx)).
      cbn. rewrite !@Downset.ext_ana. 2: typeclasses eauto.
      2: {
        clear. constructor. intros x y Hxy.
        rstep. apply compose_play2_mor. eauto. }
      destruct Hx as ((r & Hr) & Hb). inv Hr.
      + cbn.
        rewrite Sup.mor. apply sup_iff. intros <-.
        eapply sup_at. reflexivity. apply join_r. reflexivity.
      + cbn.
        rewrite Sup.mor. apply sup_iff. intros <-.
        eapply sup_at. reflexivity. apply join_r. reflexivity.
    - cbn. unfold after_final.
      unfold compose_t2.
      rewrite fsup_mor. apply sup_iff.
      intros (x & Hx). cbn.
      rewrite Downset.ext_ana. 
      unfold filter_r.
      rewrite fsup_mor. eapply (fsup_at (prq n1 e x)).
      split. exists n1. constructor. apply Hx.
      rewrite Downset.ext_ana. 
      cbn. eapply sup_at. reflexivity.
      unfold compose_play2_obligation_1.
      rewrite Sup.mor. eapply sup_at. Unshelve. 2: reflexivity.
      unfold eq_rect. rewrite Sup.mor. eapply sup_at.
      reflexivity.
      rewrite Downset.ext_ana. 
      reflexivity.
    - cbn. unfold after_final.
      unfold compose_t2.
      rewrite fsup_mor. apply sup_iff.
      intros (x & Hx). cbn.
      rewrite Downset.ext_ana.
      unfold filter_r.
      rewrite fsup_mor. eapply (fsup_at (prq n1 e x)).
      split. exists n1. constructor. apply Hx.
      rewrite Downset.ext_ana. 
      cbn. eapply sup_at. reflexivity.
      unfold compose_play2_obligation_1.
      rewrite Sup.mor. eapply sup_at. Unshelve. 2: reflexivity.
      unfold eq_rect. rewrite Sup.mor. eapply sup_at.
      reflexivity.
      rewrite Downset.ext_ana.
      reflexivity.
  Qed.

  Context `(s1: s F1 G1) `(s2: s E1 F1) `(t1: s F2 G2) `(t2: s E2 F2)
    (re: r E1 E2) (rf: r F1 F2) (rg: r G1 G2)
    (sim1: sim_s rf rg s1 t1) (sim2: sim_s re rf s2 t2).

  Theorem hcomp: sim_s re rg (compose s1 s2) (compose t1 t2).
  Proof.
    unfold sim_s. intros X1 X2 qg1 qg2 Hqg.
    specialize (sim1 _ _ qg1 qg2 Hqg).
    intros p1 Hp1. cbn in p1.
    unfold compose in Hp1. unfold compose_t1 in Hp1.
    pose proof (Downset.emb_join_dense (s1 X1 qg1)).
    rewrite H in Hp1. setoid_rewrite Sup.mor in Hp1.
    apply Downset.emb_join_prime in Hp1.
    destruct Hp1 as ((c & Hc) & Hp1). cbn in Hp1.
    rewrite Downset.ext_ana in Hp1. 
    unfold sim_t in sim1. specialize (sim1 _ Hc).
    clear H. clear Hc.
    (* we could also induction on p1? *)
    revert rf  sim1 re t2 sim2.
    unfold compose. generalize (t1 X2 qg2).
    revert X2 qg2 qg1 rg Hqg s2 Hp1.
    induction c.
    - intros. cbn in sim1. cbn in Hp1.
      apply (iff_sym (Downset.emb_mor _ _)) in Hp1.
      inv Hp1. cbn.
      destruct sim1 as (r2 & Hf2 & Hr2).
      exists r2. split; eauto.
      apply at_final_intro_t. eauto.
    - intros.
      cbn in sim1. destruct sim1 as (r2 & Hf2 & Hr2 & Hnext).
      clear sim1. cbn in Hp1.
      Local Transparent join. unfold join in Hp1.
      apply Downset.emb_join_prime in Hp1 as (i & Hp1).
      destruct i.
      {
        (* duplicate proof *)
        apply (iff_sym (Downset.emb_mor _ _)) in Hp1.
        inv Hp1. cbn.
        exists r2. split; eauto.
        apply at_final_intro_t. eauto.
      }
      apply map_prq_elim in Hp1 as (_next & Hp1 & Hpnext).
      inv Hp1.
      + subst_dep. cbn.
        exists r2. split; eauto.
        apply at_final_intro_t. eauto.
      + subst_dep. cbn.
        exists r2. split. apply at_final_intro_t. eauto.
        split. eauto.
        intros X2' q2' Hq2. specialize (Hnext _ _ Hq2).
        eapply sim_play_propers. reflexivity.
        apply after_final_compose_t.
        exploit (IHc next0). apply Hq2. 2: apply Hnext. 2: apply sim2.
        etransitivity; eauto. apply Downset.emb_mor; eauto.
        tauto.
    - intros. cbn in sim1.
      destruct sim1 as (Y1 & m1 & He1 & Hm1). clear sim1.
      cbn in Hp1.
      unfold sim_s in sim2. specialize (sim2 _ _ _ _ Hm1).
      unfold compose_t2 in Hp1.
      pose proof (Downset.emb_join_dense (s2 B e)).
      rewrite H in Hp1. setoid_rewrite Sup.mor in Hp1.
      apply Downset.emb_join_prime in Hp1.
      destruct Hp1 as ((c & Hc) & Hp1). cbn in Hp1.
      rewrite Downset.ext_ana in Hp1. 
      specialize (sim2 _ Hc).
      clear Hc Hqg H Hm1. revert t2 p1 re sim2 Hp1.
      revert p He1.
      induction c; intros.
      + cbn in Hp1. apply bot_elim in Hp1. inv Hp1.
      + cbn in Hp1. apply bot_elim in Hp1. inv Hp1.
      + cbn in Hp1. apply (iff_sym (Downset.emb_mor _ _)) in Hp1.
        inv Hp1. subst_dep. cbn.
        cbn in sim2. destruct sim2 as (Y2 & m2 & He2 & Hm2).
        exists Y2, m2. split; eauto.
        eapply at_external_compose_t; eauto.
      + cbn in Hp1.
        apply Downset.emb_join_prime in Hp1 as (i & Hp1).
        destruct i.
        {
          (* duplicate proof *)
          apply (iff_sym (Downset.emb_mor _ _)) in Hp1.
          inv Hp1. subst_dep. cbn.
          destruct sim2 as (Y2 & m2 & He2 & Hm2 & Hnext2).
          exists Y2, m2. split; eauto.
          eapply at_external_compose_t; eauto.
        }
        apply map_pmn_elim in Hp1 as (_next & Hp1 & Hpnext).
        inv Hp1.
        * subst_dep. cbn in sim2.
          destruct sim2 as (Y2 & m2 & He2 & Hm2 & ?). clear sim2.
          exists Y2, m2. split; eauto.
          eapply at_external_compose_t; eauto.
        * subst_dep. cbn in sim2.
          destruct sim2 as (Y2 & m2 & He2 & Hm2 & Hnext2). clear sim2.
          cbn. exists Y2, m2. split; eauto.
          eapply at_external_compose_t; eauto.
          split. apply Hm2.
          intros n2 Hn2. specialize (Hnext2 _ Hn2).
          set (next_t2 := fun A q => after_external (t2 A q) m2 n2).
          assert (He3: at_external (filter_m p) m1).
          apply filter_m_at_external. eauto.
          specialize (IHc e (filter_m p) He3 next_t2).
          (* TODO: rewrite *)
          eapply sim_play_propers. reflexivity. apply after_external_compose_t.
          apply IHc. apply Hnext2.
          etransitivity; eauto. apply Downset.emb_mor. eauto.
    - intros. cbn in sim1.
      destruct sim1 as (Y1 & m1 & He1 & Hm1 & Hnext1). clear sim1.
      unfold sim_s in sim2. specialize (sim2 _ _ _ _ Hm1).
      cbn in Hp1. unfold compose_t2 in Hp1.
      pose proof (Downset.emb_join_dense (s2 B e)).
      rewrite H in Hp1. setoid_rewrite Sup.mor in Hp1. 
      apply Downset.emb_join_prime in Hp1.
      destruct Hp1 as ((d & Hd) & Hp1). cbn in Hp1.
      rewrite Downset.ext_ana in Hp1. 
      specialize (sim2 _ Hd). clear Hd. clear H.
      revert p1 b Hp1 t2 re sim2 Hnext1.
      revert p He1.
      (* induction on s2's behavior *)
      induction d; intros.
      + (* s1 calls s2, and s2 returns and terminates with no further states. *)
        cbn in Hp1.
        apply Downset.emb_join_prime in Hp1.
        destruct Hp1 as (Hb & Hp1). subst.
        cbn in sim2. destruct sim2 as (r2 & Hf2 & Hr2).
        clear sim2. specialize (Hnext1 _ Hr2).
        specialize (IHc p1 _ _ _ _ Hqg _ Hp1 _ _ Hnext1).
        exploit IHc.
        { unfold sim_s. intros. unfold sim_t. intros.
          apply bot_elim in H0. inv H0. }
        intros HX.
        (* My guess is compose_t1 (after_external p m1 r2) ?Goal6 = compose_t1 p t2 *)
        eapply sim_play_propers. reflexivity.
        apply after_external_compose_t2. apply Hf2. apply HX.
      + (* s1 calls s2, and s2 returns, and the execution goes on. *)
        cbn in Hp1.
        apply Downset.emb_join_prime in Hp1.
        destruct Hp1 as (Hb & Hp1). subst.
        cbn in sim2. destruct sim2 as (r2 & Hf2 & Hr2 & Hnext2).
        clear sim2. specialize (Hnext1 _ Hr2).
        unfold compose_play2_obligation_1 in Hp1.
        specialize (IHc p1 _ _ _ _ Hqg _ Hp1 _ _ Hnext1).
        exploit IHc.
        {
          unfold sim_s. intros * Hq.
          unfold sim_t. intros * Hp0.
          apply Downset.emb_join_prime in Hp0.
          destruct Hp0 as (HA & Hp0). subst.
          unfold eq_rect in Hp0.
          apply Downset.emb_join_prime in Hp0.
          destruct Hp0 as (Hf & Hp0). subst.
          apply (iff_sym (Downset.emb_mor _ _)) in Hp0.
          (* TODO: rewrite not work.. *)
          eapply sim_play_propers. apply Hp0. reflexivity.
          apply Hnext2. apply Hq.
        }
        intros HX.
        eapply sim_play_propers. reflexivity.
        apply after_external_compose_t2. apply Hf2. apply HX.
      + cbn in Hp1. apply (iff_sym (Downset.emb_mor _ _)) in Hp1.
        inv Hp1. subst_dep. cbn.
        cbn in sim2. destruct sim2 as (Y2 & m2 & He2 & Hm2).
        exists Y2, m2. split; eauto. eapply at_external_compose_t; eauto.
      + cbn in Hp1.
        apply Downset.emb_join_prime in Hp1 as (i & Hp1).
        destruct i.
        {
          (* duplicate proof *)
          apply (iff_sym (Downset.emb_mor _ _)) in Hp1.
          inv Hp1. subst_dep. cbn.
          destruct sim2 as (Y2 & m2 & He2 & Hm2 & Hnext2).
          exists Y2, m2. split; eauto.
          eapply at_external_compose_t; eauto.
        }
        apply map_pmn_elim in Hp1 as (next_ & Hp1 & Hpnext).
        destruct sim2 as (Y2 & m2 & He2 & Hm2 & Hnext2). clear sim2.
        inv Hp1.
        * subst_dep. cbn. exists Y2, m2. split; eauto.
          eapply at_external_compose_t; eauto.
        * subst_dep. cbn. exists Y2, m2.
          split. eapply at_external_compose_t; eauto.
          split. eauto.
          intros n2 Hn2. specialize (Hnext2 _ Hn2).
          eapply sim_play_propers. reflexivity. apply after_external_compose_t.
          specialize (IHd _ Hm1).
          assert (He3: at_external (filter_m p) m1).
          apply filter_m_at_external. eauto.
          specialize (IHd _ He3).
          specialize (IHd _ _ Hpnext).
          (* TODO: rewrite not work.. *)
          eapply sim_play_propers. apply H1. reflexivity.
          apply IHd. apply Hnext2.
          intros n1 Hn1. rewrite <- filter_m_after_external.
          apply Hnext1. eauto.
  Qed.

End HCOMP.

