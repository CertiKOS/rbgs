Require Import Classical.
Require Import Program.Equality.
Require Import LogicalRelations.
Require Import Poset.
Require Import Lattice.
Require Import Downset.


(** * Preliminaries *)

(** Effect signature *)

Record esig :=
  {
    op :> Type;
    ar : op -> Type;
  }.

Arguments ar {_}.

(** Tactics *)

Ltac xsubst :=
  repeat progress
   (match goal with
    | H : ?x = ?x |- _ =>
      clear H
    | H : existT _ _ _ = existT _ _ _ |- _ =>
      apply inj_pair2 in H
    end;
    subst).


(** * Strategies *)

Section STRAT.
  Context {E F : esig}.

  (** ** Moves *)

  Variant position :=
    | ready
    | running (q : op F)
    | suspended (q : op F) (m : op E).

  Variant move : position -> position -> Type :=
    | oq (q : op F) : move ready (running q)
    | pq {q} (m : op E) : move (running q) (suspended q m)
    | oa {q m} (n : ar m) : move (suspended q m) (running q)
    | pa {q} (r : ar q) : move (running q) ready.

  Inductive play : position -> Type :=
    | pnil_ready : play ready
    | pnil_suspended q m : play (suspended q m)
    | pcons {i j} : move i j -> play j -> play i.

  Inductive pref : forall {i : position}, relation (play i) :=
    | pnil_ready_pref t : pref pnil_ready t
    | pnil_suspended_pref {q m} t : pref (@pnil_suspended q m) t
    | pcons_pref {i j} (e : move i j) s t : pref s t -> pref (pcons e s) (pcons e t).

  Program Canonical Structure play_poset (p : position) : poset :=
    {|
      poset_carrier := play p;
      ref := pref;
    |}.
  Next Obligation.
    split.
    - red. induction x; constructor; auto.
    - intros x y z Hxy Hyz.
      induction Hxy; try constructor;
      inversion Hyz; xsubst; constructor; auto.
  Qed.
  Next Obligation.
    intros x y Hxy Hyx.
    induction Hxy; inversion Hyx; xsubst; auto;
    elim IHHxy; auto.
  Qed.

  Definition strat (p : position) :=
    downset (play_poset p).

  (** ** Determinism *)

  Inductive pcoh : forall {i : position}, relation (play i) :=
    | pnil_ready_pcoh_l s : pcoh pnil_ready s
    | pnil_ready_pcoh_r s : pcoh s pnil_ready
    | pnil_suspended_pcoh_l q m s : pcoh (pnil_suspended q m) s
    | pnil_suspended_pcoh_r q m s : pcoh s (pnil_suspended q m)
    | pcons_pcoh {i j} (m : move i j) (s t : play j) :
        pcoh s t -> pcoh (pcons m s) (pcons m t)
    | pcons_pcoh_oq (q1 q2 : F) s1 s2 :
        q1 <> q2 -> pcoh (pcons (oq q1) s1) (pcons (oq q2) s2)
    | pcons_pcoh_oa {q m} (n1 n2 : ar m) (s1 s2 : play (running q)) :
        n1 <> n2 -> pcoh (pcons (oa n1) s1) (pcons (oa n2) s2).

  Global Instance pcoh_refl i :
    Reflexive (@pcoh i).
  Proof.
    intros s.
    induction s; constructor; auto.
  Qed.

  Global Instance pcoh_sym i :
    Symmetric (@pcoh i).
  Proof.
    intros s t Hst.
    induction Hst; constructor; auto.
  Qed.

  Class Deterministic {p} (σ : strat p) :=
    {
      determinism : forall s t, Downset.has σ s -> Downset.has σ t -> pcoh s t;
    }.

  Lemma pq_determinism {q} (σ : strat (running q)) `{!Deterministic σ} m1 m2 s1 s2 :
    Downset.has σ (pcons (pq m1) s1) ->
    Downset.has σ (pcons (pq m2) s2) ->
    m1 = m2.
  Proof.
    intros H1 H2.
    pose proof (determinism _ _ H1 H2) as H12.
    dependent destruction H12; auto.
  Qed.

  Lemma pa_determinism {q} (σ : strat (running q)) `{!Deterministic σ} r1 r2 s1 s2 :
    Downset.has σ (pcons (pa r1) s1) ->
    Downset.has σ (pcons (pa r2) s2) ->
    r1 = r2.
  Proof.
    intros H1 H2.
    pose proof (determinism _ _ H1 H2) as H12.
    dependent destruction H12; auto.
  Qed.

  (** ** Residuals *)

  Section NEXT.
    Context {i j} (e : move i j).
    Obligation Tactic := cbn.

    Definition scons : strat j -> strat i :=
      Downset.map (pcons e).

    Global Instance scons_deterministic (σ : strat j) :
      Deterministic σ ->
      Deterministic (scons σ).
    Proof.
      intros Hσ. constructor.
      intros s' t' Hs Ht. cbn in *.
      destruct Hs as ((s & Hs) & Hs'); cbn in *.
      destruct Ht as ((t & Ht) & Ht'); cbn in *.
      dependent destruction Hs'; try (constructor; auto).
      dependent destruction Ht'; try (constructor; auto).
      auto using determinism.
    Qed.

    Program Definition next (σ : strat i) : strat j :=
      {| Downset.has s := Downset.has σ (pcons e s) |}.
    Next Obligation.
      intros σ s t Hst.
      apply Downset.closed.
      constructor; auto.
    Qed.

    Global Instance next_deterministic (σ : strat i) :
      Deterministic σ ->
      Deterministic (next σ).
    Proof.
      intros Hσ. constructor.
      intros s t Hs Ht. cbn in *.
      pose proof (determinism _ _ Hs Ht).
      dependent destruction H.
      - assumption.
      - congruence.
      - congruence.
    Qed.

    Lemma scons_next_adj σ τ :
      scons σ [= τ <-> σ [= next τ.
    Proof.
      split.
      - intros H s Hs.
        cbn. apply H.
        unfold scons. cbn.
        pose proof (fun u Hus => Downset.closed σ u s Hus Hs) as Hs'.
        exists (exist _ _ Hs').
        reflexivity.
      - intros H s Hs. cbn in Hs.
        destruct Hs as [[t Ht] Hs]. cbn in Hs.
        apply (Downset.closed _ _ (pcons e t)); auto. clear Hs.
        apply H.
        apply Ht.
        reflexivity.
    Qed.
  End NEXT.
End STRAT.

Arguments strat : clear implicits.
Infix "::" := pcons.

Section ID.
  Context {E : esig}.
  Obligation Tactic := cbn.

  Inductive id_has : forall {p}, @play E E p -> Prop :=
    | id_has_pnil_ready :
        id_has pnil_ready
    | id_has_q m s :
        id_has s ->
        id_has (oq m :: pq m :: s)
    | id_has_pnil_suspended m :
        id_has (@pnil_suspended E E m m)
    | id_has_a {m} (n : ar m) s :
        id_has s ->
        id_has (oa n :: pa n :: s).

  Program Definition id : strat E E ready :=
    {| Downset.has := id_has |}.
  Next Obligation.
  Admitted.
End ID.

Section COMPOSE.
  Context {E F G : esig}.
  Obligation Tactic := cbn.

  Variant cpos : @position F G -> @position E F -> @position E G -> Type :=
    | cpos_ready :
        cpos ready ready ready
    | cpos_left q :
        cpos (running q) ready (running q)
    | cpos_right q m :
        cpos (suspended q m) (running m) (running q)
    | cpos_suspended q m u :
        cpos (suspended q m) (suspended m u) (suspended q u).

  Inductive comp_has :
    forall {i j k} (p: cpos i j k), play i -> play j -> play k -> Prop :=
    | comp_ready t :
        comp_has cpos_ready (pnil_ready) t (pnil_ready)
    | comp_oq q s t w :
        comp_has (cpos_left q) s t w ->
        comp_has cpos_ready (oq q :: s) t (oq q :: w)
    | comp_lq q m s t w :
        comp_has (cpos_right q m) s t w ->
        comp_has (cpos_left q) (pq m :: s) (oq m :: t) w
    | comp_rq q m u s t w :
        comp_has (cpos_suspended q m u) s t w ->
        comp_has (cpos_right q m) s (pq u :: t) (pq u :: w)
    | comp_suspended q m u s :
        comp_has (cpos_suspended q m u) s (pnil_suspended m u) (pnil_suspended q u)
    | comp_oa q m u v s t w :
        comp_has (cpos_right q m) s t w ->
        comp_has (cpos_suspended q m u) s (oa v :: t) (oa v :: w)
    | comp_ra q m n s t w :
        comp_has (cpos_left q) s t w ->
        comp_has (cpos_right q m) (oa n :: s) (pa n :: t) w
    | comp_la q r s t w :
        comp_has cpos_ready s t w ->
        comp_has (cpos_left q) (pa r :: s) t (pa r :: w).

  Hint Constructors comp_has.
  Hint Constructors pref.
  Hint Resolve (reflexivity (R := pref)).

  Lemma comp_has_pref {i j k} (p : cpos i j k) s t w :
    comp_has p s t w ->
    forall w', w' [= w -> exists s' t', s' [= s /\ t' [= t /\ comp_has p s' t' w'.
  Proof.
    induction 1; cbn in *.
    - (* ready *)
      intros w' Hw'.
      inversion Hw'; clear Hw'; xsubst; eauto.
    - (* incoming question *)
      intros w' Hw'.
      dependent destruction w'; eauto.
      inversion Hw'; clear Hw'; xsubst.
      edestruct IHcomp_has as (s' & t' & Hs' & Ht' & Hw'); eauto 10.
    - (* internal question *)
      intros w' Hw'.
      edestruct IHcomp_has as (s' & t' & Hs' & Ht' & Hw''); eauto 10.
    - (* outgoing question *)
      intros w' Hw'.
      dependent destruction w'; eauto.
      inversion Hw'; clear Hw'; xsubst.
      edestruct IHcomp_has as (s' & t' & Hs' & Ht' & Hw'); eauto 10.
    - (* waiting for answer *)
      intros w' Hw'.
      dependent destruction w'; eauto.
      inversion Hw'.
    - (* outgoing question is answered *)
      intros w' Hw'.
      dependent destruction w'; eauto.
      inversion Hw'; clear Hw'; xsubst.
      edestruct IHcomp_has as (s' & t' & Hs' & Ht' & Hw'); eauto 10.
    - (* internal answer *)
      intros w' Hw'.
      edestruct IHcomp_has as (s' & t' & Hs' & Ht' & Hw''); eauto 10.
    - (* incoming question is answered *)
      intros w' Hw'.
      dependent destruction w'; eauto.
      inversion Hw'; clear Hw'; xsubst.
      edestruct IHcomp_has as (s' & t' & Hs' & Ht' & Hw'); eauto 10.
  Qed.

  Program Definition compose {i j k} p (σ : strat F G i) (τ : strat E F j) : strat E G k :=
    {| Downset.has w :=
         exists s t, Downset.has σ s /\ Downset.has τ t /\ comp_has p s t w |}.
  Next Obligation.
    intros i j k p σ τ w' w Hw' (s & t & Hs & Ht & Hw).
    edestruct @comp_has_pref as (s' & t' & Hs' & Ht' & Hw''); try eassumption.
    eauto 10 using Downset.closed.
  Qed.

  Global Instance compose_deterministic {i j k} p σ τ :
    Deterministic σ ->
    Deterministic τ ->
    Deterministic (@compose i j k p σ τ).
  Proof.
    intros Hσ Hτ. constructor.
    intros w1 w2 (s1 & t1 & Hs1 & Ht1 & H1) (s2 & t2 & Hs2 & Ht2 & H2).
    pose proof (determinism s1 s2 Hs1 Hs2) as Hs. clear σ Hs1 Hs2 Hσ.
    pose proof (determinism t1 t2 Ht1 Ht2) as Ht. clear τ Ht1 Ht2 Hτ.
    revert s2 t2 w2 H2 Hs Ht.
    induction H1; intros.
    - constructor.
    - dependent destruction Hs;
      dependent destruction H2;
      constructor; eauto.
    - dependent destruction Hs.
      dependent destruction H2.
      dependent destruction Ht; eauto.
      congruence.
    - dependent destruction Ht.
      dependent destruction H2.
      constructor; eauto.
    - constructor.
    - dependent destruction Ht;
      dependent destruction H2;
      constructor; eauto.
    - dependent destruction Hs;
      dependent destruction H2;
      dependent destruction Ht; eauto.
      congruence.
    - dependent destruction Hs.
      dependent destruction H2.
      constructor; eauto.
  Qed.

  (** Properties of [compose] vs. [next] *)

  Lemma compose_next_oq q σ τ :
    compose (cpos_left q) (next (oq q) σ) τ =
    next (oq q) (compose cpos_ready σ τ).
  Proof.
    apply antisymmetry; cbn.
    - intros w' (s & t & Hs & Ht & Hstw').
      eauto 10.
    - intros w' (s & t & Hs & Ht & Hstw').
      dependent destruction Hstw'. eauto.
  Qed.

  Lemma compose_next_lq {q} m σ τ :
    compose (cpos_right q m) (next (pq m) σ) (next (oq m) τ) [=
    compose (cpos_left q) σ τ.
  Proof.
    intros w (s & t & Hs & Ht & Hw). cbn in Hs, Ht.
    econstructor; eauto.
  Qed.

  Lemma compose_next_rq {q m} u σ τ :
    compose (cpos_suspended q m u) σ (next (pq u) τ) [=
    next (pq u) (compose (cpos_right q m) σ τ).
  Proof.
    intros w' (s & t & Hs & Ht & Hw). cbn in Ht.
    econstructor; eauto.
  Qed.

  Lemma compose_next_oa {q m u} v σ τ :
    compose (cpos_right q m) σ (next (oa v) τ) =
    next (oa v) (compose (cpos_suspended q m u) σ τ).
  Proof.
    apply antisymmetry.
    - intros w' (s & t & Hs & Ht & Hw'). cbn in Ht |- *.
      eauto 10.
    - intros w' (s & t & Hs & Ht & Hw'). cbn.
      dependent destruction Hw'. eauto.
  Qed.

  Lemma compose_next_ra {q m} n σ τ :
    compose (cpos_left q) (next (oa n) σ) (next (pa n) τ) [=
    compose (cpos_right q m) σ τ.
  Proof.
    intros w' (s & t & Hs & Ht & Hw'). cbn in Hs, Ht |- *.
    eauto 10.
  Qed.

  Lemma compose_next_la {q} r σ τ :
    compose cpos_ready (next (pa r) σ) τ [=
    next (pa r) (compose (cpos_left q) σ τ).
  Proof.
    intros w' (s & t & Hs & Ht & Hw'). cbn in Hs |- *.
    eauto 10.
  Qed.
End COMPOSE.
                                          

(** * §4 REFINEMENT CONVENTIONS *)
                                          
(** ** §4.2 Refinement Conventions *)

Section RC.
  Context {E1 E2 : esig}.
  Obligation Tactic := cbn.

  (** *** Definition 4.1 *)

  Inductive rcp :=
    | rcp_allow (m1 : op E1) (m2 : op E2)
    | rcp_forbid (m1 : op E1) (m2 : op E2) (n1 : ar m1) (n2 : ar m2)
    | rcp_cont (m1 : op E1) (m2 : op E2) (n1 : ar m1) (n2 : ar m2) (k : rcp).

  Inductive rcp_ref : relation rcp :=
    | rcp_allow_ref m1 m2 :
        rcp_ref (rcp_allow m1 m2) (rcp_allow m1 m2)
    | rcp_allow_cont_ref m1 m2 n1 n2 k :
        rcp_ref (rcp_allow m1 m2) (rcp_cont m1 m2 n1 n2 k)
    | rcp_allow_forbid_ref m1 m2 n1 n2 :
        rcp_ref (rcp_allow m1 m2) (rcp_forbid m1 m2 n1 n2)
    | rcp_cont_ref m1 m2 n1 n2 k k' :
        rcp_ref k k' -> rcp_ref (rcp_cont m1 m2 n1 n2 k) (rcp_cont m1 m2 n1 n2 k')
    | rcp_cont_forbid_ref m1 m2 n1 n2 k :
        rcp_ref (rcp_cont m1 m2 n1 n2 k) (rcp_forbid m1 m2 n1 n2)
    | rcp_forbid_ref m1 m2 n1 n2 :
        rcp_ref (rcp_forbid m1 m2 n1 n2) (rcp_forbid m1 m2 n1 n2).

  Program Canonical Structure rcp_poset : poset :=
    {|
      poset_carrier := rcp;
      ref := rcp_ref;
    |}.
  Next Obligation.
    split.
    - intro w.
      induction w; constructor; auto.
    - intros x y z Hxy. revert z.
      induction Hxy; intros z Hyz;
      inversion Hyz; clear Hyz; xsubst; constructor; auto.
  Qed.
  Next Obligation.
    intros w1 w2 Hw12 Hw21.
    induction Hw12; inversion Hw21; xsubst; firstorder congruence.
  Qed.

  Definition conv :=
    downset rcp_poset.

  (** *** Residual *)

  Program Definition rcnext q1 q2 r1 r2 (R : conv) : conv :=
    {| Downset.has w := Downset.has R (rcp_cont q1 q2 r1 r2 w) |}.
  Next Obligation.
    intros q1 q2 r1 r2 R s t Hst Hs.
    eapply Downset.closed; eauto.
    eapply rcp_cont_ref; auto.
  Qed.

  (** *** Miscellaneous useful things *)

  Hint Constructors rcp_ref.

  Global Instance rcnext_ref :
    Monotonic rcnext (forallr -, forallr -, - ==> - ==> ref ++> ref).
  Proof.
    intros q1 q2 r1 r2 R S HRS.
    cbn. eauto.
  Qed.

  Lemma rcnext_inf {I} m1 m2 n1 n2 (R : I -> conv) :
    rcnext m1 m2 n1 n2 (linf R) = inf i, rcnext m1 m2 n1 n2 (R i).
  Proof.
    apply antisymmetry; cbn; auto.
  Qed.

  Lemma rcnext_sup {I} m1 m2 n1 n2 (R : I -> conv) :
    rcnext m1 m2 n1 n2 (lsup R) = sup i, rcnext m1 m2 n1 n2 (R i).
  Proof.
    apply antisymmetry; cbn; auto.
  Qed.
End RC.

Arguments rcp : clear implicits.
Arguments rcp_poset : clear implicits.
Arguments conv : clear implicits.
Global Instance rcnext_params : Params (@rcnext) 5.

(** ** §4.3 Refinement Squares *)

Section RSQ.
  Context {E1 E2 F1 F2 : esig}.

  (** *** Definition 4.2 (Refinement Square) *)

  Variant rspos : @position E1 F1 -> @position E2 F2 -> Type :=
    | rs_ready : rspos ready ready
    | rs_running q1 q2 : rspos (running q1) (running q2)
    | rs_suspended q1 q2 m1 m2 : rspos (suspended q1 m1) (suspended q2 m2).

  Inductive rsp (R S : conv _ _) :
    forall {i1 i2}, rspos i1 i2 -> @play E1 F1 i1 -> strat E2 F2 i2 -> Prop :=
    | rsp_ready τ :
        Downset.has τ pnil_ready ->
        rsp R S rs_ready pnil_ready τ
    | rsp_oq q1 s τ :
        Downset.has τ pnil_ready ->
        (forall q2, Downset.has S (rcp_allow q1 q2) ->
                    rsp R S (rs_running q1 q2) s (next (oq q2) τ)) ->
        rsp R S rs_ready (oq q1 :: s) τ
    | rsp_pq q1 q2 m1 m2 s τ :
        Downset.has R (rcp_allow m1 m2) ->
        rsp R S (rs_suspended q1 q2 m1 m2) s (next (pq m2) τ) ->
        rsp R S (rs_running q1 q2) (pq m1 :: s) τ
    | rsp_suspended q1 q2 m1 m2 τ :
        Downset.has τ (pnil_suspended q2 m2) ->
        rsp R S (rs_suspended q1 q2 m1 m2) (pnil_suspended q1 m1) τ
    | rsp_oa q1 q2 m1 m2 n1 s τ :
        Downset.has τ (pnil_suspended q2 m2) ->
        (forall n2,
          ~ Downset.has R (rcp_forbid m1 m2 n1 n2) ->
          rsp (rcnext m1 m2 n1 n2 R) S (rs_running q1 q2) s (next (oa n2) τ)) ->
        rsp R S (rs_suspended q1 q2 m1 m2) (oa n1 :: s) τ
    | rsp_pa q1 q2 r1 r2 s τ :
        ~ Downset.has S (rcp_forbid q1 q2 r1 r2) ->
        rsp R (rcnext q1 q2 r1 r2 S) rs_ready s (next (pa r2) τ) ->
        rsp R S (rs_running q1 q2) (pa r1 :: s) τ.

  Definition rsq R S {i1 i2} p (σ : strat E1 F1 i1) (τ : strat E2 F2 i2) : Prop :=
    forall s, Downset.has σ s -> rsp R S p s τ.

  (** *** Monotonicity properties *)

  Global Instance rsp_ref :
    Monotonic rsp (ref ++> ref --> forallr -, forallr -, - ==> ref --> ref ++> impl).
  Proof.
    intros R R' HR S S' HS i1 i2 p s1 s2 Hs τ1 τ2 Hτ H. cbn in *.
    revert R' HR S' HS s2 Hs τ2 Hτ.
    induction H; intros.
    - dependent destruction Hs; constructor; auto.
    - dependent destruction Hs; constructor; auto.
      intros q2 Hq2.
      eapply H1; cbn; eauto.
    - dependent destruction Hs.
      econstructor; eauto.
      eapply IHrsp; cbn; eauto.
    - dependent destruction Hs; constructor; auto.
    - dependent destruction Hs; constructor; auto.
      intros n2 Hn2.
      eapply H1; cbn; eauto.
    - dependent destruction Hs.
      econstructor; eauto.
      eapply IHrsp; cbn; eauto.
  Qed.

  Global Instance rsq_ref :
    Monotonic rsq (ref ++> ref --> forallr -, forallr -, - ==> ref --> ref ++> impl).
  Proof.
    intros R R' HR S S' HS i1 i2 p σ1 σ2 Hσ τ1 τ2 Hτ H s2 Hs2.
    rewrite <- HR, <- HS, <- Hτ.
    eapply H; eauto.
  Qed.

  (** *** Operational behavior *)

  Lemma rsq_next_oq {R S σ τ} q1 q2 :
    rsq R S rs_ready σ τ ->
    Downset.has S (rcp_allow q1 q2) ->
    rsq R S (rs_running q1 q2) (next (oq q1) σ) (next (oq q2) τ).
  Proof.
    intros Hστ Hq s Hs. cbn in *.
    specialize (Hστ _ Hs).
    dependent destruction Hστ.
    eauto.
  Qed.

  Lemma rsq_next_pq {R S q1 q2 σ τ} `{!Deterministic τ} m1 :
    rsq R S (rs_running q1 q2) σ τ ->
    Downset.has σ (pq m1 :: pnil_suspended q1 m1) ->
    exists m2,
      Downset.has R (rcp_allow m1 m2) /\
      Downset.has τ (pq m2 :: pnil_suspended q2 m2) /\
      rsq R S (rs_suspended q1 q2 m1 m2) (next (pq m1) σ) (next (pq m2) τ).
  Proof.
    intros Hστ H.
    apply Hστ in H.
    dependent destruction H. exists m2. split; auto.
    dependent destruction H0. cbn in H0. split; auto.
    intros s Hs. cbn in Hs.
    apply Hστ in Hs.
    dependent destruction Hs.
    assert (m3 = m2). {
      rewrite <- (pnil_suspended_pref s) in Hs.
      dependent destruction Hs. cbn in H2.
      pose proof (determinism _ _ H0 H2) as H23.
      dependent destruction H23; auto.
    }
    subst. auto.
  Qed.

  Lemma rsq_next_oa {R S q1 q2 m1 m2 σ τ} n1 n2 :
    rsq R S (rs_suspended q1 q2 m1 m2) σ τ ->
    ~ Downset.has R (rcp_forbid m1 m2 n1 n2) ->
    rsq (rcnext m1 m2 n1 n2 R) S (rs_running q1 q2) (next (oa n1) σ) (next (oa n2) τ).
  Proof.
    intros Hστ Hn s Hs.
    specialize (Hστ _ Hs).
    dependent destruction Hστ.
    eauto.
  Qed.

  Lemma rsq_next_pa {R S q1 q2 σ τ} `{!Deterministic τ} r1 :
    rsq R S (rs_running q1 q2) σ τ ->
    Downset.has σ (pa r1 :: pnil_ready) ->
    exists r2,
      ~ Downset.has S (rcp_forbid q1 q2 r1 r2) /\
      Downset.has τ (pa r2 :: pnil_ready) /\
      rsq R (rcnext q1 q2 r1 r2 S) rs_ready (next (pa r1) σ) (next (pa r2) τ).
  Proof.
    intros Hστ H.
    apply Hστ in H.
    dependent destruction H. exists r2. split; auto.
    dependent destruction H0. cbn in H0. split; auto.
    intros s Hs. cbn in Hs.
    apply Hστ in Hs.
    dependent destruction Hs.
    assert (r3 = r2). {
      rewrite <- (pnil_ready_pref s) in Hs.
      dependent destruction Hs. cbn in H2.
      pose proof (determinism _ _ H0 H2) as H23.
      dependent destruction H23; auto.
    }
    subst. auto.
  Qed.

  (** *** Continuity vs. refinement conventions *)

  Lemma rsp_sup_cases {I} {i1 i2} (p : rspos i1 i2) R (S : I -> conv F1 F2) (s : play i1) (τ : strat E2 F2 i2) `{Hτ : !Deterministic τ}:
    match p with
    | rs_ready => fun s τ =>
      inhabited I /\
      forall i, rsp R (S i) p s τ
    | rs_running q1 q2
    | rs_suspended q1 q2 _ _ => fun s τ =>
      (exists i, Downset.has (S i) (rcp_allow q1 q2)) /\
      (forall i, Downset.has (S i) (rcp_allow q1 q2) -> rsp R (S i) p s τ)
    end s τ ->
    rsp R (lsup S) p s τ.
  Proof.
    revert i2 p I R S τ Hτ.
    induction s as [ | q1 m1 | i1 j1 m s' IHs']; intros i2 p I R S τ Hτ.
    - (* ready *)
      dependent destruction p.
      intros [[i] H]. specialize (H i).
      dependent destruction H.
      constructor; auto.
    - (* suspended *)
      dependent destruction p.
      intros [[i Hi] H]. specialize (H i Hi).
      dependent destruction H.
      constructor; auto.
    - (* move *)
      dependent destruction m.
      + (* incoming question *)
        rename q into q1.
        dependent destruction p.
        intros [[i] H].
        constructor.
        * specialize (H i).
          dependent destruction H.
          assumption.
        * clear i. intros q2 Hq12.
          apply (IHs' _ (rs_running q1 q2) I R S (next (oq q2) τ) _).
          split; eauto.
          intros i Hi.
          specialize (H i). dependent destruction H.
          apply H0. assumption.
      + (* outgoing question *)
        rename q into q1, m into m1.
        dependent destruction p.
        intros [[i Hiq] H].
        pose proof (H i Hiq) as Hi.
        dependent destruction Hi.
        econstructor; eauto.
        eapply IHs'; try typeclasses eauto.
        split; eauto.
        intros j Hjq.
        pose proof (H j Hjq) as Hj.
        dependent destruction Hj.
        assert (m3 = m2). {
          dependent destruction Hi;
          dependent destruction Hj; cbn in *;
          eapply (pq_determinism τ); eauto.
        }
        subst m3; auto.
      + (* environment answer *)
        rename q into q1, m into m1, n into n1.
        dependent destruction p.
        intros [[i Hiq] H]. constructor.
        * specialize (H i Hiq).
          dependent destruction H.
          assumption.
        * intros n2 Hn.
          eapply IHs'. { typeclasses eauto. }
          split; eauto.
          intros j Hjq.
          specialize (H j Hjq).
          dependent destruction H; eauto.
      + (* component answer *)
        rename q into q1, r into r1.
        dependent destruction p.
        (* specialize (IHs _ rs_ready). cbn iota beta in IHs. *)
        intros [[i Hiq] H].
        pose proof (H i Hiq) as Hi. dependent destruction Hi.
        econstructor.
        * intros [j Hjr].
          assert (Downset.has (S j) (rcp_allow q1 q2)) as Hjq. {
            eapply Downset.closed; eauto.
            constructor.
          }
          pose proof (H j Hjq) as Hj. dependent destruction Hj.
          assert (r3 = r2). {
            dependent destruction Hi;
            dependent destruction Hj; cbn in *;
            eapply (pa_determinism τ); eauto.
          }
          subst r3. eauto.
        * assert (rcnext q1 q2 r1 r2 (sup {j | Downset.has (S j) (rcp_allow q1 q2)}, S j) =
                  rcnext q1 q2 r1 r2 (lsup S)). {
            clear. apply antisymmetry; cbn.
            -- intros ? [? ?]. eauto.
            -- intros s [i Hi].
               assert (Hi' : Downset.has (S i) (rcp_allow q1 q2))
                 by (eapply Downset.closed; [constructor | eauto]).
               exists (exist _ i Hi'). cbn. auto.
          }
          rewrite <- H1. unfold fsup.
          rewrite rcnext_sup.
          apply IHs'. { typeclasses eauto. }
          split; eauto.
          intros [j Hj].
          specialize (H j Hj).
          dependent destruction H. cbn.
          assert (r0 = r2). {
            dependent destruction H0; dependent destruction Hi; cbn in *;
            eapply (pa_determinism τ); eauto.
          }
          congruence.
  Qed.

  Lemma rsp_sup {I} R S s τ `{Hτ : !Deterministic τ} :
    inhabited I ->
    (forall i:I, rsp R (S i) rs_ready s τ) ->
    rsp R (lsup S) rs_ready s τ.
  Proof.
    eauto using (rsp_sup_cases rs_ready).
  Qed.

  Lemma rsq_sup {I} R S σ τ `{Hτ : !Deterministic τ} :
    inhabited I ->
    (forall i:I, rsq R (S i) rs_ready σ τ) ->
    rsq R (lsup S) rs_ready σ τ.
  Proof.
    intros HI H s Hs.
    apply rsp_sup; auto.
    intro i. apply H, Hs.
  Qed.

  Lemma rsp_inf {I} R S {i1 i2} {p : rspos i1 i2} s τ `{Hτ : !Deterministic τ} :
    inhabited I ->
    (forall i:I, rsp (R i) S p s τ) ->
    rsp (linf R) S p s τ.
  Admitted.
End RSQ.

Global Instance rsp_params : Params (@rsp) 7.
Global Instance rsq_params : Params (@rsq) 7.

Section RSQ_COMP.
  Context {E1 E2} (R : conv E1 E2).
  Context {F1 F2} (S : conv F1 F2).
  Context {G1 G2} (T : conv G1 G2).

  (** *** Theorem 4.3 (Horizontal composition of refinement squares) *)

  (** The possible combinations of positions for the source and target,
    left-hand side, right-hand side and composite stragies. *)

  Variant rscpos : forall {i1 j1 k1 i2 j2 k2},
    @cpos E1 F1 G1 i1 j1 k1 -> @cpos E2 F2 G2 i2 j2 k2 ->
    rspos i1 i2 -> rspos j1 j2 -> rspos k1 k2 -> Type :=
    | rsc_ready :
        rscpos cpos_ready cpos_ready
               rs_ready rs_ready rs_ready
    | rsc_left q1 q2 :
        rscpos (cpos_left q1) (cpos_left q2)
               (rs_running q1 q2) rs_ready (rs_running q1 q2)
    | rsc_right q1 q2 m1 m2 :
        rscpos (cpos_right q1 m1) (cpos_right q2 m2)
               (rs_suspended q1 q2 m1 m2) (rs_running m1 m2) (rs_running q1 q2)
    | rsc_suspended q1 q2 m1 m2 u1 u2 :
        rscpos (cpos_suspended q1 m1 u1) (cpos_suspended q2 m2 u2)
               (rs_suspended q1 q2 m1 m2) (rs_suspended m1 m2 u1 u2) (rs_suspended q1 q2 u1 u2).

  (** Having enumerated them, we can formulate the compatibility of
    composition with refinement squares as follows. *)

  Hint Constructors comp_has pref.

  Lemma rsq_comp {i1 j1 k1 i2 j2 k2 p1 p2 pi pj pk} :
    @rscpos i1 j1 k1 i2 j2 k2 p1 p2 pi pj pk ->
    forall (σ1 : strat F1 G1 i1) (τ1 : strat E1 F1 j1)
           (σ2 : strat F2 G2 i2) (τ2 : strat E2 F2 j2)
           `{Hσ2 : !Deterministic σ2} `{Hτ2 : !Deterministic τ2},
      rsq S T pi σ1 σ2 ->
      rsq R S pj τ1 τ2 ->
      rsq R T pk (compose p1 σ1 τ1) (compose p2 σ2 τ2).
  Proof.
    intros p σ1 τ1 σ2 τ2 Hσ2 Hτ2 Hσ Hτ w1 (s1 & t1 & Hs1 & Ht1 & Hst1).
    revert R S T i2 j2 k2 p2 pi pj pk p σ1 τ1 σ2 τ2 Hσ2 Hτ2 Hσ Hτ Hs1 Ht1.
    induction Hst1; intros.
    - (* ready *)
      inversion p; clear p; xsubst.
      constructor; cbn.
      exists pnil_ready, pnil_ready.
      eapply Downset.closed in Ht1; cbn; auto using pnil_ready_pref.
      specialize (Hσ _ Hs1). inversion Hσ; clear Hσ; xsubst.
      specialize (Hτ _ Ht1). inversion Hτ; clear Hτ; xsubst.
      eauto.
    - (* incoming question *)
      inversion p; clear p; xsubst.
      constructor.
      + exists pnil_ready, pnil_ready.
        eapply Downset.closed in Ht1; cbn; auto using pnil_ready_pref.
        specialize (Hσ _ Hs1). inversion Hσ; clear Hσ; xsubst.
        specialize (Hτ _ Ht1). inversion Hτ; clear Hτ; xsubst.
        eauto.
      + intros q2 Hq.
        rewrite <- (compose_next_oq q2).
        eapply IHHst1 with (1 := rsc_left q q2)
                           (σ1 := next (oq q) σ1); cbn; eauto with typeclass_instances.
        apply rsq_next_oq; auto.
    - (* internal question *)
      inversion p; clear p; xsubst.
      edestruct @rsq_next_pq as (m2 & Hm & Hm2 & ?); eauto.
      { eapply Downset.closed; cbn; eauto. constructor. constructor. }
      rewrite <- (compose_next_lq m2).
      eapply IHHst1 with (1 := rsc_right q q2 m m2)
                         (σ1 := next (pq m) σ1)
                         (τ1 := next (oq m) τ1); eauto with typeclass_instances.
      apply rsq_next_oq; auto.
    - (* outgoing question *)
      inversion p; clear p; xsubst.
      edestruct @rsq_next_pq as (u2 & Hu & Hu2 & ?); eauto.
      { eapply Downset.closed; cbn; eauto. constructor. constructor. }
      econstructor; eauto.
      rewrite <- compose_next_rq.
      eapply IHHst1 with (1 := rsc_suspended q q2 m m2 u u2)
                         (σ1 := σ1)
                         (τ1 := next (pq u) τ1); eauto with typeclass_instances.
    - (* suspended *)
      inversion p; clear p; xsubst.
      constructor; cbn.
      exists (pnil_suspended q2 m2), (pnil_suspended m2 u2).
      eapply Downset.closed in Hs1; cbn; auto using pnil_suspended_pref.
      specialize (Hσ _ Hs1). dependent destruction Hσ.
      specialize (Hτ _ Ht1). dependent destruction Hτ.
      eauto.
    - (* environment answer *)
      inversion p; clear p; xsubst.
      constructor.
      + exists (pnil_suspended q2 m2), (pnil_suspended m2 u2).
        eapply Downset.closed in Hs1; cbn; auto using pnil_suspended_pref.
        specialize (Hσ _ Hs1). dependent destruction Hσ.
        specialize (Hτ _ Ht1). dependent destruction Hτ.
        eauto.
      + intros n2 Hn.
        rewrite <- compose_next_oa.
        eapply IHHst1 with (1 := rsc_right q q2 m m2)
                           (σ1 := σ1)
                           (τ1 := next (oa v) τ1); eauto with typeclass_instances.
        apply rsq_next_oa; auto.
    - (* answer of τ *)
      inversion p; clear p; xsubst.
      edestruct @rsq_next_pa as (n2 & Hn & Hn2 & H); eauto.
      { eapply Downset.closed; eauto. cbn. constructor. constructor. }
      rewrite <- (compose_next_ra n2).
      eapply IHHst1 with (1 := rsc_left q q2)
                         (σ1 := next (oa n) σ1)
                         (τ1 := next (pa n) τ1); eauto with typeclass_instances.
      apply rsq_next_oa; auto.
    - (* answer of σ *)
      inversion p; clear p; xsubst.
      edestruct @rsq_next_pa as (r2 & Hr & Hr2 & H); eauto.
      { eapply Downset.closed; eauto. cbn. constructor. constructor. }
      econstructor; eauto.
      rewrite <- (compose_next_la r2).
      eapply IHHst1 with (1 := rsc_ready)
                         (σ1 := next (pa r) σ1)
                         (τ1 := τ1); eauto with typeclass_instances.
  Qed.
End RSQ_COMP.

(** ** §4.4 Vertical Composition *)

(** *** Definition 4.6 (Veritcal composition of refinement conventions) *)

Section VCOMP.
  Context {E1 E2 E3 : esig}.
  Obligation Tactic := cbn.

  Fixpoint vcomp_has (R : conv E1 E2) (S : conv E2 E3) (s : rcp E1 E3) : Prop :=
    match s with
      | rcp_allow m1 m3 =>
        exists m2, Downset.has R (rcp_allow m1 m2) /\
                   Downset.has S (rcp_allow m2 m3)
      | rcp_forbid m1 m3 n1 n3 =>
        exists m2, Downset.has R (rcp_allow m1 m2) /\
                   Downset.has S (rcp_allow m2 m3) /\
        forall n2, Downset.has R (rcp_forbid m1 m2 n1 n2) \/
                   Downset.has S (rcp_forbid m2 m3 n2 n3)
      | rcp_cont m1 m3 n1 n3 s =>
        exists m2, Downset.has R (rcp_allow m1 m2) /\
                   Downset.has S (rcp_allow m2 m3) /\
        forall n2, Downset.has R (rcp_forbid m1 m2 n1 n2) \/
                   Downset.has S (rcp_forbid m2 m3 n2 n3) \/
                   vcomp_has (rcnext m1 m2 n1 n2 R) (rcnext m2 m3 n2 n3 S) s
    end.

  Global Instance vcomp_has_ref :
    Monotonic vcomp_has (ref ++> ref ++> rcp_ref --> impl).
  Proof.
    intros R1 R2 HR S1 S2 HS u v Huv.
    revert R1 R2 HR S1 S2 HS. cbn. unfold impl.
    induction Huv as [ | | | m1 m3 n1 n3 k k' Hk IHk | m1 m3 n1 n3 k | m1 m3 n1 n3 ]; cbn.
    - firstorder.
    - firstorder.
    - firstorder.
    - intros R1 R2 HR S1 S2 HS (m2 & Hm12 & Hm23 & Hn).
      exists m2; repeat (split; auto).
      intros n2. specialize (Hn n2) as [Hn12 | [Hn23 | Hk']]; eauto.
      right. right. revert Hk'. eapply IHk; cbn; eauto.
    - intros R1 R2 HR S1 S2 HS (m2 & Hm12 & Hm23 & Hn).
      exists m2; repeat (split; auto).
      intros n2. specialize (Hn n2) as [Hn12 | Hn23]; eauto.
    - intros R1 R2 HR S1 S2 HS (m2 & Hm12 & Hm23 & Hn).
      exists m2; repeat (split; auto).
      intros n2. specialize (Hn n2) as [Hn12 | Hn23]; eauto.
  Qed.

  Program Definition vcomp R S : conv E1 E3 :=
    {| Downset.has := vcomp_has R S |}.
  Next Obligation.
    intros until 1. rauto.
  Qed.

  (** The following formulations and properties of [vcomp] are useful
    for the vertical composition proof of refinement squares below. *)

  Definition vcomp_at_question_has (m2 : E2) R S s : Prop :=
    match s with
      | rcp_allow m1 m3 =>
        Downset.has R (rcp_allow m1 m2) /\
        Downset.has S (rcp_allow m2 m3)
      | rcp_forbid m1 m3 n1 n3 =>
        Downset.has R (rcp_allow m1 m2) /\
        Downset.has S (rcp_allow m2 m3) /\
        forall n2, Downset.has R (rcp_forbid m1 m2 n1 n2) \/
                   Downset.has S (rcp_forbid m2 m3 n2 n3)
      | rcp_cont m1 m3 n1 n3 k =>
        Downset.has R (rcp_allow m1 m2) /\
        Downset.has S (rcp_allow m2 m3) /\
        forall n2, Downset.has R (rcp_forbid m1 m2 n1 n2) \/
                   Downset.has S (rcp_forbid m2 m3 n2 n3) \/
                   Downset.has (vcomp (rcnext m1 m2 n1 n2 R) (rcnext m2 m3 n2 n3 S)) k
    end.

  Program Definition vcomp_at_question m2 R S : conv E1 E3 :=
    {| Downset.has := vcomp_at_question_has m2 R S |}.
  Next Obligation.
    intros m2 R S s t Hst.
    induction Hst; cbn; try tauto.
    + setoid_rewrite Hst. auto.
    + firstorder auto.
  Qed.

  Lemma vcomp_sup_at_question R S :
    vcomp R S = sup m2, vcomp_at_question m2 R S.
  Proof.
    apply antisymmetry; intros [m1 m3 | m1 m3 n1 n3 | m1 m3 n1 n3 k]; cbn; firstorder.
  Qed.

  Definition vcomp_at_has (m2 : E2) (xn2 : option (ar m2)) R S s : Prop :=
    match s with
      | rcp_allow m1 m3 =>
        Downset.has R (rcp_allow m1 m2) /\
        Downset.has S (rcp_allow m2 m3)
      | rcp_forbid m1 m3 n1 n3 =>
        Downset.has R (rcp_allow m1 m2) /\
        Downset.has S (rcp_allow m2 m3) /\
        forall n2, xn2 = Some n2 ->
                   Downset.has R (rcp_forbid m1 m2 n1 n2) \/
                   Downset.has S (rcp_forbid m2 m3 n2 n3)
      | rcp_cont m1 m3 n1 n3 k =>
        Downset.has R (rcp_allow m1 m2) /\
        Downset.has S (rcp_allow m2 m3) /\
        forall n2, xn2 = Some n2 ->
                   Downset.has R (rcp_forbid m1 m2 n1 n2) \/
                   Downset.has S (rcp_forbid m2 m3 n2 n3) \/
                   Downset.has (vcomp (rcnext m1 m2 n1 n2 R) (rcnext m2 m3 n2 n3 S)) k
    end.

  Program Definition vcomp_at m2 n2 R S : conv E1 E3 :=
    {| Downset.has := vcomp_at_has m2 n2 R S |}.
  Next Obligation.
    intros m2 xn2 R S s t Hst.
    induction Hst; cbn; try tauto.
    + setoid_rewrite Hst. auto.
    + firstorder auto.
  Qed.

  Lemma vcomp_expand R S :
    vcomp R S = sup m2, inf xn2, vcomp_at m2 xn2 R S.
  Proof.
    apply antisymmetry; intros [m1 m3 | m1 m3 n1 n3 | m1 m3 n1 n3 k]; cbn.
    - firstorder.
    - firstorder.
    - firstorder.
    - firstorder.
    - intros (m2 & H2). exists m2.
      pose proof (H2 None) as (? & ? & _). split; auto. split; auto.
      intros n2. pose proof (H2 (Some n2)) as (? & ? & ?). eauto.
    - intros (m2 & H2). exists m2.
      pose proof (H2 None) as (? & ? & _). split; auto. split; auto.
      intros n2. pose proof (H2 (Some n2)) as (? & ? & ?). eauto.
  Qed.

  Lemma rcnext_vcomp_at m1 m2 m3 n1 n2 n3 R S :
    ~ Downset.has R (rcp_forbid m1 m2 n1 n2) ->
    ~ Downset.has S (rcp_forbid m2 m3 n2 n3) ->
    rcnext m1 m3 n1 n3 (vcomp_at m2 (Some n2) R S) =
    vcomp (rcnext m1 m2 n1 n2 R) (rcnext m2 m3 n2 n3 S).
  Proof.
    intros Hn12 Hn23.
    apply antisymmetry; intros s; cbn.
    - intros (Hm12 & Hm23 & Hn). specialize (Hn _ (reflexivity _)).
      destruct Hn as [? | [? | ?]]; tauto.
    - destruct s as [m1' m3' | m1' m3' n1' n3' | m1' m3' n1' n3' k]; cbn.
      + intros (m2' & Hm12' & Hm23').
        split. { eapply Downset.closed; eauto. constructor. }
        split. { eapply Downset.closed; eauto. constructor. }
        inversion 1; clear H; subst.
        eauto.
      + intros (m2' & Hm12' & Hm23' & Hn13').
        split. { eapply Downset.closed; eauto. constructor. }
        split. { eapply Downset.closed; eauto. constructor. }
        inversion 1; clear H; subst.
        eauto 10.
      + intros (m2' & Hm12' & Hm23' & Hn13').
        split. { eapply Downset.closed; eauto. constructor. }
        split. { eapply Downset.closed; eauto. constructor. }
        inversion 1; clear H; subst.
        eauto 10.
  Qed.

  (* ... *)

  Lemma rcnext_vcomp m1 m3 n1 n3 R S :
    rcnext m1 m3 n1 n3 (vcomp R S) =
    sup {m2 | Downset.has R (rcp_allow m1 m2) /\ Downset.has S (rcp_allow m2 m3)},
    inf {n2 | ~Downset.has R (rcp_forbid m1 m2 n1 n2) /\ ~Downset.has S (rcp_forbid m2 m3 n2 n3)},
    vcomp (rcnext m1 m2 n1 n2 R) (rcnext m2 m3 n2 n3 S).
  Proof.
    apply antisymmetry; intros s; cbn.
    - intros (m2 & Hm12 & Hm23 & Hs).
      exists (exist _ m2 (conj Hm12 Hm23)); cbn.
      intros (n2 & Hn12 & Hn23); cbn.
      firstorder.
    - intros ((m2 & Hm12 & Hm23) & Hs); cbn in *.
      exists m2; repeat (split; auto).
      intros n2.
      destruct (classic (Downset.has R (rcp_forbid m1 m2 n1 n2))) as [ | Hn12]; auto.
      destruct (classic (Downset.has S (rcp_forbid m2 m3 n2 n3))) as [ | Hn23]; auto.
      specialize (Hs (exist _ n2 (conj Hn12 Hn23))); cbn in *; auto.
  Qed.
End VCOMP.

(** *** Theorem 4.7 (Veritcal composition of refinement squares) *)

Section RSVCOMP.
  Context {E1 F1 E2 F2 E3 F3 : esig}.

  Variant rsvpos : forall {p1 p2 p3}, @rspos E1 E2 F1 F2 p1 p2 ->
                                      @rspos E2 E3 F2 F3 p2 p3 ->
                                      @rspos E1 E3 F1 F3 p1 p3 -> Type :=
    | rsv_ready :
        rsvpos rs_ready
               rs_ready
               rs_ready
    | rsv_running q1 q2 q3 :
        rsvpos (rs_running q1 q2)
               (rs_running q2 q3)
               (rs_running q1 q3)
    | rsv_suspended q1 q2 q3 m1 m2 m3 :
        rsvpos (rs_suspended q1 q2 m1 m2)
               (rs_suspended q2 q3 m2 m3)
               (rs_suspended q1 q3 m1 m3).

  Lemma rsp_vcomp {p1 p2 p3 p12 p23 p13} (p : @rsvpos p1 p2 p3 p12 p23 p13) :
    forall (R : conv E1 E2) (R' : conv E2 E3) (S : conv F1 F2) (S' : conv F2 F3)
           (s1 : @play E1 F1 p1) (σ2 : strat E2 F2 p2) (σ3 : strat E3 F3 p3)
           `{Hσ2 : !Deterministic σ2} `{Hσ3 : !Deterministic σ3},
      rsp R S p12 s1 σ2 ->
      rsq R' S' p23 σ2 σ3 ->
      match p with
        | rsv_ready =>
          rsp (vcomp R R') (vcomp S S') p13 s1 σ3
        | rsv_running q1 q2 q3 =>
          rsp (vcomp R R') (inf r2, vcomp_at q2 r2 S S') p13 s1 σ3
        | rsv_suspended q1 q2 q3 m1 m2 m3 =>
          rsp (inf n2, vcomp_at m2 n2 R R') (inf r2, vcomp_at q2 r2 S S') p13 s1 σ3
      end.
  Proof.
    intros R R' S S' s1 σ2 σ3 Hσ2 Hσ3 H12 Hσ23.
    revert p3 p23 p13 p R' S' σ3 Hσ3 Hσ23.
    induction H12; intros; dependent destruction p.
    - (* ready *)
      pose proof (Hσ23 _ H) as Hnil.
      dependent destruction Hnil.
      constructor; auto.
    - (* incoming question *)
      rewrite (vcomp_expand S S').
      pose proof (Hσ23 _ H) as Hnil.
      dependent destruction Hnil.
      constructor; auto.
      intros q3 Hq13.
      apply rsp_sup_cases; eauto with typeclass_instances.
      split. { destruct Hq13 as [q2 Hq13]. eauto. } clear Hq13.
      intros q2 Hq13. cbn in Hq13. specialize (Hq13 None) as [Hq12 Hq23].
      eapply (H1 q2 Hq12 _ _ _ _ (rsv_running q1 q2 q3)); eauto with typeclass_instances.
      eapply rsq_next_oq; eauto.
    - (* outgoing question *)
      rename q4 into q3.
      rewrite (vcomp_expand R R'), <- (sup_ub m2).
      assert (Hm2 : Downset.has τ (pq m2 :: pnil_suspended q2 m2))
        by (dependent destruction H12; cbn in *; auto).
      edestruct @rsq_next_pq as (m3 & Hm23 & Hm3 & Hnext); eauto.
      econstructor. { cbn. eauto. }
      eapply (IHrsp _ _ _ _ (rsv_suspended q1 q2 q3 m1 m2 m3)); eauto with typeclass_instances.
    - (* suspended *)
      rename q4 into q3, m4 into m3.
      pose proof (Hσ23 _ H) as Hnil.
      dependent destruction Hnil.
      constructor; auto.
    - (* environment answer *)
      rename q4 into q3, m4 into m3.
      admit.
    - (* component answer *)
      rename q4 into q3, H into Hr12.
      rewrite (inf_lb (Some r2)).
      destruct (rsq_next_pa r2 Hσ23) as (r3 & Hr23 & Hr3 & H23). {
        dependent destruction H12; auto.
      }
      econstructor. { cbn. intros (Hq12 & Hq23 & [Hr | Hr]); eauto. }
      rewrite rcnext_vcomp_at by auto.
      eapply (IHrsp _ _ _ _ rsv_ready); eauto with typeclass_instances.
  Admitted.
End RSVCOMP.
