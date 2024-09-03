Require Import Classical.
Require Import Program.Equality.
From coqrel Require Import LogicalRelations.
(* Require Import Quiver. *)
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

Ltac xinv H := inversion H; clear H; subst; xsubst.

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
    @downset (play_poset p).

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

  Require Import Coq.Program.Equality.

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
    @downset rcp_poset.

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

  Lemma rcp_allows (s : rcp) :
    exists m1 m2, rcp_allow m1 m2 [= s.
  Proof.
    destruct s; cbn; eauto.
  Qed.

  Variant rctrim_has q1 q2 r1 r2 (R : conv) : rcp -> Prop :=
    | rctrim_allow :
        Downset.has R (rcp_allow q1 q2) ->
        rctrim_has q1 q2 r1 r2 R (rcp_allow q1 q2)
    | rctrim_forbid n1 n2 :
        Downset.has R (rcp_allow q1 q2) ->
        (n1 = r1 -> n2 = r2 -> Downset.has R (rcp_forbid q1 q2 n1 n2)) ->
        rctrim_has q1 q2 r1 r2 R (rcp_forbid q1 q2 n1 n2)
    | rctrim_cont n1 n2 s :
        Downset.has R (rcp_allow q1 q2) ->
        (n1 = r1 -> n2 = r2 -> Downset.has R (rcp_cont q1 q2 n1 n2 s)) ->
        rctrim_has q1 q2 r1 r2 R (rcp_cont q1 q2 n1 n2 s).

  Program Definition rctrim q1 q2 r1 r2 R : conv :=
    {| Downset.has := rctrim_has q1 q2 r1 r2 R |}.
  Next Obligation.
    intros q1 q2 r1 r2 R s t Hst Hs.
    induction Hs; inversion Hst; clear Hst; xsubst; constructor; auto.
    - clear H. intros H1 H2. eapply Downset.closed; eauto. constructor.
    - clear H. intros H1 H2. eapply Downset.closed; eauto. constructor; auto.
  Qed.

  Lemma rcnext_rctrim m1 m2 n1 n2 R :
    rcnext m1 m2 n1 n2 (rctrim m1 m2 n1 n2 R) = rcnext m1 m2 n1 n2 R.
  Proof.
    apply antisymmetry; cbn.
    - inversion 1; xsubst. eauto.
    - intros s Hs. constructor; auto.
      eapply Downset.closed; eauto. constructor.
  Qed.
End RC.

Arguments rcp : clear implicits.
Arguments rcp_poset : clear implicits.
Arguments conv : clear implicits.

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
End RSQ.

Global Instance rsp_params : Params (@rsp) 7.
Proof.
Admitted.

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

  Hint Constructors comp_has pref rscpos.

  Lemma rsp_comp {i1 j1 k1 i2 j2 k2 p1 p2 pi pj pk} :
    @rscpos i1 j1 k1 i2 j2 k2 p1 p2 pi pj pk ->
    forall (s : @play F1 G1 i1) (t : @play E1 F1 j1)
      (σ : strat F2 G2 i2) (τ : strat E2 F2 j2) (w : @play E1 G1 k1),
      comp_has p1 s t w ->
      rsp S T pi s σ ->
      rsp R S pj t τ ->
      rsp R T pk w (compose p2 σ τ).
  Proof.
    intros p s t σ τ w Hw Hs Ht.
    revert R S T i2 j2 k2 p2 pi pj pk p σ τ Hs Ht.
    induction Hw; intros.
    - (* ready *)
      xinv p. xinv Hs. constructor; cbn.
      exists pnil_ready, pnil_ready. repeat apply conj; eauto.
      xinv Ht; eauto.
    - (* incoming question *)
      xinv p. xinv Hs. constructor; cbn.
      + exists pnil_ready, pnil_ready. repeat apply conj; eauto.
        xinv Ht; eauto.
      + intros q2 Hq. rewrite <- (compose_next_oq q2). eauto.
    - (* internal question *)
      xinv p. xinv Hs. xinv Ht.
      rewrite <- (compose_next_lq m2). eauto.
    - (* outgoing question *)
      xinv p. xinv Ht. econstructor; eauto.
      rewrite <- compose_next_rq. eauto.
    - (* suspended *)
      xinv p. xinv Ht. constructor. cbn.
      exists (pnil_suspended q2 m2), (pnil_suspended m2 u2).
      repeat apply conj; eauto.
      xinv Hs; eauto.
    - (* environment answer *)
      xinv p. xinv Ht. constructor.
      + exists (pnil_suspended q2 m2), (pnil_suspended m2 u2).
        repeat apply conj; eauto. xinv Hs; eauto.
      + intros n2 Hn. rewrite <- compose_next_oa. eauto.
    - (* answer of τ *)
      xinv p. xinv Hs. xinv Ht.
      rewrite <- (compose_next_ra r2). eauto.
    - (* answer of σ *)
      xinv p. xinv Hs. econstructor; eauto.
      rewrite <- (compose_next_la r2). eauto.
  Qed.

  Lemma rsq_comp {i1 j1 k1 i2 j2 k2 p1 p2 pi pj pk} :
    @rscpos i1 j1 k1 i2 j2 k2 p1 p2 pi pj pk ->
    forall (σ1 : strat F1 G1 i1) (τ1 : strat E1 F1 j1)
           (σ2 : strat F2 G2 i2) (τ2 : strat E2 F2 j2),
      rsq S T pi σ1 σ2 ->
      rsq R S pj τ1 τ2 ->
      rsq R T pk (compose p1 σ1 τ1) (compose p2 σ2 τ2).
  Proof.
    intros p σ1 τ1 σ2 τ2 Hσ Hτ w1 (s1 & t1 & Hs1 & Ht1 & Hst1).
    eauto using rsp_comp.
  Qed.
End RSQ_COMP.

Section SEQ_COMP.

  Section DEF.

    Obligation Tactic := cbn.

    Context {E F: esig}.

    Inductive seq_comp_has: forall {i j}, @play E F i -> @play E F j -> @play E F i -> Prop :=
    | seq_comp_ready (t: play ready):
      seq_comp_has pnil_ready t t
    | seq_comp_oq q s (t: play ready) w:
      seq_comp_has s t w ->
      seq_comp_has (oq q :: s) t (oq q :: w)
    | seq_comp_pq q m s t w:
      seq_comp_has s (t: play ready) w ->
      @seq_comp_has (running q) _ (pq m :: s) t (pq m :: w)
    | seq_comp_suspend q m (t: play ready):
      seq_comp_has (pnil_suspended q m) t (pnil_suspended q m)
    | seq_comp_oa q m n s (t: play ready) w:
      seq_comp_has s t w ->
      @seq_comp_has (suspended q m) _ (oa n :: s) t (oa n :: w)
    | seq_comp_pa q r s (t: play ready) w:
      seq_comp_has s t w ->
      @seq_comp_has (running q) _ (pa r :: s) t (pa r :: w).

    Hint Constructors seq_comp_has.
    Hint Constructors pref.
    Hint Resolve (reflexivity (R := pref)).

    Lemma seq_comp_has_pref {i j} (s: @play E F i) (t: @play E F j) w :
      seq_comp_has s t w ->
      forall w', w' [= w -> exists s' t', s' [= s /\ t' [= t /\ seq_comp_has s' t' w'.
    Proof.
      induction 1; cbn in *.
      - intros w' Hw'. xinv Hw'; eauto 10.
      - intros w' Hw'.
        dependent destruction w'; eauto. xinv Hw'.
        edestruct IHseq_comp_has as (s' & t' & Hs' & Ht' & Hw'); eauto 10.
      - intros w' Hw'.
        dependent destruction w'. xinv Hw'.
        edestruct IHseq_comp_has as (s' & t' & Hs' & Ht' & Hw'); eauto 10.
      - intros w' Hw'. xinv Hw'; eauto 10.
      - intros w' Hw'.
        dependent destruction w'; eauto. xinv Hw'.
        edestruct IHseq_comp_has as (s' & t' & Hs' & Ht' & Hw'); eauto 10.
      - intros w' Hw'.
        dependent destruction w'; eauto. xinv Hw'.
        edestruct IHseq_comp_has as (s' & t' & Hs' & Ht' & Hw'); eauto 10.
    Qed.

    Program Definition seq_compose {i j} (σ : strat E F i) (τ : strat E F j) : strat E F i :=
      {| Downset.has w :=
          exists s t, Downset.has σ s /\ Downset.has τ t /\ seq_comp_has s t w |}.
    Next Obligation.
      intros i j σ τ x y Href (s & t & Hs & Ht & Hw).
      edestruct @seq_comp_has_pref as (s' & t' & Hs' & Ht' & Hw''); eauto.
      eauto 10 using Downset.closed.
    Qed.

  End DEF.

  Class RegularConv {E F} (R : conv E F) :=
    {
      regular_conv m1 m2 n1 n2:
        Downset.has R (rcp_allow m1 m2) ->
        ~ Downset.has R (rcp_forbid m1 m2 n1 n2) ->
        rcnext m1 m2 n1 n2 R = R;
    }.

  Hint Constructors seq_comp_has.
  Hint Constructors pref.
  Hint Resolve (reflexivity (R := pref)).

  Lemma rsp_seq_comp {E1 E2 F1 F2} (R S: conv _ _)
    `{!RegularConv R} `{!RegularConv S}
    i1 i2 j1 j2 (pi: rspos i1 j1) (pj: rspos i2 j2) (s: @play E1 F1 i1)
    (τ1: @strat E2 F2 j1) (τ2: @strat E2 F2 j2):
    (exists s1 s2, seq_comp_has s1 s2 s /\
      rsp R S pi s1 τ1 /\
      rsp R S pj s2 τ2) ->
      rsp R S pi s (seq_compose τ1 τ2).
  Proof.
    intros (s1 & s2 & Hs & Hs1 & Hs2).
    revert j1 j2 τ1 τ2 pi pj Hs1 Hs2.
    dependent induction Hs.
    - intros. xinv Hs1. dependent destruction pj.
      assert (Ht : τ2 [= (seq_compose τ1 τ2)).
      { intros k Hk. exists pnil_ready, k. eauto. }
      rewrite <- Ht. eauto.
    - intros. xinv Hs1. constructor.
      + xinv Hs2; cbn; eauto.
      + intros q2 Hq. dependent destruction pj.
        assert (Ht: seq_compose (next (oq q2) τ1) τ2 [= next (oq q2) (seq_compose τ1 τ2)).
        { intros k (k1 & k2 & Hk1 & Hk2 & Hk3). cbn in *; eauto 10. }
        rewrite <- Ht. eauto.
    - intros. xinv Hs1. dependent destruction pj.
      econstructor; eauto.
      assert (Ht: seq_compose (next (pq m2) τ1) τ2 [= next (pq m2) (seq_compose τ1 τ2)).
      { intros k (k1 & k2 & Hk1 & Hk2 & Hk3). cbn in *; eauto 10. }
      rewrite <- Ht. eauto.
    - intros. xinv Hs1. dependent destruction pj.
      eapply rsp_suspended.
      exists (pnil_suspended q2 m2), pnil_ready. repeat apply conj; eauto.
      xinv Hs2; eauto.
    - intros. xinv Hs1. dependent destruction pj.
      econstructor.
      + xinv Hs2; cbn; eauto.
      + intros n2 Hn. 
        assert (Ht: seq_compose (next (oa n2) τ1) τ2 [= next (oa n2) (seq_compose τ1 τ2)).
        { intros k (k1 & k2 & Hk1 & Hk2 & Hk3). cbn in *; eauto 10. }
        rewrite <- Ht. specialize (H9 _ Hn).
        rewrite regular_conv in *; eauto. 1-2: admit.
    - intros. xinv Hs1. dependent destruction pj.
      econstructor; eauto.
      assert (Ht: seq_compose (next (pa r2) τ1) τ2 [= next (pa r2) (seq_compose τ1 τ2)).
      { intros k (k1 & k2 & Hk1 & Hk2 & Hk3). cbn in *; eauto 10. }
      rewrite <- Ht. rewrite regular_conv in *; eauto. 1-2: admit.
  Admitted.

  Lemma rsq_seq_comp {E1 E2 F1 F2} (R S: conv _ _)
    `{!RegularConv R} `{!RegularConv S}
    i j p (σ1 σ2: @strat E1 F1 i) (τ1 τ2: @strat E2 F2 j):
    rsq R S p σ1 τ1 ->
    rsq R S p σ2 τ2 ->
    rsq R S p (seq_compose σ1 σ2) (seq_compose τ1 τ2).
  Proof.
  Abort.

End SEQ_COMP.

Section CLOSURE.

  Obligation Tactic := cbn.

  Context {E F: esig}.

  Inductive closure_has: forall {i}, @strat E F i -> @play E F i -> Prop :=
  | closure_has_nil σ: @closure_has ready σ pnil_ready
  | closure_has_cons i σ s t w:
    Downset.has σ s -> closure_has σ t -> seq_comp_has s t w ->
    @closure_has i σ w.

  Hint Constructors closure_has.
  Hint Resolve (reflexivity (R := pref)).

  Program Definition closure {i} (σ : strat E F i) : strat E F i :=
    {| Downset.has w := closure_has σ w |}.
  Next Obligation.
    intros i σ x y H1 H2. revert x H1. induction H2.
    - intros. xinv H1; eauto.
    - intros x Hx.
      edestruct @seq_comp_has_pref as (s' & t' & Hs' & Ht' & Hw''); eauto.
      specialize (IHclosure_has _ Ht').
      eauto 10 using Downset.closed.
  Qed.

  Lemma closure_unfold {i} (σ: strat E F i):
    seq_compose σ (closure σ) [= closure σ .
  Proof.
    intros w Hw. cbn in *.
    destruct Hw as (s & t & Hs & Ht & Hw).
    econstructor; eauto.
  Qed.

End CLOSURE.

Lemma rsq_closure {E1 E2 F1 F2} (R S: conv _ _)
  `{!RegularConv R} `{!RegularConv S}
  i j p (σ: @strat E1 F1 i) (τ: @strat E2 F2 j):
  rsq R S p σ τ ->
  rsq R S p (closure σ) (closure τ).
Proof.
  intros Hr. cbn. intros s Hs. cbn in Hs.
  revert τ Hr.
  dependent induction Hs.
  - intros. dependent destruction p.
    repeat constructor.
  - intros. specialize (IHHs _ _ Hr).
    unfold rsq in Hr. specialize (Hr _ H).
    rewrite <- closure_unfold.
    eapply rsp_seq_comp; eauto.
Qed.

(** ** §6.1 Embedding *)

From compcert Require Import LanguageInterface Smallstep Globalenvs.

Section SIG.

  Variable li: language_interface.

  Canonical Structure li_sig: esig :=
    {|
      op := Genv.symtbl * query li;
      ar _ := reply li;
    |}.

End SIG.

Coercion li_sig: language_interface >-> esig.

Require Import Classical_Prop.

Section CONV.

  Obligation Tactic := cbn.

  Context {liA liB: language_interface} (cc: callconv liA liB).

  Inductive callconv_conv_has: rcp liA liB -> Prop :=
  | callconv_conv_has_allow m1 m2 se1 se2:
    (exists w, match_senv cc w se1 se2 /\ match_query cc w m1 m2) ->
    callconv_conv_has (rcp_allow (se1, m1) (se2, m2))
  | callconv_conv_has_forbid m1 m2 n1 n2 se1 se2:
    (exists w, match_senv cc w se1 se2 /\ match_query cc w m1 m2 /\
          ~ match_reply cc w n1 n2) ->
    callconv_conv_has (rcp_forbid (se1, m1) (se2, m2) n1 n2)
  | callconv_conv_has_cont m1 m2 n1 n2 se1 se2 k:
    (exists w, match_senv cc w se1 se2 /\ match_query cc w m1 m2 /\
          (match_reply cc w n1 n2 -> callconv_conv_has k)) ->
    callconv_conv_has (rcp_cont (se1, m1) (se2, m2) n1 n2 k).

  Hint Constructors callconv_conv_has.
  Hint Constructors rcp_ref.
  Hint Resolve (reflexivity (R := rcp_ref)).

  Program Canonical Structure callconv_conv: conv liA liB :=
    {| Downset.has w := callconv_conv_has w |}.
  Next Obligation.
    intros x y H1. induction H1; intros Hx; eauto.
    - xinv Hx. destruct H0 as (w & A & B & C). eauto.
    - xinv Hx. destruct H0 as (w & A & B & C). eauto.
    - xinv Hx. destruct H0 as (w & A & B & C). eauto 10.
    - xinv Hx. destruct H0 as (w & A & B & C).
      constructor. exists w. repeat apply conj; eauto.
      intros. exfalso. eauto.
  Qed.

  Lemma rcp_forbid_match_reply w se1 se2 q1 q2:
    match_senv cc w se1 se2 -> match_query cc w q1 q2 ->
    forall r1 r2, ~ Downset.has callconv_conv (rcp_forbid (se1, q1) (se2, q2) r1 r2) ->
             match_reply cc w r1 r2.
  Proof.
    intros Hse Hq * Hr. 
    apply NNPP. intros Hnr.
    apply Hr. constructor. eauto 10.
  Qed.

  Lemma match_reply_rcp_forbid se1 se2 q1 q2 r1 r2:
    (forall w, match_senv cc w se1 se2 /\ match_query cc w q1 q2 /\ match_reply cc w r1 r2) ->
    ~ Downset.has callconv_conv (rcp_forbid (se1, q1) (se2, q2) r1 r2).
  Proof.
  Admitted.

  Instance callconv_regular: RegularConv callconv_conv.
  Proof.
    split. intros * Hm Hn. apply antisymmetry.
    - intros x Hx. cbn in *. xinv Hx. 
      destruct H0 as (w & Hq & Hse & Hr).
      apply Hr. eapply rcp_forbid_match_reply; eauto.
    - intros x Hx. cbn. xinv Hm.
      destruct H0 as (w & Hq & Hse).
      constructor. exists w. eauto.
  Qed.

End CONV.

Section CONV.

  Obligation Tactic := cbn.

  Context {liA liB: language_interface} (cc: callconv liA liB).

  Inductive cc_conv_has: list (ccworld cc) -> rcp liA liB -> Prop :=
  | cc_conv_has_allow m1 m2 se1 se2 w ws
    (HSE: match_senv cc w se1 se2) (HM: match_query cc w m1 m2):
    cc_conv_has (cons w ws) (rcp_allow (se1, m1) (se2, m2))
  | cc_conv_has_forbid m1 m2 n1 n2 se1 se2 w ws
    (HSE: match_senv cc w se1 se2) (HM: match_query cc w m1 m2)
    (HN: ~ match_reply cc w n1 n2):
    cc_conv_has (cons w ws) (rcp_forbid (se1, m1) (se2, m2) n1 n2)
  | cc_conv_has_cont m1 m2 n1 n2 se1 se2 k w ws
    (HSE: match_senv cc w se1 se2) (HM: match_query cc w m1 m2)
    (HK: match_reply cc w n1 n2 -> cc_conv_has ws k):
    cc_conv_has (cons w ws) (rcp_cont (se1, m1) (se2, m2) n1 n2 k).

  Hint Constructors cc_conv_has.
  Hint Constructors rcp_ref.
  Hint Resolve (reflexivity (R := rcp_ref)).

  Program Canonical Structure cc_conv' ws: conv liA liB :=
    {| Downset.has s := cc_conv_has ws s |}.
  Next Obligation.
    intros w x y H1. revert w. induction H1; intros w Hx; try (xinv Hx; eauto).
    constructor; eauto.
    intros. exfalso. eauto.
  Qed.

  Lemma rcp_forbid_mr w ws se1 se2 q1 q2:
    match_senv cc w se1 se2 -> match_query cc w q1 q2 ->
    forall r1 r2, ~ Downset.has (cc_conv' (cons w ws))
               (rcp_forbid (se1, q1) (se2, q2) r1 r2) ->
             match_reply cc w r1 r2.
  Proof.
    intros Hse Hq * Hr.
    apply NNPP. intros Hnr.
    apply Hr. constructor; eauto 10.
  Qed.

  (* Lemma match_reply_rcp_forbid se1 se2 q1 q2 r1 r2: *)
  (*   (forall w, match_senv cc w se1 se2 /\ match_query cc w q1 q2 /\ match_reply cc w r1 r2) -> *)
  (*   ~ Downset.has callconv_conv (rcp_forbid (se1, q1) (se2, q2) r1 r2). *)
  (* Proof. *)
  (* Admitted. *)

  Definition cc_conv := sup ws, cc_conv' ws.

  Instance cc_regular: RegularConv cc_conv.
  Proof.
    split. intros * Hm Hn. apply antisymmetry.
    - intros x Hx. cbn in *.
      destruct Hx as (w & Hx). xinv Hx. exists ws.
      apply HK. eapply rcp_forbid_mr; eauto.
      eapply not_ex_all_not in Hn. apply Hn.
    - intros x Hx. cbn in *.
      destruct Hm as (ws & Hm). xinv Hm.
      destruct Hx as (wt & Hx). exists (cons w wt).
      constructor; eauto.
      Unshelve. exact ws.
  Qed.

End CONV.

Coercion cc_conv: callconv >-> poset_carrier.

Require Import Coqlib.
Close Scope list_scope.

Section LTS.

  Obligation Tactic := cbn.

  Context {liA liB: language_interface} (L: semantics liA liB).

  Inductive state_strat_has (se: Genv.symtbl) (q: query liB) (s: state L): forall {i}, @play liA liB i -> Prop :=
  | state_strat_has_suspended s1 t m
    (STAR: Star (L se) s t s1) (EXT: at_external (L se) s1 m):
    @state_strat_has se q s (running (se, q)) (pq (se, m) :: pnil_suspended (se, q) (se, m))
  | state_strat_has_external s1 s2 t k m n
    (STAR: Star (L se) s t s1) (EXT: at_external (L se) s1 m)
    (AFT: after_external (L se) s1 n s2) (HK: state_strat_has se q s2 k):
    @state_strat_has se q s (running (se, q)) (pq (se, m) :: @oa liA liB (se, q) (se, m) n :: k)
  | state_strat_has_final s1 t r
    (STAR: Star (L se) s t s1) (FIN: final_state (L se) s1 r):
    @state_strat_has se q s (running (se, q)) (@pa liA liB (se, q) r :: pnil_ready).

  Program Definition state_strat se q s i: @strat liA liB i :=
    {| Downset.has w := @state_strat_has se q s i w |}.
  Next Obligation.
    intros *. intros Href H. revert Href. induction H.
    - intros Href. simple inversion Href; try discriminate.
      subst. xsubst. inv H2. xsubst. intros Href'.
      xinv Href'. econstructor; eauto.
    - intros Href. simple inversion Href; try discriminate.
      subst. xsubst. intros Href'. inv H3. xsubst.
      simple inversion Href'; try discriminate.
      + inv H0. xsubst. econstructor; eauto.
      + subst. xsubst. inv H3. xsubst. intros Href''.
        econstructor; eauto.
    - intros Href. simple inversion Href; try discriminate.
      subst. xsubst. inv H2. xsubst.
      intros Href'. xinv Href'. econstructor; eauto.
  Qed.

  Inductive lts_strat_has: forall {i}, @play liA liB i -> Prop :=
  | lts_strat_has_nil: @lts_strat_has ready pnil_ready
  | lts_strat_has_intro se q s k:
    Genv.valid_for (skel L) se ->
    initial_state (L se) q s ->
    state_strat_has se q s k ->
    @lts_strat_has ready (@oq liA liB (se, q) :: k).

  Program Definition lts_strat' i: strat liA liB i :=
    {| Downset.has w := @lts_strat_has i w |}.
  Next Obligation.
    intros. xinv H0.
    - xinv H. constructor.
    - simple inversion H; try discriminate.
      + xsubst. constructor.
      + intros. subst. xsubst. xinv H4.
        econstructor; eauto.
        eapply state_strat_obligation_1; eauto.
  Qed.

  Program Definition lts_strat: strat liA liB ready :=
    closure (lts_strat' ready).

End LTS.

Coercion lts_strat: semantics >-> poset_carrier.

Section RSQ_SUP.

  Context {E1 E2 F1 F2 I} (R: conv E1 E2) (S: I -> conv F1 F2).

  Lemma rsp_sup i1 i2 (p: rspos i1 i2) s τ:
    (forall i, rsp R (S i) p s τ) -> rsp R (lsup S) p s τ.
  Proof.
    intros H. induction s.
    - dependent destruction p.
      constructor. admit.
    - dependent destruction p.
      constructor. admit.
    - Local Opaque lsup.
      dependent destruction p; dependent destruction m.
      + constructor. admit.
        intros q2 Hq.
  Admitted.


  Lemma rsq_sup i1 i2 (p: rspos i1 i2) σ τ:
    (forall i, rsq R (S i) p σ τ) -> rsq R (lsup S) p σ τ.
  Proof.
    intros H i. erewrite sup_lub.
  Admitted.


End RSQ_SUP.

Section FSIM.

  Context {liA1 liA2 liB1 liB2: language_interface}
    (ccA: callconv liA1 liA2) (ccB: callconv liB1 liB2)
    (L1: semantics liA1 liB1) (L2: semantics liA2 liB2)
    (FSIM: forward_simulation ccA ccB L1 L2).

  Hint Constructors state_strat_has lts_strat_has.

  Lemma fsim_rsq: rsq (cc_conv ccA) (cc_conv ccB) rs_ready L1 L2.
  Proof.
    apply rsq_closure; try apply cc_regular.
    apply rsq_sup. intros ws.
    intros p Hp. cbn in Hp. xinv Hp. { repeat constructor. }
    constructor. { constructor. }
    intros q2 Hq2. cbn in Hq2.
    rename q into q1. destruct q2 as (se2 & q2).
    xinv Hq2. rename ws0 into ws.
    destruct FSIM. destruct X.
    specialize (fsim_lts _ _ _ HSE H0).
    rename s into s1. rename se into se1.
    edestruct (@fsim_match_initial_states) as (i & s2 & A & B); eauto.
    assert (Hs: state_strat L2 se2 q2 s2 (running (se2, q2))
                  [= (next (oq (se2, q2)) (lts_strat' L2 ready))).
    { intros p Hp. cbn in *. econstructor; eauto.
      eapply match_senv_valid_for in HSE. apply HSE.
      rewrite <- fsim_skel. eauto. }
    rewrite <- Hs. clear Hs fsim_skel fsim_footprint A H0 H1.
    revert i s2 B. dependent induction H2; intros i ts Hts.
    - edestruct @simulation_star as (i1 & ts1 & A & B); eauto.
      edestruct @fsim_match_external as (wx & tq2 & C & D & E & F); eauto.
      eapply rsp_pq. exists (cons wx nil). constructor; eauto.
      eapply rsp_suspended. cbn. econstructor; eauto.
    - edestruct @simulation_star as (i1 & ts1 & A & B); eauto.
      edestruct @fsim_match_external as (wx & tq2 & C & D & E & F); eauto.
      eapply rsp_pq. exists (cons wx nil). constructor; eauto.
      eapply rsp_oa. cbn. econstructor; eauto.
      intros n2 Hn.
      rewrite @regular_conv. 2: apply cc_regular.
      2: { exists (cons wx nil). constructor; eauto. }
      2: apply Hn.
      cbn in Hn. eapply not_ex_all_not with (n := (cons wx nil)) in Hn.
      eapply rcp_forbid_mr in Hn; eauto.
      specialize (F _ _ _ Hn AFT) as (i' & ts2 & X & Y).
      exploit IHstate_strat_has; eauto. intros Z.
      assert (Hs: state_strat L2 se2 q2 ts2 (running (se2, q2))
               [= next (oa n2) (next (pq (se2, tq2)) (state_strat L2 se2 q2 ts (running (se2, q2))))).
      { intros p Hp. cbn in *. econstructor; eauto. }
      rewrite <- Hs. apply Z.
    - edestruct (@simulation_star) as (i1 & ts1 & A & B); eauto.
      clear Hts.
      edestruct (@fsim_match_final_states) as (r2 & C & D); eauto.
      eapply rsp_pa with (r3 := r2).
      + intros Hr. xinv Hr. eauto.
      + constructor. cbn. econstructor; eauto.
    Qed.

End FSIM.

Section FSIM.

  Context {liA1 liA2 liB1 liB2: language_interface}
    (ccA: callconv liA1 liA2) (ccB: callconv liB1 liB2)
    (L1: semantics liA1 liB1) (L2: semantics liA2 liB2)
    (FSIM: forward_simulation ccA ccB L1 L2).

  Hint Constructors state_strat_has lts_strat_has.

  Lemma fsim_rsq: rsq ccA ccB rs_ready L1 L2.
  Proof.
    apply rsq_closure; try apply callconv_regular.
    intros p Hp. cbn in Hp. xinv Hp. { repeat constructor. }
    constructor. { constructor. }
    intros q2 Hq2. cbn in Hq2. 
    rename q into q1. destruct q2 as (se2 & q2).
    xinv Hq2. subst. destruct H3 as (w & Hse & Hq).
    destruct FSIM. destruct X.
    specialize (fsim_lts _ _ _ Hse H0).
    rename s into s1. rename se into se1.
    edestruct (@fsim_match_initial_states) as (i & s2 & A & B); eauto.
    assert (Hs: state_strat L2 se2 q2 s2 (running (se2, q2))
                  [= (next (oq (se2, q2)) (lts_strat' L2 ready))).
    { intros p Hp. cbn in *. econstructor; eauto.
      eapply match_senv_valid_for in Hse. apply Hse.
      rewrite <- fsim_skel. eauto. }
    rewrite <- Hs. clear Hs fsim_skel fsim_footprint A H0 H1.
    revert i s2 B. dependent induction H2; intros i ts Hts.
    - edestruct @simulation_star as (i1 & ts1 & A & B); eauto.
      edestruct @fsim_match_external as (wx & tq2 & C & D & E & F); eauto.
      eapply rsp_pq. constructor. exists wx. split; eauto.
      eapply rsp_suspended. cbn. econstructor; eauto.
    - edestruct @simulation_star as (i1 & ts1 & A & B); eauto.
      edestruct @fsim_match_external as (wx & tq2 & C & D & E & F); eauto.
      eapply rsp_pq. constructor. exists wx. split; eauto.
      eapply rsp_oa. cbn. econstructor; eauto.
      intros n2 Hn. eapply rcp_forbid_match_reply in Hn; eauto.
      specialize (F _ _ _ Hn AFT) as (i' & ts2 & X & Y).
      exploit IHstate_strat_has; eauto. intros Z.
      rewrite @regular_conv. 2: apply callconv_regular.
      2: { constructor. eauto. }
      2: {

      (* intros Hr. xinv Hr. destruct H0 as (wt & HA & HB & HC). *)
        admit.

      }
      assert (Hs: state_strat L2 se2 q2 ts2 (running (se2, q2))
               [= next (oa n2) (next (pq (se2, tq2)) (state_strat L2 se2 q2 ts (running (se2, q2))))).
      { intros p Hp. cbn in *. econstructor; eauto. }
      rewrite <- Hs. apply Z. 
    - edestruct (@simulation_star) as (i1 & ts1 & A & B); eauto.
      clear Hts.
      edestruct (@fsim_match_final_states) as (r2 & C & D); eauto.
      eapply rsp_pa with (r3 := r2).
      + intros Hr. xinv Hr. admit.
      + constructor. cbn. econstructor; eauto.
    Admitted.

End FSIM.


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

  Lemma vcomp_has_inv_ex σ τ w :
    vcomp_has σ τ w ->
    exists s t, Downset.has σ s /\ Downset.has τ t.
  Proof.
    destruct w; cbn; firstorder.
  Qed.

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

  Lemma rcnext_vcomp1 m1 m3 n1 n3 R S m2 n2:
    rcnext m1 m3 n1 n3 (vcomp R S) [=
    vcomp (rcnext m1 m2 n1 n2 R) (rcnext m2 m3 n2 n3 S).
  Proof.
  Admitted.

  Lemma rcnext_vcomp2 m1 m3 n1 n3 R S m2 n2:
   Downset.has R (rcp_allow m1 m2) ->
   Downset.has S (rcp_allow m2 m3) ->
   ~ Downset.has R (rcp_forbid m1 m2 n1 n2) ->
   ~ Downset.has S (rcp_forbid m2 m3 n2 n3) ->
   vcomp (rcnext m1 m2 n1 n2 R) (rcnext m2 m3 n2 n3 S) [=
   rcnext m1 m3 n1 n3 (vcomp R S).
  Proof.
    intros A B C D x Hx. cbn in *.
    exists m2. repeat apply conj; eauto.
    intros n2'.


  Admitted.

  Lemma rcnext_vcomp' m1 m2 m3 n1 n2 n3 R S :
    rcnext m1 m3 n1 n3 (vcomp (rctrim m1 m2 n1 n2 R) (rctrim m2 m3 n2 n3 S)) =
    vcomp (rcnext m1 m2 n1 n2 R) (rcnext m2 m3 n2 n3 S).
  Proof.
    apply antisymmetry; intros s; cbn.
    - intros (xm2 & Hm12 & Hm23 & Hn).
      assert (xm2 = m2) by (inversion Hm12; auto); subst.
      specialize (Hn n2); destruct Hn as [? | [? | ?]]; auto.
      +
  Abort.
End VCOMP.

(** *** Theorem 4.7 (Veritcal composition of refinement squares) *)

Section RSVCOMP.
  Context {E1 F1 E2 F2 E3 F3 : esig}.

  Variant rsvpos : forall {p1 p2 p3}, @rspos E1 E2 F1 F2 p1 p2 -> @rspos E2 E3 F2 F3 p2 p3 -> @rspos E1 E3 F1 F3 p1 p3 -> Type :=
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
          Downset.has S (rcp_allow q1 q2) ->
          Downset.has S' (rcp_allow q2 q3) ->
          rsp (vcomp R R') (vcomp S S') p13 s1 σ3
        | rsv_suspended q1 q2 q3 m1 m2 m3 =>
          Downset.has S (rcp_allow q1 q2) ->
          Downset.has S' (rcp_allow q2 q3) ->
          Downset.has R (rcp_allow m1 m2) ->
          Downset.has R' (rcp_allow m2 m3) ->
          rsp (vcomp R R') (vcomp S S') p13 s1 σ3
      end.
  Proof.
    intros R R' S S' s1 σ2 σ3 Hσ2 Hσ3 H12 Hσ23.
    revert p3 p23 p13 p R' S' σ3 Hσ3 Hσ23.
    induction H12; dependent destruction p; intros.
    - (* ready *)
      specialize (Hσ23 _ H).
      dependent destruction Hσ23.
      constructor; auto.
    - (* incoming question *)
      pose proof (Hσ23 _ H) as Hnil.
      dependent destruction Hnil.
      constructor; auto. cbn.
      intros q3 (q2 & Hq12 & Hq23).
      eapply (H1 q2 Hq12 _ _ _ _ (rsv_running q1 q2 q3)); eauto with typeclass_instances.
      eapply rsq_next_oq; eauto.
    - (* outgoing question *)
      rename q4 into q3.
      assert (Hm2 : Downset.has τ (pq m2 :: pnil_suspended q2 m2))
        by (dependent destruction H12; cbn in *; auto).
      edestruct @rsq_next_pq as (m3 & Hm23 & Hm3 & Hnext); eauto.
      econstructor; cbn; eauto.
      eapply (IHrsp _ _ _ _ (rsv_suspended q1 q2 q3 m1 m2 m3)); eauto with typeclass_instances.
    - (* suspended *)
      pose proof (Hσ23 _ H) as Hnil.
      dependent destruction Hnil.
      constructor; auto.
    - (* environment answer *)
      rename q4 into q3, m4 into m3.
      pose proof (Hσ23 _ H) as Hnil.
      dependent destruction Hnil.
      constructor; auto. cbn.
      intros n3 Hn.
      apply not_ex_all_not with (n := m2) in Hn.
      apply not_and_or in Hn as [? | Hn]; try tauto.
      apply not_and_or in Hn as [? | Hn]; try tauto.
      apply not_all_ex_not in Hn as (n2 & Hn).
      apply not_or_and in Hn as (Hn12 & Hn23).
      rewrite <- rcnext_vcomp2.
      eapply (H1 n2 Hn12 _ _ _ _ (rsv_running q1 q2 q3)); eauto with typeclass_instances.
      eapply rsq_next_oa; eauto.

      rewrite <- (fsup_ub m2) by auto.
      rewrite <- finf_glb.
      + eapply (H1 n2 Hn12 _ _ _ _ (rsv_running q1 q2 q3)); eauto with typeclass_instances.
        eapply rsq_next_oa; eauto.
      + intros ? _. admit.
      apply not_and_or in Hn23. destruct Hn23; try tauto.

  Lemma rsq_vcomp {p1 p2 p3 p12 p23 p13} (p : @rsvpos p1 p2 p3 p12 p23 p13) :
    forall (R : conv E1 E2) (R' : conv E2 E3) (S : conv F1 F2) (S' : conv F2 F3)
           (σ1 : strat E1 F1 p1) (σ2 : strat E2 F2 p2) (σ3 : strat E3 F3 p3)
           `{Hσ2 : !Deterministic σ2} `{Hσ3 : !Deterministic σ3},
      rsq R S p12 σ1 σ2 ->
      rsq R' S' p23 σ2 σ3 ->
      match p with
        | rsv_ready =>
          rsp (vcomp R R') (vcomp S S') p13 s1 σ3
        | rsv_running q1 q2 q3 =>
          Downset.has S (rcp_allow q1 q2) ->
          Downset.has S' (rcp_allow q2 q3) ->
          rsp (vcomp R R') (vcomp S S') p13 s1 σ3
        | rsv_suspended q1 q2 q3 m1 m2 m3 =>
          Downset.has S (rcp_allow q1 q2) ->
          Downset.has S' (rcp_allow q2 q3) ->
          Downset.has R (rcp_allow m1 m2) ->
          Downset.has R' (rcp_allow m2 m3) ->
          rsp (vcomp R R') (vcomp S S') p13 s1 σ3
      end.

      rsq (vcomp R R') (vcomp S S') p13 σ1 σ3.
  Proof.
    intros R R' S S' σ1 σ2 σ3 Hσ2 Hσ3 Hσ12 Hσ23 s1 Hs1.
    specialize (Hσ12 s1 Hs1). clear σ1 Hs1.
    cut
    { destruct p; auto. }


    revert p3 p23 p13 p R' S' σ3 Hσ3 Hσ23.
    induction Hσ12; intros.
    - (* ready *)
      inversion p; clear p; xsubst.
      specialize (Hσ23 _ H).
      dependent destruction Hσ23.
      constructor; auto.
    - (* incoming question *)
      inversion p; clear p; xsubst.
      pose proof (Hσ23 _ H) as Hnil.
      dependent destruction Hnil.
      constructor; auto. cbn.
      intros q3 (q2 & Hq12 & Hq23).
      eapply (H1 q2 Hq12 _ _ _ _ (rsv_running q1 q2 q3)); eauto with typeclass_instances.
      eapply rsq_next_oq; eauto.
    - (* outgoing question *)
      inversion p; clear p; xsubst. rename q4 into q3.
      assert (Hm2 : Downset.has τ (pq m2 :: pnil_suspended q2 m2))
        by (dependent destruction Hσ12; cbn in *; auto).
      edestruct @rsq_next_pq as (m3 & Hm23 & Hm3 & Hnext); eauto.
      econstructor; cbn; eauto.
      eapply IHHσ12; eauto with typeclass_instances.
      constructor.
    - (* suspended *)
      inversion p; clear p; xsubst.
      pose proof (Hσ23 _ H) as Hnil.
      dependent destruction Hnil.
      constructor; auto.
    - (* environment answer *)
      inversion p; clear p; xsubst. rename q4 into q3, m4 into m3.
      pose proof (Hσ23 _ H) as Hnil.
      dependent destruction Hnil.
      constructor; auto. cbn.
      intros n3 Hn23.
      apply not_ex_all_not with (n := m2) in Hn23.
      apply not_and_or in Hn23.

      econstructor.

 (n2 & Hn12 & Hn23).
      eapply (H1 q2 Hq12 _ _ _ _ (rsv_running q1 q2 q3)); eauto with typeclass_instances.
      eapply rsq_next_oq; eauto.

      pose proof (H


      edestruct @rsq_next_pq as (m3 & Hm23 & Hm3 & Hnext); eauto.

      assert (Hm2 : Downset.has τ (pq m2 :: pnil_suspended q2 m2))
        by (dependent destruction Hσ12; cbn in *; auto).
      edestruct @rsq_next_pq as (m3 & Hm23 & Hm3 & Hnext); eauto.
      econstructor; cbn; eauto.

      specialize (Hσ23 _

 clear - Hσ12.


  Context {R : conv E1 E2} {R' : conv E2 E3}
  Context {S : conv E
  Context {E1 F1 G1} (R1 : conv E1 F1) (S1 : conv F1 G1).
  Context {E2 F2 G2} (R2 : conv E2 F2) (υ
