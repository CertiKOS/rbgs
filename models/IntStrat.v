Require Import Classical.
Require Import Program.Equality.
Require Import LogicalRelations.
Require Import Poset.
Require Import Lattice.
Require Import Downset.


(** * §2 COMPOSITIONAL SEMANTICS FOR VERIFICATION *)

(** This section introduces the basic definitions below. However, for
  the most part it is a high-level overview of the framework which is
  formally defined in the following section. We have formalized
  examples separately; see [examples/CompCertStrat.v]. *)

(** ** §2.2 Effect Signatures *)

(** *** Definition 2.1 (Effect signature) *)

Record esig :=
  {
    op :> Type;
    ar : op -> Type;
  }.

Arguments ar {_}.
Declare Scope esig_scope.
Delimit Scope esig_scope with esig.
Bind Scope esig_scope with esig.

(** ** §2.6 Combining Effect Signatures *)

(** *** Definition 2.9 (Sum of signatures) *)

(** We only formalize the binary and nullary cases. *)

Canonical Structure fcomp E F :=
  {|
    op := op E + op F;
    ar m := match m with inl m | inr m => ar m end;
  |}.

Infix "+" := fcomp : esig_scope.

Canonical Structure Empty_sig :=
  {|
    op := Empty_set;
    ar m := match m with end;
  |}.

Notation "0" := Empty_sig : esig_scope.


(** * §3 STRATEGY MODEL *)

(** ** §3.1 Strategies *)

Section STRAT.
  Context {E F : esig}.

  (** *** Def 3.1 (Strategy) *)

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
      dependent destruction Hyz; constructor; auto.
  Qed.
  Next Obligation.
    intros x y Hxy Hyx.
    induction Hxy; dependent destruction Hyx; auto;
    elim IHHxy; auto.
  Qed.

  Definition strat (p : position) :=
    downset (play_poset p).

  (** *** Useful lemmas *)

  Lemma strat_closed {p} (σ : strat p) (s t : play p) :
    Downset.has σ t ->
    pref s t ->
    Downset.has σ s.
  Proof.
    eauto using Downset.closed.
  Qed.

  Lemma strat_has_any_pnil_ready (σ : strat ready) (s : play ready) :
    Downset.has σ s ->
    Downset.has σ pnil_ready.
  Proof.
    eauto using strat_closed, pnil_ready_pref.
  Qed.

  Lemma strat_has_any_pnil_suspended {q m} (σ : strat (suspended q m)) s :
    Downset.has σ s ->
    Downset.has σ (pnil_suspended q m).
  Proof.
    eauto using strat_closed, pnil_suspended_pref.
  Qed.

  Lemma pcons_eq_inv_l {i j} (m1 m2 : move i j) (s1 s2 : play j) :
    pcons m1 s1 = pcons m2 s2 -> m1 = m2.
  Proof.
    intro H. dependent destruction H. reflexivity.
  Qed.

  Lemma pcons_eq_inv_r {i j} (m1 m2 : move i j) (s1 s2 : play j) :
    pcons m1 s1 = pcons m2 s2 -> s1 = s2.
  Proof.
    intro H. dependent destruction H. reflexivity.
  Qed.

  Lemma oa_eq_inv q m n1 n2 :
    @oa q m n1 = @oa q m n2 -> n1 = n2.
  Proof.
    intro H. dependent destruction H. reflexivity.
  Qed.

  Lemma pa_eq_inv q r1 r2 :
    @pa q r1 = @pa q r2 -> r1 = r2.
  Proof.
    intro H. dependent destruction H. reflexivity.
  Qed.

  (** *** Determinism *)

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

  Lemma pcoh_inv_pq {q} (m1 m2 : E) (s1 s2 : play (suspended q _)) :
    pcoh (pcons (pq m1) s1) (pcons (pq m2) s2) ->
    m1 = m2.
  Proof.
    intros H. dependent destruction H. auto.
  Qed.

  Lemma pcoh_inv_pa {q} (r1 r2 : ar q) (s1 s2 : play ready) :
    pcoh (pcons (pa r1) s1) (pcons (pa r2) s2) ->
    r1 = r2.
  Proof.
    intros H. dependent destruction H. auto.
  Qed.

  (** *** Residuals *)

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

Notation "E ->> F" := (strat E F ready) (at level 55, right associativity).
Declare Scope strat_scope.
Delimit Scope strat_scope with strat.
Bind Scope strat_scope with strat.
Open Scope strat_scope.

(** To make using determinism properties easier, we provide the
  [determinism] tactic below. Additional hints in the [determinism]
  database can used to establish that the strategy makes particular
  moves. *)

Global Hint Resolve determinism pcoh_inv_pq pcoh_inv_pa : determinism.

Global Hint Extern 1 (Downset.has ?σ (?e :: ?s)) =>
       change (Downset.has (next e σ) s) : determinism.

Ltac determinism m m' :=
  assert (m' = m) by eauto 10 with determinism;
  subst m'.

(** ** §3.2 Layered Composition *)

(** *** Def 3.4 (Layered Composition of Strategies) *)

Section ID.
  Context {E : esig}.
  Obligation Tactic := cbn.

  Variant idpos : @position E E -> Type :=
    | id_ready : idpos ready
    | id_suspended m : idpos (suspended m m).

  Inductive id_has : forall {i}, idpos i -> @play E E i -> Prop :=
    | id_has_pnil_ready :
        id_has id_ready pnil_ready
    | id_has_q m s :
        id_has (id_suspended m) s ->
        id_has id_ready (oq m :: pq m :: s)
    | id_has_pnil_suspended m :
        id_has (id_suspended m) (@pnil_suspended E E m m)
    | id_has_a {m} (n : ar m) s :
        id_has id_ready s ->
        id_has (id_suspended m) (oa n :: pa n :: s).

  Program Definition id_when {i} (p : idpos i) : strat E E i :=
    {| Downset.has := id_has p |}.
  Next Obligation.
    intros i p s t Hst Ht.
    induction Ht; repeat (dependent destruction Hst; try constructor; eauto).
  Qed.
End ID.

Notation id E := (id_when (E:=E) id_ready).

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

  Hint Constructors comp_has : core.
  Hint Constructors pref : core.
  Hint Resolve (fun E F i => reflexivity (R := @pref E F i)) : core.

  Lemma comp_has_pref {i j k} (p : cpos i j k) s t w :
    comp_has p s t w ->
    forall w', w' [= w -> exists s' t', s' [= s /\ t' [= t /\ comp_has p s' t' w'.
  Proof.
    induction 1; cbn in *.
    - (* ready *)
      intros w' Hw'.
      dependent destruction Hw'; eauto.
    - (* incoming question *)
      intros w' Hw'.
      dependent destruction w'; eauto.
      dependent destruction Hw'.
      edestruct IHcomp_has as (s' & t' & Hs' & Ht' & Hw''); eauto 10.
    - (* internal question *)
      intros w' Hw'.
      edestruct IHcomp_has as (s' & t' & Hs' & Ht' & Hw''); eauto 10.
    - (* outgoing question *)
      intros w' Hw'.
      dependent destruction w'; eauto.
      dependent destruction Hw'.
      edestruct IHcomp_has as (s' & t' & Hs' & Ht' & Hw''); eauto 10.
    - (* waiting for answer *)
      intros w' Hw'.
      dependent destruction w'; eauto.
      inversion Hw'.
    - (* outgoing question is answered *)
      intros w' Hw'.
      dependent destruction w'; eauto.
      dependent destruction Hw'.
      edestruct IHcomp_has as (s' & t' & Hs' & Ht' & Hw''); eauto 10.
    - (* internal answer *)
      intros w' Hw'.
      edestruct IHcomp_has as (s' & t' & Hs' & Ht' & Hw''); eauto 10.
    - (* incoming question is answered *)
      intros w' Hw'.
      dependent destruction w'; eauto.
      dependent destruction Hw'.
      edestruct IHcomp_has as (s' & t' & Hs' & Ht' & Hw''); eauto 10.
  Qed.

  Program Definition compose_when {i j k} p (σ : strat F G i) (τ : strat E F j) : strat E G k :=
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
    Deterministic (@compose_when i j k p σ τ).
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
    compose_when (cpos_left q) (next (oq q) σ) τ =
    next (oq q) (compose_when cpos_ready σ τ).
  Proof.
    apply antisymmetry; cbn.
    - intros w' (s & t & Hs & Ht & Hstw').
      eauto 10.
    - intros w' (s & t & Hs & Ht & Hstw').
      dependent destruction Hstw'. eauto.
  Qed.

  Lemma compose_next_lq {q} m σ τ :
    compose_when (cpos_right q m) (next (pq m) σ) (next (oq m) τ) [=
    compose_when (cpos_left q) σ τ.
  Proof.
    intros w (s & t & Hs & Ht & Hw). cbn in Hs, Ht.
    econstructor; eauto.
  Qed.

  Lemma compose_next_rq {q m} u σ τ :
    compose_when (cpos_suspended q m u) σ (next (pq u) τ) [=
    next (pq u) (compose_when (cpos_right q m) σ τ).
  Proof.
    intros w' (s & t & Hs & Ht & Hw). cbn in Ht.
    econstructor; eauto.
  Qed.

  Lemma compose_next_oa {q m u} v σ τ :
    compose_when (cpos_right q m) σ (next (oa v) τ) =
    next (oa v) (compose_when (cpos_suspended q m u) σ τ).
  Proof.
    apply antisymmetry.
    - intros w' (s & t & Hs & Ht & Hw'). cbn in Ht |- *.
      eauto 10.
    - intros w' (s & t & Hs & Ht & Hw'). cbn.
      dependent destruction Hw'. eauto.
  Qed.

  Lemma compose_next_ra {q m} n σ τ :
    compose_when (cpos_left q) (next (oa n) σ) (next (pa n) τ) [=
    compose_when (cpos_right q m) σ τ.
  Proof.
    intros w' (s & t & Hs & Ht & Hw'). cbn in Hs, Ht |- *.
    eauto 10.
  Qed.

  Lemma compose_next_la {q} r σ τ :
    compose_when cpos_ready (next (pa r) σ) τ [=
    next (pa r) (compose_when (cpos_left q) σ τ).
  Proof.
    intros w' (s & t & Hs & Ht & Hw'). cbn in Hs |- *.
    eauto 10.
  Qed.
End COMPOSE.

Notation compose := (compose_when cpos_ready).
Infix "⊙" := compose (at level 45, right associativity) : strat_scope.

(** *** Theorem 3.5 (Properties of Layered Composition) *)

Section COMPOSE_ID.
  Context {E F : esig}.

  Hint Constructors id_has comp_has : core.

  (** When the identity is composed on the left,
    it passes through incoming interactions unchanged. *)

  Definition id_pos_l (i : @position E F) : @position F F :=
    match i with
      | ready => ready
      | running q => suspended q q
      | suspended q m => suspended q q
    end.

  Definition id_idpos_l i : idpos (id_pos_l i) :=
    match i with
      | ready => id_ready
      | running q => id_suspended q
      | suspended q m => id_suspended q
    end.

  Definition id_cpos_l i : cpos (id_pos_l i) i i :=
    match i with
      | ready => cpos_ready
      | running q => cpos_right q q
      | suspended q m => cpos_suspended q q m
    end.

  Lemma compose_id_has_l_gt {i} (s : @play E F i) :
    exists t, id_has (id_idpos_l i) t /\ comp_has (id_cpos_l i) t s s.
  Proof.
    induction s; cbn; eauto 10.
    destruct IHs as (t & Ht & Hst).
    dependent destruction m; cbn in *; eauto 10.
  Qed.

  Lemma compose_id_has_l_lt {i} (s s': @play E F i) (t: @play F F (id_pos_l i)):
    id_has (id_idpos_l i) t ->
    comp_has (id_cpos_l i) t s s' ->
    s' [= s.
  Proof.
    revert t s'.
    induction s; cbn; intros t s' Ht Hs'.
    - dependent destruction Hs'. { constructor. }
      dependent destruction Ht.
      dependent destruction Hs'.
    - dependent destruction Hs'. constructor.
    - dependent destruction Hs'; cbn in *.
      + constructor.
      + dependent destruction Ht.
        dependent destruction Hs'.
        constructor; eauto.
      + constructor; eauto.
      + constructor; eauto.
      + dependent destruction Ht.
        dependent destruction Hs'.
        constructor; eauto.
  Qed.

  Lemma compose_id_l_when i (σ : strat E F i) :
    compose_when (id_cpos_l i) (id_when (id_idpos_l i)) σ = σ.
  Proof.
    apply antisymmetry; cbn.
    - intros w (s & t & Hs & Ht & Hw).
      eapply Downset.closed; eauto using compose_id_has_l_lt.
    - intros s Hs.
      edestruct (compose_id_has_l_gt s) as (t & Ht & Hst); eauto.
  Qed.

  Lemma compose_id_l (σ : E ->> F) :
    id F ⊙ σ = σ.
  Proof.
    apply compose_id_l_when.
  Qed.

  (** Likewise, when the identity is composed on the right,
    it passes through outgoing interactions unchanged. *)

  Definition id_pos_r (i : @position E F) : @position E E :=
    match i with
      | ready => ready
      | running q => ready
      | suspended q m => suspended m m
    end.

  Definition id_idpos_r i : idpos (id_pos_r i) :=
    match i with
      | ready => id_ready
      | running q => id_ready
      | suspended q m => id_suspended m
    end.

  Definition id_cpos_r i : cpos i (id_pos_r i) i :=
    match i with
      | ready => cpos_ready
      | running q => cpos_left q
      | suspended q m => cpos_suspended q m m
    end.

  Lemma compose_id_has_r_gt {i} (s : @play E F i) :
    exists t, id_has (id_idpos_r i) t /\ comp_has (id_cpos_r i) s t s.
  Proof.
    induction s; cbn; eauto 10.
    destruct IHs as (t & Ht & Hst).
    dependent destruction m; cbn in *; eauto 10.
  Qed.

  Lemma compose_id_has_r_lt {i} (s s': @play E F i) (t: @play E E (id_pos_r i)):
    id_has (id_idpos_r i) t ->
    comp_has (id_cpos_r i) s t s' ->
    s' [= s.
  Proof.
    revert t s'.
    induction s; cbn; intros t s' Ht Hs'.
    - dependent destruction Hs'. constructor.
    - dependent destruction Hs'. { constructor. }
      dependent destruction Ht.
      dependent destruction Hs'.
    - dependent destruction Hs'; cbn in *.
      + constructor; eauto.
      + dependent destruction Ht.
        dependent destruction Hs'.
        constructor; eauto.
      + constructor; eauto.
      + dependent destruction Ht.
        dependent destruction Hs'.
        constructor; eauto.
      + constructor; eauto.
  Qed.

  Lemma compose_id_r_when i (σ : strat E F i) :
    compose_when (id_cpos_r i) σ (id_when (id_idpos_r i)) = σ.
  Proof.
    apply antisymmetry; cbn.
    - intros w (s & t & Hs & Ht & Hw).
      eapply Downset.closed; eauto using compose_id_has_r_lt.
    - intros s Hs.
      edestruct (compose_id_has_r_gt s) as (t & Ht & Hst); eauto.
  Qed.

  Lemma compose_id_r (σ : E ->> F) :
    σ ⊙ id E = σ.
  Proof.
    apply compose_id_r_when.
  Qed.
End COMPOSE_ID.

Section COMPOSE_COMPOSE.
  Context {E F G H : esig}.

  Variant ccpos :
    forall {iσ iτ iυ iστ iτυ iστυ}, @cpos F G H iσ iτ iστ ->
                                    @cpos E F G iτ iυ iτυ ->
                                    @cpos E G H iσ iτυ iστυ ->
                                    @cpos E F H iστ iυ iστυ -> Type :=
    | ccpos_ready :
        ccpos cpos_ready
              cpos_ready
              cpos_ready
              cpos_ready
    | ccpos_left q1 :
        ccpos (cpos_left q1)
              cpos_ready
              (cpos_left q1)
              (cpos_left q1)
    | ccpos_mid q1 q2 :
        ccpos (cpos_right q1 q2)
              (cpos_left q2)
              (cpos_right q1 q2)
              (cpos_left q1)
    | ccpos_right q1 q2 q3 :
        ccpos (cpos_suspended q1 q2 q3)
              (cpos_right q2 q3)
              (cpos_right q1 q2)
              (cpos_right q1 q3)
    | ccpos_suspended q1 q2 q3 q4 :
        ccpos (cpos_suspended q1 q2 q3)
              (cpos_suspended q2 q3 q4)
              (cpos_suspended q1 q2 q4)
              (cpos_suspended q1 q3 q4).

  Hint Constructors pref comp_has : core.

  Ltac destruct_comp_has :=
    repeat
      match goal with
      | H : comp_has _ (_ _) _ _ |- _ => dependent destruction H
      | H : comp_has _ _ (_ _) _ |- _ => dependent destruction H
      | H : comp_has _ _ _ (_ _) |- _ => dependent destruction H
      | p : ccpos _ _ _ _ |- _ => dependent destruction p
      end.

  Lemma comp_has_assoc_1 {iσ iτ iυ iστ iτυ iστυ pστ pτυ pσ_τυ pστ_υ} :
    @ccpos iσ iτ iυ iστ iτυ iστυ pστ pτυ pσ_τυ pστ_υ ->
    forall s t st u stu,
      comp_has pστ s t st ->
      comp_has pστ_υ st u stu ->
      exists s' t' u' tu,
        s' [= s /\ t' [= t /\ u' [= u /\
        comp_has pτυ t' u' tu /\
        comp_has pσ_τυ s' tu stu.
  Proof.
    intros p s t st u stu Hst Hst_u. cbn.
    revert iυ iτυ iστυ pτυ pσ_τυ pστ_υ p u stu Hst_u.
    induction Hst; intros; cbn.
    - (* ready *)
      destruct_comp_has; eauto 10.
    - (* environment question *)
      destruct_comp_has; eauto 10.
      rename t0 into u, w into st, w0 into stu.
      edestruct (IHHst _ _ _ _ _ _ (ccpos_left q) u stu Hst_u)
        as (s' & t' & u' & tu & Hs' & Ht' & Hu' & Htu & Hs_tu).
      eauto 100.
    - (* question of [σ] *)
      destruct_comp_has; eauto 10.
      rename w into st.
      destruct (IHHst _ _ _ _ _ _ (ccpos_mid q m) u stu Hst_u)
        as (s' & t' & u' & tu & Hs' & Ht' & Hu' & Htu & Hs_tu).
      eauto 100.
    - (* question of [τ] *)
      destruct_comp_has; eauto 10.
      rename u into x, w into st, t0 into u, w0 into stu.
      destruct (IHHst _ _ _ _ _ _ (ccpos_right q m x) u stu Hst_u)
        as (s' & t' & u' & tu & Hs' & Ht' & Hu' & Htu & Hs_tu).
      eauto 100.
    - (* [στ] suspended, note that [υ] may still do its thing for a while *)
      rename u into x, u0 into u.
      revert iτυ iστυ pτυ pστ_υ pσ_τυ p stu Hst_u.
      induction u as [ | xx e | ? ? [ | ? e | ? e f | xx yy] u IHu]; intros;
      dependent destruction p;
      dependent destruction Hst_u;
      eauto 100.
      + (* question of [υ] *)
        rename q0 into x.
        edestruct (IHu _ _ _ _ _ (ccpos_suspended q m x e))
          as (s' & t' & u' & tu & Hs' & Ht' & Hu' & Htu & Hs_tu); eauto 100.
      + (* environment answer *)
        rename q0 into x.
        edestruct (IHu _ _ _ _ _ (ccpos_right q m x))
          as (s' & t' & u' & tu & Hs' & Ht' & Hu' & Htu & Hs_tu); eauto 100.
    - (* answer of [υ] -- note that as above, [u] could perform a series of
        interaction with the environment before the answer which
        synchronizes with [st] appears, hence we have to do the same
        induction on [u] as we wait, but now an answer of [υ] is
        possible and has us continue the top-level induction. *)
      rename u into x, v into y, w into st, u0 into u.
      revert iτυ iστυ pτυ pστ_υ pσ_τυ p stu Hst_u.
      induction u as [ | xx e | ? ? [ | ? e | ? e f | xx yy] u IHu]; intros;
      dependent destruction p;
      dependent destruction Hst_u;
      eauto 100.
      + (* question of [υ] *)
        rename q0 into x.
        edestruct (IHu _ _ _ _ _ (ccpos_suspended q m x e))
          as (s' & t' & u' & tu & Hs' & Ht' & Hu' & Htu & Hs_tu); eauto 100.
      + (* environment answer *)
        rename q0 into x.
        edestruct (IHu _ _ _ _ _ (ccpos_right q m x))
          as (s' & t' & u' & tu & Hs' & Ht' & Hu' & Htu & Hs_tu); eauto 100.
      + (* answer of [υ] *)
        rename xx into x, yy into y.
        edestruct (IHHst _ _ _ _ _ _ (ccpos_mid q m))
          as (s' & t' & u' & tu & Hs' & Ht' & Hu' & Htu & Hs_tu); eauto 100.
    - (* answer of [τ] *)
      rename w into st.
      dependent destruction p.
      edestruct (IHHst _ _ _ _ _ _ (ccpos_left q))
        as (s' & t' & u' & tu & Hs' & Ht' & Hu' & Htu & Hs_tu); eauto 100.
    - (* answer of [σ] *)
      rename w into st.
      dependent destruction p.
      dependent destruction Hst_u.
      edestruct (IHHst _ _ _ _ _ _ ccpos_ready)
        as (s' & t' & u' & tu & Hs' & Ht' & Hu' & Htu & Hs_tu); eauto 100.
  Qed.

  Lemma comp_has_assoc_2 {iσ iτ iυ iστ iτυ iστυ pστ pτυ pσ_τυ pστ_υ} :
    @ccpos iσ iτ iυ iστ iτυ iστυ pστ pτυ pσ_τυ pστ_υ ->
    forall s t u tu stu,
      comp_has pτυ t u tu ->
      comp_has pσ_τυ s tu stu ->
      exists s' t' u' st,
        s' [= s /\ t' [= t /\ u' [= u /\
        comp_has pστ s' t' st /\
        comp_has pστ_υ st u' stu.
  Proof.
    intros p s t u tu stu Htu Hs_tu. cbn.
    revert iτ iυ iστ iτυ iστυ pστ pτυ pσ_τυ pστ_υ p t u tu stu Htu Hs_tu.
    induction s as [ | | _ _ [ | | | ] ]; intros.
    - (* ready *)
      destruct_comp_has; eauto 100.
    - (* [σ] suspended *)
      revert iστ iστυ pστ pσ_τυ pστ_υ p stu Hs_tu.
      induction Htu; intros;
      dependent destruction p;
      dependent destruction Hs_tu;
      eauto 100.
      + (* question of [τ] *)
        edestruct (IHHtu _ _ _ _ _ (ccpos_right _ _ _))
          as (s' & t' & u' & st & Hs' & Ht' & Hu' & Hst & Hstu); eauto 100.
      + (* suspended *)
        edestruct (IHHtu _ _ _ _ _ (ccpos_suspended _ _ _ _))
          as (s' & t' & u' & st & Hs' & Ht' & Hu' & Hst & Hstu); eauto 100.
      + (* environment answer *)
        edestruct (IHHtu _ _ _ _ _ (ccpos_right _ _ _))
          as (s' & t' & u' & st & Hs' & Ht' & Hu' & Hst & Hstu); eauto 100.
      + (* answer of [υ] *)
        edestruct (IHHtu _ _ _ _ _ (ccpos_mid _ _))
          as (s' & t' & u' & st & Hs' & Ht' & Hu' & Hst & Hstu); eauto 100.
    - (* environment question *)
      destruct_comp_has; eauto 100.
      edestruct (IHs _ _ _ _ _ _ _ _ _ (ccpos_left _))
        as (s' & t' & u' & st & Hs' & Ht' & Hu' & Hst & Hstu); eauto 100.
    - (* question of [σ] *)
      destruct_comp_has; eauto 100.
      edestruct (IHs _ _ _ _ _ _ _ _ _ (ccpos_mid _ _))
        as (s' & t' & u' & st & Hs' & Ht' & Hu' & Hst & Hstu); eauto 100.
    - (* answer of [τ] -- after a while *)
      revert iστ iστυ pστ pσ_τυ pστ_υ p stu Hs_tu.
      induction Htu; intros.
      + (* ready -- we'll be done before then *)
        destruct_comp_has.
      + (* question of [σ] -- we'll be done before then *)
        destruct_comp_has.
      + (* question of [τ] *)
        dependent destruction p.
        edestruct (IHHtu _ _ _ _ _ (ccpos_right _ _ _))
          as (s' & t' & u' & st & Hs' & Ht' & Hu' & Hst & Hstu); eauto 100.
      + (* question of [υ] *)
        dependent destruction p.
        dependent destruction Hs_tu.
        edestruct (IHHtu _ _ _ _ _ (ccpos_suspended _ _ _ _))
          as (s' & t' & u' & st & Hs' & Ht' & Hu' & Hst & Hstu); eauto 100.
      + (* suspended *)
        dependent destruction p.
        dependent destruction Hs_tu.
        eauto 100.
      + (* environment answer *)
        dependent destruction p.
        dependent destruction Hs_tu.
        edestruct (IHHtu _ _ _ _ _ (ccpos_right _ _ _))
          as (s' & t' & u' & st & Hs' & Ht' & Hu' & Hst & Hstu); eauto 100.
      + (* answer of [υ] *)
        dependent destruction p.
        edestruct (IHHtu _ _ _ _ _ (ccpos_mid _ _))
          as (s' & t' & u' & st & Hs' & Ht' & Hu' & Hst & Hstu); eauto 100.
      + (* answer of [τ] *)
        dependent destruction p.
        dependent destruction Hs_tu.
        edestruct (IHs _ _ _ _ _ _ _ _ _ (ccpos_left _))
          as (s' & t' & u' & st & Hs' & Ht' & Hu' & Hst & Hstu); eauto 100.
    - (* answer of [σ] *)
      destruct_comp_has; eauto 100.
      edestruct (IHs _ _ _ _ _ _ _ _ _ ccpos_ready)
        as (s' & t' & u' & st & Hs' & Ht' & Hu' & Hst & Hstu); eauto 100.
  Qed.

  Lemma compose_assoc_when {iσ iτ iυ iστ iτυ iστυ pστ pτυ pσ_τυ pστ_υ} :
    @ccpos iσ iτ iυ iστ iτυ iστυ pστ pτυ pσ_τυ pστ_υ ->
    forall σ τ υ,
      compose_when pστ_υ (compose_when pστ σ τ) υ =
      compose_when pσ_τυ σ (compose_when pτυ τ υ).
  Proof.
    intros p ? ? ?.
    apply antisymmetry; cbn.
    - intros stu (st & u & (s & t & Hs & Ht & Hst) & Hu & Hstu).
      edestruct @comp_has_assoc_1 as (s'&t'&u'& tu & Hs'& Ht'& Hu'& Htu & Hs_tu);
        eauto 100 using Downset.closed.
    - intros stu (s & tu & Hs & (t & u & Ht & Hu & Htu) & Hstu).
      edestruct @comp_has_assoc_2 as (s'&t'&u'& st & Hs'& Ht'& Hu'& Hst & Hst_u);
        eauto 100 using Downset.closed.
  Qed.

  Lemma compose_assoc (σ : G ->> H) (τ : F ->> G) (υ : E ->> F) :
    (σ ⊙ τ) ⊙ υ = σ ⊙ τ ⊙ υ.
  Proof.
    apply compose_assoc_when.
    constructor.
  Qed.
End COMPOSE_COMPOSE.

(** *** Isomorphisms *)

Class Retraction {E F} (f : E ->> F) (g : F ->> E) :=
  {
    retraction : f ⊙ g = id F;
  }.

Class Isomorphism {E F} (f : E ->> F) (g : F ->> E) :=
  {
    iso_fw :> Retraction f g;
    iso_bw :> Retraction g f;
  }.

Lemma retract {E F G} `{Hfg : Retraction F G} (σ : strat E G ready) :
  f ⊙ g ⊙ σ = σ.
Proof.
  rewrite <- compose_assoc.
  rewrite retraction.
  rewrite compose_id_l.
  reflexivity.
Qed.

(** ** §3.3 Flat Composition *)

(** *** Definition 3.6 (Flat composition of strategies) *)

Section FCOMP_STRAT.
  Context {E1 E2 F1 F2 : esig}.
  Obligation Tactic := cbn.

  Variant fcpos : @position E1 F1 -> @position E2 F2 -> @position (fcomp E1 E2) (fcomp F1 F2) -> Type :=
    | fcpos_ready :
        fcpos ready ready ready
    | fcpos_running_l q1 :
        fcpos (running q1) ready (running (inl q1))
    | fcpos_running_r q2 :
        fcpos ready (running q2) (running (inr q2))
    | fcpos_suspended_l q1 m1 :
        fcpos (suspended q1 m1) ready (suspended (inl q1) (inl m1))
    | fcpos_suspended_r q2 m2 :
        fcpos ready (suspended q2 m2) (suspended (inr q2) (inr m2)).

  Inductive fcomp_has : forall {i1 i2 i}, fcpos i1 i2 i -> play i1 -> play i2 -> play i -> Prop :=
    | fcomp_ready :
        fcomp_has fcpos_ready pnil_ready pnil_ready pnil_ready
    | fcomp_oq_l q1 s1 s2 s :
        fcomp_has (fcpos_running_l q1) s1 s2 s ->
        fcomp_has fcpos_ready (oq q1 :: s1) s2 (oq (inl q1) :: s)
    | fcomp_oq_r q2 s1 s2 s :
        fcomp_has (fcpos_running_r q2) s1 s2 s ->
        fcomp_has fcpos_ready s1 (oq q2 :: s2) (oq (inr q2) :: s)
    | fcomp_pq_l {q1} m1 s1 s2 s :
        fcomp_has (fcpos_suspended_l q1 m1) s1 s2 s ->
        fcomp_has (fcpos_running_l q1) (pq m1 :: s1) s2 (pq (inl m1) :: s)
    | fcomp_pq_r {q2} m2 s1 s2 s :
        fcomp_has (fcpos_suspended_r q2 m2) s1 s2 s ->
        fcomp_has (fcpos_running_r q2) s1 (pq m2 :: s2) (pq (inr m2) :: s)
    | fcomp_suspended_l q1 m1 s2 :
        fcomp_has (fcpos_suspended_l q1 m1) (pnil_suspended q1 m1) s2 (pnil_suspended (inl q1) (inl m1))
    | fcomp_suspended_r q2 m2 s1 :
        fcomp_has (fcpos_suspended_r q2 m2) s1 (pnil_suspended q2 m2) (pnil_suspended (inr q2) (inr m2))
    | fcomp_oa_l {q1 m1} n1 s1 s2 s :
        fcomp_has (fcpos_running_l q1) s1 s2 s ->
        fcomp_has (fcpos_suspended_l q1 m1) (oa n1 :: s1) s2 (oa (m:=inl m1) n1 :: s)
    | fcomp_oa_r {q2 m2} n2 s1 s2 s :
        fcomp_has (fcpos_running_r q2) s1 s2 s ->
        fcomp_has (fcpos_suspended_r q2 m2) s1 (oa n2 :: s2) (oa (m:=inr m2) n2 :: s)
    | fcomp_pa_l {q1} r1 s1 s2 s :
        fcomp_has fcpos_ready s1 s2 s ->
        fcomp_has (fcpos_running_l q1) (pa r1 :: s1) s2 (pa (q:=inl q1) r1 :: s)
    | fcomp_pa_r {q2} r2 s1 s2 s :
        fcomp_has fcpos_ready s1 s2 s ->
        fcomp_has (fcpos_running_r q2) s1 (pa r2 :: s2) (pa (q:=inr q2) r2 :: s).

  Hint Constructors fcomp_has pref : core.

  Lemma fcomp_has_closed {i1 i2 i} p t1 t2 t :
    @fcomp_has i1 i2 i p t1 t2 t ->
    forall s, s [= t ->
    exists s1 s2, s1 [= t1 /\ s2 [= t2 /\ fcomp_has p s1 s2 s.
  Proof.
    intros Ht s Hst. revert i1 i2 p t1 t2 Ht. cbn in *.
    induction Hst; intros.
    - dependent destruction p; eauto.
    - dependent destruction p; eauto.
    - dependent destruction Ht; edestruct IHHst as (? & ? & ? & ? & ?); eauto 10.
  Qed.

  Program Definition fcomp_when {i1 i2 i} p (σ1 : strat E1 F1 i1) (σ2 : strat E2 F2 i2) : strat (fcomp E1 E2) (fcomp F1 F2) i :=
    {| Downset.has s :=
        exists s1 s2, Downset.has σ1 s1 /\ Downset.has σ2 s2 /\ fcomp_has p s1 s2 s |}.
  Next Obligation.
    intros i1 i2 i p σ1 σ2 s t Hst (t1 & t2 & Ht1 & Ht2 & Ht).
    edestruct (fcomp_has_closed p) as (s1 & s2 & Hst1 & Hst2 & Hs); eauto.
    eauto 10 using Downset.closed.
  Qed.
End FCOMP_STRAT.

Notation fcomp_st := (fcomp_when fcpos_ready).
Infix "+" := fcomp_st : strat_scope.

(** *** Theorem 3.7 (Properties of flat composition) *)

Section COMPOSE_FCOMP.
  Context {E1 E2 F1 F2 G1 G2 : esig}.

  Variant fccpos :
    forall {i1 i2 j1 j2 i12 j12 ij1 ij2 ij12},
      (* the left-hand side does ⊙ first then ⊕ *)
      cpos i1 j1 ij1 -> cpos i2 j2 ij2 -> fcpos ij1 ij2 ij12 ->
      (* the right-hand side does ⊕ first then ⊙ *)
      fcpos i1 i2 i12 -> fcpos j1 j2 j12 -> cpos i12 j12 ij12 -> Type
    :=
    | fccpos_ready :
        fccpos cpos_ready cpos_ready fcpos_ready
               fcpos_ready fcpos_ready cpos_ready
    (* running [σ1] *)
    | fccpos_left_l (q1 : G1) :
        fccpos (cpos_left q1) cpos_ready (fcpos_running_l q1)
               (fcpos_running_l q1) fcpos_ready (cpos_left (inl q1))
    (* running [σ2] *)
    | fccpos_left_r (q2 : G2) :
        fccpos cpos_ready (cpos_left q2) (fcpos_running_r q2)
               (fcpos_running_r q2) fcpos_ready (cpos_left (inr q2))
    (* running [τ] *)
    | fccpos_right_l (q1 : G1) (m1 : F1) :
        fccpos (cpos_right q1 m1) cpos_ready (fcpos_running_l q1)
               (fcpos_suspended_l q1 m1) (fcpos_running_l m1) (cpos_right (inl q1) (inl m1))
    | fccpos_right_r (q2 : G2) (m2 : F2) :
        fccpos cpos_ready (cpos_right q2 m2) (fcpos_running_r q2)
               (fcpos_suspended_r q2 m2) (fcpos_running_r m2) (cpos_right (inr q2) (inr m2))
    (* [τ] suspended *)
    | fccpos_suspended_l (q1 : G1) (m1 : F1) (u1 : E1) :
        fccpos (cpos_suspended q1 m1 u1) cpos_ready (fcpos_suspended_l q1 u1)
               (fcpos_suspended_l q1 m1) (fcpos_suspended_l m1 u1) (cpos_suspended (inl q1) (inl m1) (inl u1))
    | fccpos_suspended_r (q2 : G2) (m2 : F2) (u2 : E2) :
        fccpos cpos_ready (cpos_suspended q2 m2 u2) (fcpos_suspended_r q2 u2)
               (fcpos_suspended_r q2 m2) (fcpos_suspended_r m2 u2) (cpos_suspended (inr q2) (inr m2) (inr u2)).

  Hint Constructors comp_has fcomp_has : core.

  Lemma fcomp_compose_has {i1 i2 j1 j2 i12 j12 ij1 ij2 ij12 p1 p2 p12 qi qj qij} :
    @fccpos i1 i2 j1 j2 i12 j12 ij1 ij2 ij12 p1 p2 p12 qi qj qij ->
    forall s1 s2 t1 t2 st,
    (exists st1 st2,
        comp_has p1 s1 t1 st1 /\
        comp_has p2 s2 t2 st2 /\
        fcomp_has p12 st1 st2 st) <->
    (exists s12 t12,
        fcomp_has qi s1 s2 s12 /\
        fcomp_has qj t1 t2 t12 /\
        comp_has qij s12 t12 st).
  Proof.
    intros p s1 s2 t1 t2 st. split.
    - intros (st1 & st2 & Hst1 & Hst2 & Hst).
  Admitted.

  Lemma fcomp_compose_when {i1 i2 j1 j2 i12 j12 ij1 ij2 ij12 p1 p2 p12 qi qj qij} :
    @fccpos i1 i2 j1 j2 i12 j12 ij1 ij2 ij12 p1 p2 p12 qi qj qij ->
    forall σ1 σ2 τ1 τ2,
      fcomp_when p12 (compose_when p1 σ1 τ1) (compose_when p2 σ2 τ2) =
      compose_when qij (fcomp_when qi σ1 σ2) (fcomp_when qj τ1 τ2).
  Proof.
    intros p σ1 σ2 τ1 τ2.
    pose proof (fcomp_compose_has p).
    apply antisymmetry; cbn.
    - intros s (st1 &st2 &(s1 &t1 &Hs1 &Ht1 &Hst1) &(s2 &t2 &Hs2 &Ht2 &Hst2) &Hs).
      edestruct (proj1 (H s1 s2 t1 t2 s)) as (s12 & t12 & Hs12 & Ht12 & H'); eauto 100.
    - intros s (s12 &t12 &(s1 &s2 &Hs1 &Hs2 &Hs12) &(t1 &t2 &Ht1 &Ht2 &Ht12) &Hs).
      edestruct (proj2 (H s1 s2 t1 t2 s)) as (st1 & st2 & Hst1 & Hst2 & H'); eauto 100.
  Qed.

  Lemma fcomp_compose (σ1: F1->>G1) (σ2: F2->>G2) (τ1: E1->>F1) (τ2: E2->>F2) :
    (σ1 ⊙ τ1) + (σ2 ⊙ τ2) = (σ1 + σ2) ⊙ (τ1 + τ2).
  Proof.
    apply fcomp_compose_when.
    constructor.
  Qed.
End COMPOSE_FCOMP.

Section FCOMP_ID.
  Context {E1 E2 : esig}.

  Variant fcipos :
    forall {i1 i2 i}, idpos i1 -> idpos i2 -> fcpos i1 i2 i -> idpos i -> Type :=
    | fcipos_ready :
        fcipos id_ready id_ready fcpos_ready
               id_ready
    | fcipos_suspended_l (q1 : E1) :
        fcipos (id_suspended q1) id_ready (fcpos_suspended_l q1 q1)
               (id_suspended (inl q1))
    | fcipos_suspended_r (q2 : E2) :
        fcipos id_ready (id_suspended q2) (fcpos_suspended_r q2 q2)
               (id_suspended (inr q2)).

  Lemma fcomp_id_when {i1 i2 i p1 p2 p12 q} (p : @fcipos i1 i2 i p1 p2 p12 q) :
    fcomp_when p12 (id_when p1) (id_when p2) = id_when q.
  Admitted.

  Lemma fcomp_id :
    id E1 + id E2 = id (E1 + E2).
  Proof.
    apply fcomp_id_when.
    constructor.
  Qed.
End FCOMP_ID.

(** In addition to the bifunctor ⊕ we define the following structural maps.
  Some of them are discussed informally in the paper's §2.6. *)

(** *** Monoidal structure *)

Section FCOMP_UNIT.
  Context {E : esig}.
  Obligation Tactic := cbn.

  (** **** Left unitor *)

  Variant flpos : @position (fcomp Empty_sig E) E -> Type :=
    | flpos_ready : flpos ready
    | flpos_suspended (q : E) : flpos (suspended q (inr q)).

  Inductive flam_has : forall {i}, flpos i -> play i -> Prop :=
    | flam_ready :
        flam_has flpos_ready pnil_ready
    | flam_question q s :
        flam_has (flpos_suspended q) s ->
        flam_has flpos_ready (oq q :: pq (inr q) :: s)
    | flam_suspended q :
        flam_has (flpos_suspended q) (pnil_suspended q (inr q))
    | flam_answer q r s :
        flam_has flpos_ready s ->
        flam_has (flpos_suspended q) (oa (m:=inr q) r :: pa (q:=q) r :: s).

  Program Definition flam_when {i} (p : flpos i) : strat (fcomp Empty_sig E) E i :=
    {| Downset.has := flam_has p |}.
  Next Obligation.
    intros i p s t Hst Ht. revert s Hst.
    induction Ht; intros;
      dependent destruction Hst;
      try dependent destruction Hst;
      constructor; auto.
  Qed.

  (** **** Left unitor inverse *)

  Variant flrpos : @position E (fcomp Empty_sig E) -> Type :=
    | flrpos_ready : flrpos ready
    | flrpos_suspended (q : E) : flrpos (suspended (inr q) q).

  Inductive flamr_has : forall {i}, flrpos i -> play i -> Prop :=
    | flamr_ready :
        flamr_has flrpos_ready pnil_ready
    | flamr_question q s :
        flamr_has (flrpos_suspended q) s ->
        flamr_has flrpos_ready (oq (inr q) :: pq q :: s)
    | flamr_suspended q :
        flamr_has (flrpos_suspended q) (pnil_suspended (inr q) q)
    | flamr_answer q r s :
        flamr_has flrpos_ready s ->
        flamr_has (flrpos_suspended q) (oa (m:=q) r :: pa (q:=inr q) r :: s).

  Program Definition flamr_when {i} (p : flrpos i) : strat E (fcomp Empty_sig E) i :=
    {| Downset.has := flamr_has p |}.
  Next Obligation.
    intros i p s t Hst Ht. revert s Hst.
    induction Ht; intros;
      dependent destruction Hst;
      try dependent destruction Hst;
      constructor; auto.
  Qed.

  (** **** Left unitor properties *)

  Global Instance flam_iso :
    Isomorphism (flam_when flpos_ready) (flamr_when flrpos_ready).
  Proof.
  Admitted.

  (** **** Right unitor *)

  Variant frpos : @position (fcomp E Empty_sig) E -> Type :=
    | frpos_ready : frpos ready
    | frpos_suspended (q : E) : frpos (suspended q (inl q)).

  Inductive frho_has : forall {i}, frpos i -> play i -> Prop :=
    | frho_ready :
        frho_has frpos_ready pnil_ready
    | frho_question q s :
        frho_has (frpos_suspended q) s ->
        frho_has frpos_ready (oq q :: pq (inl q) :: s)
    | frho_suspended q :
        frho_has (frpos_suspended q) (pnil_suspended q (inl q))
    | frho_answer q r s :
        frho_has frpos_ready s ->
        frho_has (frpos_suspended q) (oa (m:=inl q) r :: pa (q:=q) r :: s).

  Program Definition frho_when {i} (p : frpos i) : strat (fcomp E Empty_sig) E i :=
    {| Downset.has := frho_has p |}.
  Next Obligation.
    intros i p s t Hst Ht. revert s Hst.
    induction Ht; intros;
      dependent destruction Hst;
      try dependent destruction Hst;
      constructor; auto.
  Qed.

  (** **** Right unitor inverse *)

  Variant frrpos : @position E (fcomp E Empty_sig) -> Type :=
    | frrpos_ready : frrpos ready
    | frrpos_suspended (q : E) : frrpos (suspended (inl q) q).

  Inductive frhor_has : forall {i}, frrpos i -> play i -> Prop :=
    | frhor_ready :
        frhor_has frrpos_ready pnil_ready
    | frhor_question q s :
        frhor_has (frrpos_suspended q) s ->
        frhor_has frrpos_ready (oq (inl q) :: pq q :: s)
    | frhor_suspended q :
        frhor_has (frrpos_suspended q) (pnil_suspended (inl q) q)
    | frhor_answer q r s :
        frhor_has frrpos_ready s ->
        frhor_has (frrpos_suspended q) (oa (m:=q) r :: pa (q:=inl q) r :: s).

  Program Definition frhor_when {i} (p : frrpos i) : strat E (fcomp E Empty_sig) i :=
    {| Downset.has := frhor_has p |}.
  Next Obligation.
    intros i p s t Hst Ht. revert s Hst.
    induction Ht; intros;
      dependent destruction Hst;
      try dependent destruction Hst;
      constructor; auto.
  Qed.

  (** **** Right unitor properties *)

  Global Instance frho_iso :
    Isomorphism (frho_when frpos_ready) (frhor_when frrpos_ready).
  Proof.
  Admitted.
End FCOMP_UNIT.

Notation flam := (flam_when flpos_ready).
Notation flamr := (flamr_when flrpos_ready).
Notation frho := (frho_when frpos_ready).
Notation frhor := (frhor_when frrpos_ready).

Notation "λ+" := flam.
Notation "λ'+" := flamr.
Notation "ρ+" := frho.
Notation "ρ'+" := frhor.

Section FCOMP_ASSOC.
  Context {E F G : esig}.
  Obligation Tactic := cbn.

  (** **** Associator *)

  Variant fapos : @position ((E + F) + G) (E + (F + G)) -> Type :=
    | fapos_ready : fapos ready
    | fapos_left q : fapos (suspended (inl q) (inl (inl q)))
    | fapos_mid q : fapos (suspended (inr (inl q)) (inl (inr q)))
    | fapos_right q : fapos (suspended (inr (inr q)) (inr q)).

  Inductive falph_has : forall {i}, fapos i -> play i -> Prop :=
    | falph_ready :
        falph_has fapos_ready pnil_ready
    | falph_question_l q s :
        falph_has (fapos_left q) s ->
        falph_has fapos_ready (oq (inl q) :: pq (inl (inl q)) :: s)
    | falph_question_m q s :
        falph_has (fapos_mid q) s ->
        falph_has fapos_ready (oq (inr (inl q)) :: pq (inl (inr q)) :: s)
    | falph_question_r q s :
        falph_has (fapos_right q) s ->
        falph_has fapos_ready (oq (inr (inr q)) :: pq (inr q) :: s)
    | falph_suspended_l q :
        falph_has (fapos_left q) (pnil_suspended _ _)
    | falph_suspended_m q :
        falph_has (fapos_mid q) (pnil_suspended _ _)
    | falph_suspended_r q :
        falph_has (fapos_right q) (pnil_suspended _ _)
    | falph_answer_l q r s :
        falph_has fapos_ready s ->
        falph_has (fapos_left q) (oa (m := inl (inl q)) r :: pa (q := inl q) r :: s)
    | falph_answer_m q r s :
        falph_has fapos_ready s ->
        falph_has (fapos_mid q) (oa (m := inl (inr q)) r :: pa (q := inr (inl q)) r :: s)
    | falph_answer_r (q : G) (r : ar q) s :
        falph_has fapos_ready s ->
        falph_has (fapos_right q) (oa (m := inr q) r :: pa (q := inr (inr q)) r :: s).

  Program Definition falph_when {i} (p : fapos i) : strat _ _ i :=
    {| Downset.has := falph_has p |}.
  Next Obligation.
    intros i p s t Hst Ht. revert s Hst.
    induction Ht; intros;
      dependent destruction Hst; try solve [constructor; auto];
      dependent destruction Hst; try solve [constructor; auto].
  Qed.

  (** **** Associator inverse *)

  Variant farpos : @position (E + (F + G)) ((E + F) + G) -> Type :=
    | farpos_ready : farpos ready
    | farpos_left q : farpos (suspended (inl (inl q)) (inl q))
    | farpos_mid q : farpos (suspended (inl (inr q)) (inr (inl q)))
    | farpos_right q : farpos (suspended (inr q) (inr (inr q))).

  Inductive falphr_has : forall {i}, farpos i -> play i -> Prop :=
    | falphr_ready :
        falphr_has farpos_ready pnil_ready
    | falphr_question_l q s :
        falphr_has (farpos_left q) s ->
        falphr_has farpos_ready (oq (inl (inl q)) :: pq (inl q) :: s)
    | falphr_question_m q s :
        falphr_has (farpos_mid q) s ->
        falphr_has farpos_ready (oq (inl (inr q)) :: pq (inr (inl q)) :: s)
    | falphr_question_r q s :
        falphr_has (farpos_right q) s ->
        falphr_has farpos_ready (oq (inr q) :: pq (inr (inr q)) :: s)
    | falphr_suspended_l q :
        falphr_has (farpos_left q) (pnil_suspended _ _)
    | falphr_suspended_m q :
        falphr_has (farpos_mid q) (pnil_suspended _ _)
    | falphr_suspended_r q :
        falphr_has (farpos_right q) (pnil_suspended _ _)
    | falphr_answer_l (q : E) (r : ar q) s :
        falphr_has farpos_ready s ->
        falphr_has (farpos_left q) (oa (m := inl q) r :: pa (q := inl (inl q)) r :: s)
    | falphr_answer_m q r s :
        falphr_has farpos_ready s ->
        falphr_has (farpos_mid q) (oa (m := inr (inl q)) r :: pa (q := inl (inr q)) r :: s)
    | falphr_answer_r (q : G) (r : ar q) s :
        falphr_has farpos_ready s ->
        falphr_has (farpos_right q) (oa (m := inr (inr q)) r :: pa (q := inr q) r :: s).

  Program Definition falphr_when {i} (p : farpos i) : strat _ _ i :=
    {| Downset.has := falphr_has p |}.
  Next Obligation.
    intros i p s t Hst Ht. revert s Hst.
    induction Ht; intros;
      dependent destruction Hst; try solve [constructor; auto];
      dependent destruction Hst; try solve [constructor; auto].
  Qed.

  (** **** Associator properties *)

  Global Instance falph_iso :
    Isomorphism (falph_when fapos_ready) (falphr_when farpos_ready).
  Proof.
  Admitted.
End FCOMP_ASSOC.

Notation falph := (falph_when fapos_ready).
Notation falphr := (falphr_when farpos_ready).

Notation "α+" := falph.
Notation "α'+" := falphr.

(** **** Triangle diagram *)

(** **** Pentagon diagram *)

(** *** Symmetric monoidal structure *)

(** **** Braiding *)

Section FCOMP_SYMM.
  Context {E F : esig}.
  Obligation Tactic := cbn.

  Variant fgpos : @position (F + E) (E + F) -> Type :=
    | fgpos_ready : fgpos ready
    | fgpos_left q : fgpos (suspended (inl q) (inr q))
    | fgpos_right q : fgpos (suspended (inr q) (inl q)).

  Inductive fgam_has : forall {i}, fgpos i -> play i -> Prop :=
    | fgam_ready :
        fgam_has fgpos_ready pnil_ready
    | fgam_question_l q s :
        fgam_has (fgpos_left q) s ->
        fgam_has fgpos_ready (oq (inl q) :: pq (inr q) :: s)
    | fgam_question_r q s :
        fgam_has (fgpos_right q) s ->
        fgam_has fgpos_ready (oq (inr q) :: pq (inl q) :: s)
    | fgam_suspended_l q :
        fgam_has (fgpos_left q) (pnil_suspended _ _)
    | fgam_suspended_r q :
        fgam_has (fgpos_right q) (pnil_suspended _ _)
    | fgam_answer_l q r s :
        fgam_has fgpos_ready s ->
        fgam_has (fgpos_left q) (oa (m:=inr q) r :: pa (q:=inl q) r :: s)
    | fgam_answer_r q r s :
        fgam_has fgpos_ready s ->
        fgam_has (fgpos_right q) (oa (m:=inl q) r :: pa (q:=inr q) r :: s).

  Program Definition fgam_when {i} (p : fgpos i) : strat (F + E) (E + F) i :=
    {| Downset.has := fgam_has p |}.
  Next Obligation.
    intros i p s t Hst Ht. revert s Hst.
    induction Ht; intros;
      dependent destruction Hst; try solve [constructor; auto];
      dependent destruction Hst; try solve [constructor; auto].
  Qed.
End FCOMP_SYMM.

Notation fgam := (fgam_when fgpos_ready).
Notation "γ+" := fgam.

(** **** Hexagon identity *)

(** **** Braiding is its own inverse *)

Global Instance fgam_iso {E F} :
  Isomorphism (@fgam_when E F _ fgpos_ready) (@fgam_when F E _ fgpos_ready).
Proof.
Admitted.

(** *** Duplication and projections *)

(** Although [fcomp] is not a cartesian product, it is possible to
  duplicate an interface or drop an unused component of the signature. *)

(** **** Duplication *)

Section FCOMP_DELTA.
  Context {E : esig}.
  Obligation Tactic := cbn.
  Infix "+" := fcomp.

  Variant fdpos : @position E (E + E) -> Type :=
    | fdpos_ready : fdpos ready
    | fdpos_left q : fdpos (suspended (inl q) q)
    | fdpos_right q : fdpos (suspended (inr q) q).

  Inductive fdel_has : forall {i}, fdpos i -> play i -> Prop :=
    | fdel_ready :
        fdel_has fdpos_ready pnil_ready
    | fdel_question_l q s :
        fdel_has (fdpos_left q) s ->
        fdel_has fdpos_ready (oq (inl q) :: pq q :: s)
    | fdel_question_r q s :
        fdel_has (fdpos_right q) s ->
        fdel_has fdpos_ready (oq (inr q) :: pq q :: s)
    | fdel_suspended_l q :
        fdel_has (fdpos_left q) (pnil_suspended _ _)
    | fdel_suspended_r q :
        fdel_has (fdpos_right q) (pnil_suspended _ _)
    | fdel_answer_l q r s :
        fdel_has fdpos_ready s ->
        fdel_has (fdpos_left q) (oa (m:=q) r :: pa (q:=inl q) r :: s)
    | fdel_answer_r q r s :
        fdel_has fdpos_ready s ->
        fdel_has (fdpos_right q) (oa (m:=q) r :: pa (q:=inr q) r :: s).

  Program Definition fdel_when {i} (p : fdpos i) : strat E (E + E) i :=
    {| Downset.has := fdel_has p |}.
  Next Obligation.
    intros i p s t Hst Ht. revert s Hst.
    induction Ht; intros;
      dependent destruction Hst; try solve [constructor; auto];
      dependent destruction Hst; try solve [constructor; auto].
  Qed.
End FCOMP_DELTA.

Notation fdel := (fdel_when fdpos_ready).
Notation "Δ+" := fdel.

(** **** Projections *)

Section FCOMP_PROJ.
  Context {E1 E2 : esig}.

  Variant ffpos : @position (fcomp E1 E2) E1 -> Type :=
    | ffpos_ready : ffpos ready
    | ffpos_suspended (q1 : E1) : ffpos (suspended q1 (inl q1)).

  Inductive ffst_has : forall {i}, ffpos i -> play i -> Prop :=
    | ffst_ready :
        ffst_has ffpos_ready pnil_ready
    | ffst_question q1 s :
        ffst_has (ffpos_suspended q1) s ->
        ffst_has ffpos_ready (oq q1 :: pq (inl q1) :: s)
    | ffst_suspended q1 :
        ffst_has (ffpos_suspended q1) (pnil_suspended q1 (inl q1))
    | ffst_answer q1 r1 s :
        ffst_has ffpos_ready s ->
        ffst_has (ffpos_suspended q1) (oa (m:=inl q1) r1 :: pa (q:=q1) r1 :: s).

  Program Definition ffst_when {i} (p : ffpos i) : strat (fcomp E1 E2) E1 i :=
    {| Downset.has := ffst_has p |}.
  Next Obligation.
    revert x H.
    induction H0; intros;
      dependent destruction H; try constructor; auto;
      dependent destruction H; try constructor; auto.
  Qed.

  Variant fspos : @position (fcomp E1 E2) E2 -> Type :=
    | fspos_ready : fspos ready
    | fspos_suspended (q2 : E2) : fspos (suspended q2 (inr q2)).

  Inductive fsnd_has : forall {i}, fspos i -> play i -> Prop :=
    | fsnd_ready :
        fsnd_has fspos_ready pnil_ready
    | fsnd_question q2 s :
        fsnd_has (fspos_suspended q2) s ->
        fsnd_has fspos_ready (oq q2 :: pq (inr q2) :: s)
    | fsnd_suspended q2 :
        fsnd_has (fspos_suspended q2) (pnil_suspended q2 (inr q2))
    | fsnd_answer q2 r2 s :
        fsnd_has fspos_ready s ->
        fsnd_has (fspos_suspended q2) (oa (m:=inr q2) r2 :: pa (q:=q2) r2 :: s).

  Program Definition fsnd_when {i} (p : fspos i) : strat (fcomp E1 E2) E2 i :=
    {| Downset.has := fsnd_has p |}.
  Next Obligation.
    revert x H.
    induction H0; intros;
      dependent destruction H; try constructor; auto;
      dependent destruction H; try constructor; auto.
  Qed.
End FCOMP_PROJ.

Notation ffst := (ffst_when ffpos_ready).
Notation fsnd := (fsnd_when fspos_ready).
Notation "π₁+" := ffst.
Notation "π₂+" := fsnd.

(** **** Properties *)

Global Instance ffst_fdelta {E : esig} :
  Retraction (F:=E) ffst fdel.
Proof.
Admitted.

Global Instance fsnd_fdelta {E : esig} :
  Retraction (F:=E) fsnd fdel.
Proof.
Admitted.


(** * §4 REFINEMENT CONVENTIONS *)

(** ** §4.2 Refinement Conventions *)

Section RC.
  Context {E1 E2 : esig}.
  Obligation Tactic := cbn.

  (** *** Definition 4.1 (Refinement convention) *)

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
      dependent destruction Hyz; constructor; auto.
  Qed.
  Next Obligation.
    intros w1 w2 Hw12 Hw21.
    induction Hw12; dependent destruction Hw21; firstorder congruence.
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

  Hint Constructors rcp_ref : core.

  Global Instance rcnext_ref :
    Monotonic rcnext (forallr -, forallr -, - ==> - ==> ref ++> ref).
  Proof.
    intros q1 q2 r1 r2 R S HRS.
    cbn. eauto.
  Qed.

  (** The following [auto] hints facilitate the use of downward closure. *)

  Lemma conv_has_cont_allow q1 q2 r1 r2 k R :
    Downset.has R (rcp_cont q1 q2 r1 r2 k) ->
    Downset.has R (rcp_allow q1 q2).
  Proof.
    apply Downset.closed. constructor.
  Qed.

  Lemma conv_has_forbid_allow q1 q2 r1 r2 R :
    Downset.has R (rcp_forbid q1 q2 r1 r2) ->
    Downset.has R (rcp_allow q1 q2).
  Proof.
    apply Downset.closed. constructor.
  Qed.

  Lemma conv_has_forbid_cont q1 q2 r1 r2 k R :
    Downset.has R (rcp_forbid q1 q2 r1 r2) ->
    Downset.has R (rcp_cont q1 q2 r1 r2 k).
  Proof.
    apply Downset.closed. constructor.
  Qed.

  (** [rcnext] not only trivially preserves [sup]s and [inf]s, but the
    fact that it is only sensitive to part of the refinement
    convention allows us to formulate these stronger properties. *)

  Lemma rcnext_inf {I} m1 m2 n1 n2 (R : I -> conv) :
    rcnext m1 m2 n1 n2 (linf R) =
    inf {i | ~ Downset.has (R i) (rcp_forbid m1 m2 n1 n2)}, rcnext m1 m2 n1 n2 (R i).
  Proof.
    apply antisymmetry; cbn; auto.
    intros s Hs i.
    destruct (classic (Downset.has (R i) (rcp_forbid m1 m2 n1 n2))).
    - eauto using conv_has_forbid_cont.
    - apply (Hs (exist _ i H)).
  Qed.

  Lemma rcnext_sup {I} m1 m2 n1 n2 (R : I -> conv) :
    rcnext m1 m2 n1 n2 (lsup R) =
    sup {i | Downset.has (R i) (rcp_allow m1 m2)}, rcnext m1 m2 n1 n2 (R i).
  Proof.
    apply antisymmetry; cbn; auto.
    - intros s [i Hi].
      assert (Hi' : Downset.has (R i) (rcp_allow m1 m2))
        by eauto using conv_has_cont_allow.
      exists (exist _ i Hi'); cbn; eauto.
    - intros s [[i Hi] Hi']; eauto.
  Qed.
End RC.

Arguments rcp : clear implicits.
Arguments rcp_poset : clear implicits.
Arguments conv : clear implicits.
Global Instance rcnext_params : Params (@rcnext) 5 := { }.

Global Hint Immediate
  conv_has_cont_allow
  conv_has_forbid_allow
  conv_has_forbid_cont : core.

Declare Scope conv_scope.
Delimit Scope conv_scope with conv.
Bind Scope conv_scope with conv.
Open Scope conv_scope.

(** ** §4.3 Refinement Squares *)

Section RSQ.
  Context {E1 E2 F1 F2 : esig}.

  (** *** Definition 4.2 (Refinement square) *)

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

  Definition rsq_when R S {i1 i2} p (σ : strat E1 F1 i1) (τ : strat E2 F2 i2) : Prop :=
    forall s, Downset.has σ s -> rsp R S p s τ.

  Definition rsq R S σ τ :=
    rsq_when R S rs_ready σ τ.

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

  Global Instance rsq_when_ref :
    Monotonic rsq_when
      (ref ++> ref --> forallr -, forallr -, - ==> ref --> ref ++> impl).
  Proof.
    intros R R' HR S S' HS i1 i2 p σ1 σ2 Hσ τ1 τ2 Hτ H s2 Hs2.
    rewrite <- HR, <- HS, <- Hτ.
    eapply H; eauto.
  Qed.

  Global Instance rsq_ref :
    Monotonic rsq (ref ++> ref --> ref --> ref ++> impl).
  Proof.
    unfold rsq. rauto.
  Qed.

  (** *** Determinism hints *)

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

  (** *** Operational behavior *)

  Lemma rsq_next_oq {R S σ τ} q1 q2 :
    rsq_when R S rs_ready σ τ ->
    Downset.has S (rcp_allow q1 q2) ->
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
    exists m2,
      Downset.has R (rcp_allow m1 m2) /\
      Downset.has τ (pq m2 :: pnil_suspended q2 m2) /\
      rsq_when R S (rs_suspended q1 q2 m1 m2) (next (pq m1) σ) (next (pq m2) τ).
  Proof.
    intros Hστ H.
    apply Hστ in H.
    dependent destruction H. exists m2. split; auto.
    dependent destruction H0. cbn in H0. split; auto.
    intros s Hs. cbn in Hs.
    apply Hστ in Hs.
    dependent destruction Hs.
    determinism m2 m3.
    subst. auto.
  Qed.

  Lemma rsq_next_oa {R S q1 q2 m1 m2 σ τ} n1 n2 :
    rsq_when R S (rs_suspended q1 q2 m1 m2) σ τ ->
    ~ Downset.has R (rcp_forbid m1 m2 n1 n2) ->
    rsq_when (rcnext m1 m2 n1 n2 R) S (rs_running q1 q2) (next (oa n1) σ) (next (oa n2) τ).
  Proof.
    intros Hστ Hn s Hs.
    specialize (Hστ _ Hs).
    dependent destruction Hστ.
    eauto.
  Qed.

  Lemma rsq_next_pa {R S q1 q2 σ τ} `{!Deterministic τ} r1 :
    rsq_when R S (rs_running q1 q2) σ τ ->
    Downset.has σ (pa r1 :: pnil_ready) ->
    exists r2,
      ~ Downset.has S (rcp_forbid q1 q2 r1 r2) /\
      Downset.has τ (pa r2 :: pnil_ready) /\
      rsq_when R (rcnext q1 q2 r1 r2 S) rs_ready (next (pa r1) σ) (next (pa r2) τ).
  Proof.
    intros Hστ H.
    apply Hστ in H.
    dependent destruction H. exists r2. split; auto.
    dependent destruction H0. cbn in H0. split; auto.
    intros s Hs. cbn in Hs.
    apply Hστ in Hs.
    dependent destruction Hs.
    determinism r2 r3.
    assumption.
  Qed.

  (** *** Preservation of joins and meets *)

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
        determinism m2 m3.
        assumption.
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
          assert (Downset.has (S j) (rcp_allow q1 q2)) as Hjq by eauto.
          pose proof (H j Hjq) as Hj. dependent destruction Hj.
          determinism r2 r3.
          eauto.
        * rewrite rcnext_sup.
          apply IHs'. { typeclasses eauto. }
          split; eauto.
          intros [j Hj].
          specialize (H j Hj).
          dependent destruction H. cbn.
          determinism r2 r0.
          assumption.
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
    (forall i:I, rsq R (S i) σ τ) ->
    rsq R (lsup S) σ τ.
  Proof.
    intros HI H s Hs.
    apply rsp_sup; auto.
    intro i. apply H, Hs.
  Qed.

  Lemma rsp_inf {I} {i1 i2} (p : rspos i1 i2) R S s τ `{Hτ : !Deterministic τ}:
    inhabited I ->
    (forall i:I, rsp (R i) S p s τ) ->
    rsp (linf R) S p s τ.
  Proof.
    revert i2 p I R S τ Hτ.
    induction s as [ | q1 m1 | i1 j1 m s' IHs']; intros i2 p I R S τ Hτ.
    - (* ready *)
      dependent destruction p.
      intros [i] H. specialize (H i).
      dependent destruction H.
      constructor; auto.
    - (* suspended *)
      dependent destruction p.
      intros [i] H. specialize (H i).
      dependent destruction H.
      constructor; auto.
    - (* move *)
      dependent destruction m.
      + (* incoming question *)
        rename q into q1.
        dependent destruction p.
        intros [i] H. pose proof (H i) as Hi.
        dependent destruction Hi.
        constructor; auto.
        intros q2 Hq.
        eapply IHs'. { typeclasses eauto. }
        split; auto. clear i H1.
        intros i. specialize (H i).
        dependent destruction H; auto.
      + (* outgoing question *)
        rename q into q1, m into m1.
        dependent destruction p.
        intros [i] H. pose proof (H i) as Hi.
        dependent destruction Hi.
        econstructor.
        * intros j. specialize (H j).
          dependent destruction H.
          determinism m2 m0.
          eassumption.
        * eapply IHs'. { typeclasses eauto. }
          split; eauto.
          intros j. specialize (H j).
          dependent destruction H.
          determinism m2 m0.
          eassumption.
      + (* environment answer *)
        rename q into q1, m into m1, n into n1.
        dependent destruction p.
        intros [i] H. constructor.
        * specialize (H i).
          dependent destruction H.
          assumption.
        * intros n2 Hn.
          rewrite rcnext_inf.
          eapply IHs'.
          -- typeclasses eauto.
          -- cbn in Hn. apply not_all_ex_not in Hn as [j Hj]. eauto.
          -- intros [j Hnj]. cbn. specialize (H j).
             dependent destruction H; eauto.
      + (* component answer *)
        rename q into q1, r into r1.
        dependent destruction p.
        intros [i] H.
        pose proof (H i) as Hi. dependent destruction Hi.
        econstructor; eauto.
        eapply IHs'. { typeclasses eauto. }
        split; auto.
        intros j.
        pose proof (H j) as Hj. dependent destruction Hj.
        determinism r2 r3.
        eassumption.
  Qed.
End RSQ.

Global Hint Resolve rsp_ready_inv_nil rsp_suspended_inv_nil : determinism.
Global Hint Unfold rsq.

Global Instance rsp_params : Params (@rsp) 7 := { }.
Global Instance rsq_when_params : Params (@rsq_when) 7 := { }.
Global Instance rsq_params : Params (@rsq) 4 := { }.

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

  Hint Constructors comp_has pref rscpos : core.

  Lemma rsp_comp {i1 j1 k1 i2 j2 k2 p1 p2 pi pj pk} :
    @rscpos i1 j1 k1 i2 j2 k2 p1 p2 pi pj pk ->
    forall (s : @play F1 G1 i1) (t : @play E1 F1 j1)
      (σ : strat F2 G2 i2) (τ : strat E2 F2 j2) (w : @play E1 G1 k1),
      comp_has p1 s t w ->
      rsp S T pi s σ ->
      rsp R S pj t τ ->
      rsp R T pk w (compose_when p2 σ τ).
  Proof.
    intros p s t σ τ w Hw Hs Ht.
    revert R S T i2 j2 k2 p2 pi pj pk p σ τ Hs Ht.
    induction Hw; intros.
    - (* ready *)
      dependent destruction p. dependent destruction Hs. constructor; cbn.
      exists pnil_ready, pnil_ready. repeat apply conj; eauto.
      dependent destruction Ht; eauto.
    - (* incoming question *)
      dependent destruction p. dependent destruction Hs. constructor; cbn.
      + exists pnil_ready, pnil_ready. repeat apply conj; eauto.
        dependent destruction Ht; eauto.
      + intros q2 Hq. rewrite <- (compose_next_oq q2). eauto.
    - (* internal question *)
      dependent destruction p. dependent destruction Hs. dependent destruction Ht.
      rewrite <- (compose_next_lq m2). eauto.
    - (* outgoing question *)
      dependent destruction p. dependent destruction Ht. econstructor; eauto.
      rewrite <- compose_next_rq. eauto.
    - (* suspended *)
      dependent destruction p. dependent destruction Ht. constructor. cbn.
      exists (pnil_suspended q2 m2), (pnil_suspended m2 u2).
      repeat apply conj; eauto.
      dependent destruction Hs; eauto.
    - (* environment answer *)
      dependent destruction p. dependent destruction Ht. constructor.
      + exists (pnil_suspended q2 m2), (pnil_suspended m2 u2).
        repeat apply conj; eauto. dependent destruction Hs; eauto.
      + intros n2 Hn. rewrite <- compose_next_oa. eauto.
    - (* answer of τ *)
      dependent destruction p. dependent destruction Hs. dependent destruction Ht.
      rewrite <- (compose_next_ra r2). eauto.
    - (* answer of σ *)
      dependent destruction p. dependent destruction Hs. econstructor; eauto.
      rewrite <- (compose_next_la r2). eauto.
  Qed.

  Lemma rsq_comp_when {i1 j1 k1 i2 j2 k2 p1 p2 pi pj pk} :
    @rscpos i1 j1 k1 i2 j2 k2 p1 p2 pi pj pk ->
    forall (σ1 : strat F1 G1 i1) (τ1 : strat E1 F1 j1)
           (σ2 : strat F2 G2 i2) (τ2 : strat E2 F2 j2),
      rsq_when S T pi σ1 σ2 ->
      rsq_when R S pj τ1 τ2 ->
      rsq_when R T pk (compose_when p1 σ1 τ1) (compose_when p2 σ2 τ2).
  Proof.
    intros p σ1 τ1 σ2 τ2 Hσ Hτ w1 (s1 & t1 & Hs1 & Ht1 & Hst1).
    eauto using rsp_comp.
  Qed.

  Lemma rsq_comp σ1 τ1 σ2 τ2 `{Hσ2: !Deterministic σ2} `{Hτ2: !Deterministic τ2}:
    rsq S T σ1 σ2 ->
    rsq R S τ1 τ2 ->
    rsq R T (σ1 ⊙ τ1) (σ2 ⊙ τ2).
  Proof. apply rsq_comp_when; auto. Qed.
End RSQ_COMP.

(** *** Definition 4.4 (Identity refinement convention) *)

Section VID.
  Context {E : esig}.

  Fixpoint vid_has (s : rcp E E) : Prop :=
    match s with
      | rcp_allow m1 m2 => m1 = m2
      | rcp_forbid m1 m2 n1 n2 => m1 = m2 /\ ~ JMeq n1 n2
      | rcp_cont m1 m2 n1 n2 k => m1 = m2 /\ (JMeq n1 n2 -> vid_has k)
    end.

  Program Definition vid : conv E E :=
    {| Downset.has := vid_has |}.
  Next Obligation.
    induction H; cbn in *; tauto.
  Qed.

  (** Properties *)

  Lemma rcnext_vid m n :
    rcnext m m n n vid = vid.
  Proof.
    apply Downset.has_eq_ext. cbn. firstorder.
  Qed.
End VID.

(** *** Theorem 4.5 (Refinement ordering as refinement squares) *)

Section ID_RSQ.
  Context {E F : esig}.

  (*
    rsq vid vid p σ τ <-> σ [= τ
    rsq R S p id id <-> S [= R
  *)
End ID_RSQ.

(** ** §4.4 Vertical Composition *)

(** *** Definition 4.6 (Vertical composition of refinement conventions) *)

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

  (** The following formulation and properties of [vcomp] are useful
    for the vertical composition proof of refinement squares below. *)

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
        repeat (split; eauto).
        inversion 1; clear H; subst.
        eauto.
      + intros (m2' & Hm12' & Hm23' & Hn13').
        repeat (split; eauto).
        inversion 1; clear H; subst.
        eauto 10.
      + intros (m2' & Hm12' & Hm23' & Hn13').
        repeat (split; eauto).
        inversion 1; clear H; subst.
        eauto 10.
  Qed.
End VCOMP.

Notation "R  ;; S" := (vcomp R S) (at level 45, right associativity) : conv_scope.

(** *** Theorem 4.7 (Vertical composition of refinement squares) *)

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
      rsq_when R' S' p23 σ2 σ3 ->
      match p with
        | rsv_ready =>
          rsp (vcomp R R') (vcomp S S') p13 s1 σ3
        | rsv_running q1 q2 q3 =>
          rsp (vcomp R R') (inf r2, vcomp_at q2 r2 S S') p13 s1 σ3
        | rsv_suspended q1 q2 q3 m1 m2 m3 =>
          Downset.has R (rcp_allow m1 m2) ->
          Downset.has R' (rcp_allow m2 m3) ->
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
      pose proof (Hσ23 _ H) as Hnil.
      dependent destruction Hnil.
      intros Hm12 Hm23.
      apply (rsp_inf (rs_suspended q1 q3 m1 m3)). { typeclasses eauto. }
      split. { eauto using None. }
      intros xn2.
      constructor; auto.
      intros n3 Hn13. cbn in Hn13.
      apply not_and_or in Hn13 as [ | Hn13]; try tauto.
      apply not_and_or in Hn13 as [ | Hn13]; try tauto.
      apply not_all_ex_not in Hn13 as [n2 Hn13].
      apply imply_to_and in Hn13 as [Hxn2 Hn13]. subst xn2.
      apply not_or_and in Hn13 as [Hn12 Hn23].
      rewrite rcnext_vcomp_at by auto.
      eapply (H1 n2 Hn12 _ _ _ _ (rsv_running q1 q2 q3)); eauto with typeclass_instances.
      apply rsq_next_oa; auto.
    - (* component answer *)
      rename q4 into q3, H into Hr12.
      rewrite (inf_lb (Some r2)).
      destruct (rsq_next_pa r2 Hσ23) as (r3 & Hr23 & Hr3 & H23). {
        dependent destruction H12; auto.
      }
      econstructor. { cbn. intros (Hq12 & Hq23 & [Hr | Hr]); eauto. }
      rewrite rcnext_vcomp_at by auto.
      eapply (IHrsp _ _ _ _ rsv_ready); eauto with typeclass_instances.
  Qed.

  Lemma rsq_vcomp_when {p1 p2 p3 p12 p23 p13} (p : @rsvpos p1 p2 p3 p12 p23 p13) :
    forall (R : conv E1 E2) (R' : conv E2 E3) (S : conv F1 F2) (S' : conv F2 F3)
           (σ1 : strat E1 F1 p1) (σ2 : strat E2 F2 p2) (σ3 : strat E3 F3 p3)
           `{Hσ2 : !Deterministic σ2} `{Hσ3 : !Deterministic σ3},
      rsq_when R S p12 σ1 σ2 ->
      rsq_when R' S' p23 σ2 σ3 ->
      match p with
        | rsv_ready =>
          rsq_when (vcomp R R') (vcomp S S') p13 σ1 σ3
        | rsv_running q1 q2 q3 =>
          rsq_when (vcomp R R') (inf r2, vcomp_at q2 r2 S S') p13 σ1 σ3
        | rsv_suspended q1 q2 q3 m1 m2 m3 =>
          Downset.has R (rcp_allow m1 m2) ->
          Downset.has R' (rcp_allow m2 m3) ->
          rsq_when (inf n2, vcomp_at m2 n2 R R') (inf r2, vcomp_at q2 r2 S S') p13 σ1 σ3
      end.
  Proof.
    intros.
    pose proof (rsp_vcomp p).
    destruct p; cbn in *; intros; intro; eauto.
  Qed.

  Lemma rsq_vcomp R R' S S' (σ1 : E1 ->> F1) (σ2 : E2 ->> F2) (σ3 : E3 ->> F3)
        `{Hσ2 : !Deterministic σ2} `{Hσ3 : !Deterministic σ3} :
    rsq R S σ1 σ2 ->
    rsq R' S' σ2 σ3 ->
    rsq (R ;; R') (S ;; S') σ1 σ3.
  Proof.
    apply (rsq_vcomp_when rsv_ready); auto.
  Qed.
End RSVCOMP.

(** *** Other properties of vertical composition *)

Section VCOMP_VID.
  Context {E F : esig}.

  Lemma vcomp_vid_l (R : conv E F) :
    vcomp vid R = R.
  Proof.
    apply Downset.has_eq_ext. intro s.
    revert R.
    induction s; cbn; intros.
    - firstorder congruence.
    - split.
      + intros (? & <- & Hm & Hn). firstorder.
      + intros H. exists m1.
        repeat (split; eauto using conv_has_forbid_allow).
        intros n1'. destruct (classic (n1 ~= n1')) as [Hn1'|Hn1']; eauto.
        apply JMeq_eq in Hn1'. subst. auto.
    - split.
      + intros (? & <- & Hm & Hn).
        specialize (Hn n1) as [[_ Hn] | Hn]; try tauto.
        destruct Hn as [Hn | Hn]; eauto.
        rewrite rcnext_vid in Hn.
        apply IHs in Hn.
        assumption.
      + intros Hn. exists m1.
        repeat (split; eauto).
        intros n1'. destruct (classic (n1 ~= n1')) as [Hn1'|Hn1']; eauto.
        apply JMeq_eq in Hn1'. subst n1'. right. right.
        rewrite rcnext_vid.
        apply IHs; auto.
  Qed.

  Lemma vcomp_vid_r (R : conv E F) :
    vcomp R vid = R.
  Proof.
    apply Downset.has_eq_ext. intro s.
    revert R.
    induction s; cbn; intros.
    - firstorder congruence.
    - split.
      + intros (? & Hm & -> & Hn). firstorder.
      + intros Hn. exists m2.
        repeat (split; eauto using conv_has_forbid_allow).
        intros n2'. destruct (classic (n2 ~= n2')) as [Hn2'|Hn2']; eauto.
        apply JMeq_eq in Hn2'. subst. auto.
    - split.
      + intros (? & Hm & <- & Hn).
        specialize (Hn n2) as [Hn | [[_ Hn] | Hn]]; try tauto; eauto.
        rewrite rcnext_vid in Hn.
        apply IHs in Hn.
        assumption.
      + intros Hn. exists m2.
        repeat (split; eauto).
        intros n2'. destruct (classic (n2 ~= n2')) as [Hn2'|Hn2']; eauto 10.
        apply JMeq_eq in Hn2'. subst n2'. right. right.
        rewrite rcnext_vid.
        apply IHs; auto.
  Qed.
End VCOMP_VID.

(** ** §4.5 Flat Composition *)

(** *** Definition 4.8 (Flat composition of refinement conventions) *)

(** *** Theorem 4.9 (Flat composition properties) *)

(** * Spatial composition *)

(** ** Tensor product of effect signatures *)

Canonical Structure tens E1 E2 :=
  {|
    op := op E1 * op E2;
    ar m := ar (fst m) * ar (snd m);
  |}%type.

(** ** Tensor product of strategies *)

(** We can define a form of tensor product for strategies, however
  note that it is not well-behaved in general. In partcular, if
  [running] strategies conflict on whether an outgoing question or
  top-level answer should come next, the result will be undefined.
  One consequence of that the composite [(σ1 ⊙ τ1) ⊗ (σ2 ⊙ τ2)]
  may synchronize even as the components [(σ1 ⊗ σ2) ⊙ (τ1 ⊗ τ2)]
  do not, weakening functoriality. *)

Section TSTRAT.
  Context {E1 E2 F1 F2 : esig}.

  Variant tpos : @position E1 F1 -> @position E2 F2 -> @position (tens E1 E2) (tens F1 F2) -> Type :=
    | tp_ready :
        tpos ready ready ready
    | tp_running q1 q2 :
        tpos (running q1) (running q2) (running (q1,q2))
    | tp_suspended q1 q2 m1 m2 :
        tpos (suspended q1 m1) (suspended q2 m2) (suspended (q1,q2) (m1,m2)).

  Inductive tstrat_has : forall {i1 i2 i}, tpos i1 i2 i -> play i1 -> play i2 -> play i -> Prop :=
    | tstrat_has_ready :
        tstrat_has (tp_ready)
                 pnil_ready
                 pnil_ready
                 pnil_ready
    | tstrat_has_oq q1 q2 s1 s2 s :
        tstrat_has (tp_running q1 q2) s1 s2 s ->
        tstrat_has (tp_ready)
                 (oq q1 :: s1)
                 (oq q2 :: s2)
                 (oq (q1,q2) :: s)
    | tstrat_has_pq q1 q2 m1 m2 s1 s2 s :
        tstrat_has (tp_suspended q1 q2 m1 m2) s1 s2 s ->
        tstrat_has (tp_running q1 q2)
                 (pq m1 :: s1)
                 (pq m2 :: s2)
                 (pq (m1,m2) :: s)
    | tstrat_has_suspended q1 q2 m1 m2 :
        tstrat_has (tp_suspended q1 q2 m1 m2)
                 (pnil_suspended q1 m1)
                 (pnil_suspended q2 m2)
                 (pnil_suspended (q1,q2) (m1,m2))
    | tstrat_has_oa q1 q2 m1 m2 n1 n2 s1 s2 s :
        tstrat_has (tp_running q1 q2) s1 s2 s ->
        tstrat_has (tp_suspended q1 q2 m1 m2)
                 (oa n1 :: s1)
                 (oa n2 :: s2)
                 (oa (m:=(m1,m2)) (n1,n2) :: s)
    | tstrat_has_pa q1 q2 r1 r2 s1 s2 s :
        tstrat_has (tp_ready) s1 s2 s ->
        tstrat_has (tp_running q1 q2)
                 (pa r1 :: s1)
                 (pa r2 :: s2)
                 (pa (q:=(q1,q2)) (r1,r2) :: s).

  Obligation Tactic := cbn.
  Hint Constructors pref tstrat_has : core.

  Program Definition tstrat {i1 i2 i} (p : tpos i1 i2 i)
    (σ1 : strat E1 F1 i1) (σ2 : strat E2 F2 i2) : strat (tens E1 E2) (tens F1 F2) i :=
      {| Downset.has s := exists s1 s2, tstrat_has p s1 s2 s /\
                                        Downset.has σ1 s1 /\
                                        Downset.has σ2 s2 |}.
  Next Obligation.
    intros i1 i2 i p σ1 σ2 t s Hts (s1 & s2 & Hs & Hs1 & Hs2).
    cut (exists t1 t2, tstrat_has p t1 t2 t /\ pref t1 s1 /\ pref t2 s2).
    { intros (t1 & t2 & Ht & Hts1 & Hts2).
      eauto 10 using Downset.closed. }
    clear - Hts Hs. revert t Hts.
    induction Hs; intros t Hts; dependent destruction Hts; eauto 10;
      edestruct IHHs as (t1 & t2 & Ht & H1 & H2); eauto 10.
  Qed.

  (** *** Residuals *)

  Lemma tstrat_next_oq q1 q2 σ1 σ2 :
    next (oq (q1,q2)) (tstrat tp_ready σ1 σ2) =
    tstrat (tp_running q1 q2) (next (oq q1) σ1) (next (oq q2) σ2).
  Proof.
    apply antisymmetry; cbn.
    - intros s (s1 & s2 & Hs & Hs1 & Hs2). dependent destruction Hs. eauto.
    - intros s (s1 & s2 & Hs & Hs1 & Hs2). eauto 10.
  Qed.

  Lemma tstrat_next_pq {q1 q2} m1 m2 σ1 σ2 :
    next (pq (m1,m2)) (tstrat (tp_running q1 q2) σ1 σ2) =
    tstrat (tp_suspended q1 q2 m1 m2) (next (pq m1) σ1) (next (pq m2) σ2).
  Proof.
    apply antisymmetry; cbn.
    - intros s (s1 & s2 & Hs & Hs1 & Hs2). dependent destruction Hs. eauto.
    - intros s (s1 & s2 & Hs & Hs1 & Hs2). eauto 10.
  Qed.

  Lemma tstrat_next_oa {q1 q2 m1 m2} n1 n2 σ1 σ2 :
    next (oa (m := (m1,m2)) (n1,n2)) (tstrat (tp_suspended q1 q2 m1 m2) σ1 σ2) =
    tstrat (tp_running q1 q2) (next (oa n1) σ1) (next (oa n2) σ2).
  Proof.
    apply antisymmetry; cbn in *.
    - intros s (s1 & s2 & Hs & Hs1 & Hs2).
      remember (oa (m:=(m1,m2)) (n1,n2) :: s) as s' in Hs.
      inversion Hs; subst.
      + dependent destruction H4.
        dependent destruction H5.
        dependent destruction H6.
      + dependent destruction H0.
        dependent destruction H4.
        apply inj_pair2 in H5.
        pose proof (pcons_eq_inv_r _ _ _ _ H5). subst s4.
        pose proof (pcons_eq_inv_l _ _ _ _ H5). clear H5.
        apply oa_eq_inv in H. dependent destruction H.
        eauto.
    - intros s (s1 & s2 & Hs & Hs1 & Hs2).
      eauto 10.
  Qed.

  Lemma tstrat_next_pa q1 q2 r1 r2 σ1 σ2 :
    next (pa (q := (q1,q2)) (r1,r2)) (tstrat (tp_running q1 q2) σ1 σ2) =
    tstrat tp_ready (next (pa r1) σ1) (next (pa r2) σ2).
  Proof.
    apply antisymmetry; cbn.
    - intros s (s1 & s2 & Hs & Hs1 & Hs2). cbn in *.
      remember (pa (q:=(q1,q2)) (r1,r2) :: s) as s' in Hs.
      inversion Hs; subst.
      + dependent destruction H1.
        dependent destruction H2.
        dependent destruction H3.
      + dependent destruction H1.
        dependent destruction H2.
        apply inj_pair2 in H3.
        pose proof (pcons_eq_inv_r _ _ _ _ H3). subst s4.
        pose proof (pcons_eq_inv_l _ _ _ _ H3). clear H3.
        apply pa_eq_inv in H. dependent destruction H.
        eauto.
    - intros s (s1 & s2 & Hs & Hs1 & Hs2).
      eauto 10.
  Qed.
End TSTRAT.

(** ** Tensor product of refinement conventions *)

Section TCONV.
  Context {E1 E2 F1 F2 : esig}.

  Fixpoint tconv_has (R1 : conv E1 F1) (R2 : conv E2 F2) (s : rcp (tens E1 E2) (tens F1 F2)) :=
    match s with
      | rcp_allow (e1,e2) (f1,f2) =>
        Downset.has R1 (rcp_allow e1 f1) /\
        Downset.has R2 (rcp_allow e2 f2)
      | rcp_forbid (e1,e2) (f1,f2) (n1,n2) (r1,r2) =>
        Downset.has R1 (rcp_allow e1 f1) /\
        Downset.has R2 (rcp_allow e2 f2) /\
        (Downset.has R1 (rcp_forbid e1 f1 n1 r1) \/
         Downset.has R2 (rcp_forbid e2 f2 n2 r2))
      | rcp_cont (e1,e2) (f1,f2) (n1,n2) (r1,r2) k =>
        Downset.has R1 (rcp_allow e1 f1) /\
        Downset.has R2 (rcp_allow e2 f2) /\
        (Downset.has R1 (rcp_forbid e1 f1 n1 r1) \/
         Downset.has R2 (rcp_forbid e2 f2 n2 r2) \/
         tconv_has (rcnext e1 f1 n1 r1 R1) (rcnext e2 f2 n2 r2 R2) k)
    end.

  Obligation Tactic := cbn.

  Program Definition tconv R1 R2 : conv (tens E1 E2) (tens F1 F2) :=
    {| Downset.has := tconv_has R1 R2 |}.
  Next Obligation.
    intros R1 R2 s t Hst. revert R1 R2.
    induction Hst as [[e1 e2] [f1 f2] |
                      [e1 e2] [f1 f2] [n1 n2] [r1 r2] k |
                      [e1 e2] [f1 f2] [n1 n2] [r1 r2] |
                      [e1 e2] [f1 f2] [n1 n2] [r1 r2] k k' Hkk' |
                      [e1 e2] [f1 f2] [n1 n2] [r1 r2] k |
                      [e1 e2] [f1 f2] [n1 n2] [r1 r2]]; cbn; firstorder.
  Qed.

  (** *** Residuals *)

  Lemma rcnext_tconv m1 m2 m1' m2' n1 n2 n1' n2' R1 R2 :
    ~ Downset.has R1 (rcp_forbid m1 m1' n1 n1') ->
    ~ Downset.has R2 (rcp_forbid m2 m2' n2 n2') ->
    rcnext (m1,m2) (m1',m2') (n1,n2) (n1',n2') (tconv R1 R2) =
    tconv (rcnext m1 m1' n1 n1' R1) (rcnext m2 m2' n2 n2' R2).
  Proof.
    intros Hn1' Hn2'.
    apply antisymmetry.
    - intros s. cbn. tauto.
    - intros s Hs. cbn.
      cut (Downset.has R1 (rcp_allow m1 m1') /\ Downset.has R2 (rcp_allow m2 m2')); try tauto.
      destruct s as [[q1 q2] [q1' q2'] |
                     [q1 q2] [q1' q2'] [r1 r2] [r1' r2'] |
                     [q1 q2] [q1' q2'] [r1 r2] [r1' r2'] k];
        cbn in Hs; repeat (destruct Hs as [? Hs]); eauto.
  Qed.

  (** *** Preservation of [sup] and [inf]. *)

  Lemma tconv_sup_l {I} R1 R2 :
    tconv (sup i:I, R1 i) R2 = sup i:I, tconv (R1 i) R2.
  Proof.
    apply antisymmetry.
    - intros s. revert I R1 R2.
      induction s as [[m1 m2] [m1' m2'] |
                      [m1 m2] [m1' m2'] [n1 n2] [n1' n2'] |
                      [m1 m2] [m1' m2'] [n1 n2] [n1' n2'] k IHk].
      + cbn in *. firstorder.
      + cbn in *.
        intros I R1 R2 ([i Hm1] & Hm2 & [[j Hn1] | Hn2]); eauto 10.
      + cbn -[lsup] in *.
        intros I R1 R2 ([i Hm1] & Hm2 & [[j Hn1] | [Hn2 | Hk]]); cbn; eauto 10.
        rewrite rcnext_sup in Hk.
        eapply IHk in Hk.
        destruct Hk as [[j Hj] Hk].
        eauto 10.
    - intros s. revert I R1 R2.
      induction s as [[m1 m2] [m1' m2'] |
                      [m1 m2] [m1' m2'] [n1 n2] [n1' n2'] |
                      [m1 m2] [m1' m2'] [n1 n2] [n1' n2'] k IHk].
      + cbn in *. firstorder.
      + cbn in *. firstorder.
      + intros I R1 R2 [i Hk]. cbn in Hk. cbn -[lsup].
        destruct Hk as (Hm1 & Hm2 & Hn).
        firstorder. right. right.
        rewrite rcnext_sup.
        eapply IHk. cbn.
        exists (exist _ i Hm1). eauto.
  Qed.

  Lemma tconv_sup_r {I} R1 R2 :
    tconv R1 (sup i:I, R2 i) = sup i:I, tconv R1 (R2 i).
  Proof.
    apply antisymmetry.
    - intros s. revert I R1 R2.
      induction s as [[m1 m2] [m1' m2'] |
                      [m1 m2] [m1' m2'] [n1 n2] [n1' n2'] |
                      [m1 m2] [m1' m2'] [n1 n2] [n1' n2'] k IHk].
      + cbn in *. firstorder.
      + cbn in *.
        intros I R1 R2 (Hm1 & [i Hm2] & [Hn1 | [j Hn2]]); eauto 10.
      + cbn -[lsup] in *.
        intros I R1 R2 (Hm1 & [i Hm2] & [Hn1 | [[j Hn2] | Hk]]); cbn; eauto 10.
        rewrite rcnext_sup in Hk.
        eapply IHk in Hk.
        destruct Hk as [[j Hj] Hk].
        eauto 10.
    - intros s. revert I R1 R2.
      induction s as [[m1 m2] [m1' m2'] |
                      [m1 m2] [m1' m2'] [n1 n2] [n1' n2'] |
                      [m1 m2] [m1' m2'] [n1 n2] [n1' n2'] k IHk].
      + cbn in *. firstorder.
      + cbn in *. firstorder.
      + intros I R1 R2 [i Hk]. cbn in Hk. cbn -[lsup].
        destruct Hk as (Hm1 & Hm2 & Hn).
        firstorder. right. right.
        rewrite rcnext_sup.
        eapply IHk. cbn.
        exists (exist _ i Hm2). eauto.
  Qed.

  Lemma tconv_sup {I J} R1 R2 :
    tconv (sup i:I, R1 i) (sup j:J, R2 j) = sup i j, tconv (R1 i) (R2 j).
  Proof.
    rewrite tconv_sup_l. f_equal.
    apply FunctionalExtensionality.functional_extensionality. intro i.
    apply tconv_sup_r.
  Qed.

  Lemma tconv_inf_l {I} R1 R2 :
    inhabited I ->
    tconv (inf i:I, R1 i) R2 = inf i:I, tconv (R1 i) R2.
  Proof.
    intros HI.
    apply antisymmetry.
    - intros s. clear HI. revert I R1 R2.
      induction s as [[m1 m2] [m1' m2'] |
                      [m1 m2] [m1' m2'] [n1 n2] [n1' n2'] |
                      [m1 m2] [m1' m2'] [n1 n2] [n1' n2'] k IHk].
      + cbn. firstorder.
      + cbn. firstorder.
      + cbn -[linf].
        intros I R1 R2 (Hm1 & Hm2 & Hn) i. cbn.
        split; auto.
        split; auto.
        destruct Hn as [Hn | Hn]; auto.
        destruct Hn as [Hn | Hn]; auto.
        rewrite rcnext_inf in Hn.
        apply IHk in Hn.
        destruct (classic (Downset.has (R1 i) (rcp_forbid m1 m1' n1 n1'))) as [? | Hi]; auto.
        specialize (Hn (exist _ i Hi)). cbn in Hn. auto.
    - intros s. revert I HI R1 R2.
      induction s as [[m1 m2] [m1' m2'] |
                      [m1 m2] [m1' m2'] [n1 n2] [n1' n2'] |
                      [m1 m2] [m1' m2'] [n1 n2] [n1' n2'] k IHk].
      + cbn. firstorder.
      + cbn. firstorder.
        destruct (classic (Downset.has R2 (rcp_forbid m2 m2' n2 n2'))) as [?|H2]; auto.
        left. intros i. specialize (H i) as (? & ? & [? | ?]); tauto.
      + intros I HI R1 R2 H. cbn in H. cbn -[linf].
        split. { firstorder. }
        split. { firstorder. }
        destruct (classic (Downset.has (inf i:I, R1 i) (rcp_forbid m1 m1' n1 n1'))); auto. right.
        destruct (classic (Downset.has R2 (rcp_forbid m2 m2' n2 n2'))); auto. right.
        rewrite rcnext_inf.
        eapply IHk.
        * apply not_all_ex_not in H0 as [i Hi]. eauto.
        * intros [i Hi]. cbn. firstorder.
  Qed.

  Lemma tconv_inf_r {I} R1 R2 :
    inhabited I ->
    tconv R1 (inf i:I, R2 i) = inf i:I, tconv R1 (R2 i).
  Proof.
    intros HI.
    apply antisymmetry.
    - intros s. clear HI. revert I R1 R2.
      induction s as [[m1 m2] [m1' m2'] |
                      [m1 m2] [m1' m2'] [n1 n2] [n1' n2'] |
                      [m1 m2] [m1' m2'] [n1 n2] [n1' n2'] k IHk].
      + cbn. firstorder.
      + cbn. firstorder.
      + cbn -[linf].
        intros I R1 R2 (Hm1 & Hm2 & Hn) i. cbn.
        split; auto.
        split; auto.
        destruct Hn as [Hn | Hn]; auto.
        destruct Hn as [Hn | Hn]; auto.
        rewrite rcnext_inf in Hn.
        apply IHk in Hn.
        destruct (classic (Downset.has (R2 i) (rcp_forbid m2 m2' n2 n2'))) as [? | Hi]; auto.
        specialize (Hn (exist _ i Hi)). cbn in Hn. auto.
    - intros s. revert I HI R1 R2.
      induction s as [[m1 m2] [m1' m2'] |
                      [m1 m2] [m1' m2'] [n1 n2] [n1' n2'] |
                      [m1 m2] [m1' m2'] [n1 n2] [n1' n2'] k IHk].
      + cbn. firstorder.
      + cbn. firstorder.
        destruct (classic (Downset.has R1 (rcp_forbid m1 m1' n1 n1'))) as [?|H1]; auto.
        right. intros i. specialize (H i) as (? & ? & [? | ?]); tauto.
      + intros I HI R1 R2 H. cbn in H. cbn -[linf].
        split. { firstorder. }
        split. { firstorder. }
        destruct (classic (Downset.has R1 (rcp_forbid m1 m1' n1 n1'))); auto. right.
        destruct (classic (Downset.has (inf i:I, R2 i) (rcp_forbid m2 m2' n2 n2'))); auto. right.
        rewrite rcnext_inf.
        eapply IHk.
        * apply not_all_ex_not in H1 as [i Hi]. eauto.
        * intros [i Hi]. cbn. firstorder.
  Qed.
End TCONV.

(** *** Functoriality vs vertical composition *)

Section TCONV_VCOMP.
  Context {E1 F1 G1} (R1 : conv E1 F1) (S1 : conv F1 G1).
  Context {E2 F2 G2} (R2 : conv E2 F2) (S2 : conv F2 G2).

  Definition combine_ans (m1' : F1) (m2' : F2) (n1' : option (ar m1')) (n2' : option (ar m2')) :=
    match n1', n2' with
      | Some x, Some y => Some  (x, y)
      | _, _ => None
    end.

  Ltac refold :=
    repeat
      match goal with
      | |- context C[vcomp_has ?R ?S ?s] =>
        let P := context C[Downset.has (vcomp R S) s] in change P
      | |- context C[vcomp_at_has ?m1 ?m2 ?n1 ?n2 ?R ?S ?s] =>
        let P := context C[Downset.has (vcomp_at m1 m2 n1 n2 R S) s] in change P
      | |- context C[tconv_has ?R ?S ?s] =>
        let P := context C[Downset.has (tconv R S) s] in change P
      end.

  Instance funext_rel A B :
    subrelation (- ==> eq) (@eq (A -> B)).
  Proof.
    intros f g Hfg.
    apply FunctionalExtensionality.functional_extensionality.
    assumption.
  Qed.

  Instance sup_eq :
    Monotonic (@lsup) (forallr -, forallr -, (- ==> eq) ==> eq).
  Proof.
    repeat rstep. f_equal. rstep.
  Qed.

  Instance inf_eq :
    Monotonic (@linf) (forallr -, forallr -, (- ==> eq) ==> eq).
  Proof.
    repeat rstep. f_equal. rstep.
  Qed.

  Lemma tconv_vcomp_at m1' m2' n1' n2' :
    tconv (vcomp_at m1' n1' R1 S1) (vcomp_at m2' n2' R2 S2) =
    vcomp_at (m1', m2') (combine_ans m1' m2' n1' n2') (tconv R1 R2) (tconv S1 S2).
  Proof.
    (* we will need these property *)
    assert (EQSOME: forall A a (P : A -> Prop), (forall x:A, Some a = Some x -> P x) <-> P a).
    { clear. firstorder congruence. }
    assert (EQNONE: forall A (P : A -> Prop), (forall x:A, None = Some x -> P x) <-> True).
    { clear. firstorder congruence. }

    apply Downset.has_eq_ext. intro s.
    revert m1' m2' n1' n2' R1 R2 S1 S2.
    induction s as [[m1 m2] [m1'' m2''] |
                    [m1 m2] [m1'' m2''] [n1 n2] [n1'' n2''] |
                    [m1 m2] [m1'' m2''] [n1 n2] [n1'' n2''] k].
    - cbn. tauto.
    - cbn. intros.
      destruct n1' as [n1' | ], n2' as [n2' | ]; cbn;
        rewrite ?EQSOME, ?EQNONE; tauto.
    - cbn. intros.
      destruct n1' as [n1' | ], n2' as [n2' | ]; cbn;
        rewrite ?EQSOME, ?EQNONE; try tauto.
      refold.
      destruct (classic (Downset.has R1 (rcp_forbid m1 m1' n1 n1'))); try tauto.
      destruct (classic (Downset.has R2 (rcp_forbid m2 m2' n2 n2'))); try tauto.
      destruct (classic (Downset.has S1 (rcp_forbid m1' m1'' n1' n1''))); try tauto.
      destruct (classic (Downset.has S2 (rcp_forbid m2' m2'' n2' n2''))); try tauto.
      rewrite !rcnext_vcomp_at by auto.
      rewrite !rcnext_tconv by auto.
      rewrite !vcomp_expand.
      rewrite !tconv_sup.
      setoid_rewrite tconv_inf_l; [ | constructor; exact None ].
      setoid_rewrite tconv_inf_r; [ | constructor; exact None ].
      cbn. setoid_rewrite IHk. cbn.
      assert (forall m1' m2' (P : _ -> Prop),
                 (forall x y, P (combine_ans m1' m2' x y)) <-> (forall xy, P xy)).
      { clear. split. - intros H [[??]|]; cbn. apply (H (Some a) (Some a0)). apply (H None None).
                      - intros H [|] [|]; cbn; auto. }
      setoid_rewrite <- H3.
      assert (forall (P : F1 * F2 -> Prop), (exists xy, P xy) <-> (exists x y, P (x,y))).
      { intro. split. intros [[? ?] ?]; eauto. intros (? & ? & ?); eauto. }
      setoid_rewrite H4.
      tauto.
  Qed.

  Lemma tconv_vcomp :
    tconv (vcomp R1 S1) (vcomp R2 S2) = vcomp (tconv R1 R2) (tconv S1 S2).
  Proof.
    assert (OPTHAB: forall A, inhabited (option A)) by (constructor; apply None).
    rewrite !vcomp_expand.
    rewrite tconv_sup.
    setoid_rewrite tconv_inf_l; auto.
    setoid_rewrite tconv_inf_r; auto.
    setoid_rewrite tconv_vcomp_at.
    apply Downset.has_eq_ext. cbn.
    intros s. split.
    - intros (m1' & m2' & H). exists (m1', m2').
      intros [[x y] | ]; cbn. apply (H (Some x) (Some y)). apply (H None None).
    - intros ([m1' m2'] & H). exists m1', m2'. eauto.
  Qed.
End TCONV_VCOMP.

(** ** Tensor product of refinement squares *)

Section TRSQ.
  Context {E1 E2 F1 F2 E1' E2' F1' F2' : esig}.

  Variant trspos :
    forall {i1 i2 j1 j2 i j}, @rspos E1 E1' F1 F1' i1 j1 ->
                              @rspos E2 E2' F2 F2' i2 j2 ->
                              @rspos (tens E1 E2) (tens E1' E2') (tens F1 F2) (tens F1' F2') i j ->
                              @tpos E1 E2 F1 F2 i1 i2 i ->
                              @tpos E1' E2' F1' F2' j1 j2 j -> Type :=
    | trs_ready :
        trspos rs_ready
               rs_ready
               rs_ready
               tp_ready
               tp_ready
    | trs_running q1 q2 q1' q2' :
        trspos (rs_running q1 q1')
               (rs_running q2 q2')
               (rs_running (q1,q2) (q1',q2'))
               (tp_running q1 q2)
               (tp_running q1' q2')
    | trs_suspended q1 q2 q1' q2' m1 m2 m1' m2' :
        trspos (rs_suspended q1 q1' m1 m1')
               (rs_suspended q2 q2' m2 m2')
               (rs_suspended (q1,q2) (q1',q2') (m1,m2) (m1',m2'))
               (tp_suspended q1 q2 m1 m2)
               (tp_suspended q1' q2' m1' m2').

  Hint Constructors tstrat_has : core.

  Lemma trsp :
    forall {i1 i2 j1 j2 i j u1 u2 u v v'} {p : @trspos i1 i2 j1 j2 i j u1 u2 u v v'}
      (R1 : conv E1 E1') (S1 : conv F1 F1') (s1 : @play E1 F1 i1) (τ1 : strat E1' F1' j1)
      (R2 : conv E2 E2') (S2 : conv F2 F2') (s2 : @play E2 F2 i2) (τ2 : strat E2' F2' j2)
      (s : @play (tens E1 E2) (tens F1 F2) i),
    rsp R1 S1 u1 s1 τ1 ->
    rsp R2 S2 u2 s2 τ2 ->
    tstrat_has v s1 s2 s ->
    match p with
      | trs_suspended q1 q2 q1' q2' m1 m2 m1' m2' =>
        Downset.has R1 (rcp_allow m1 m1') ->
        Downset.has R2 (rcp_allow m2 m2') ->
        rsp (tconv R1 R2) (tconv S1 S2) u s (tstrat v' τ1 τ2)
      | _ =>
        rsp (tconv R1 R2) (tconv S1 S2) u s (tstrat v' τ1 τ2)
    end.
  Proof.
    intros i1 i2 j1 j2 i j u1 u2 u v v' p R1 S1 s1 τ1 R2 S2 s2 τ2 s H1 H2 Hs.
    revert j1 j2 j u1 u2 u v' p R1 S1 τ1 R2 S2 τ2 H1 H2.
    induction Hs; intros.
    - (* ready *)
      dependent destruction p.
      dependent destruction H1.
      dependent destruction H2.
      constructor; cbn; eauto.
    - (* incoming question *)
      dependent destruction p.
      dependent destruction H1.
      dependent destruction H2.
      constructor; cbn; eauto.
      intros [q1' q2'] [Hq1 Hq2].
      rewrite tstrat_next_oq.
      eapply (IHHs _ _ _ _ _ _ _ (trs_running q1 q2 q1' q2')); eauto.
    - (* outgoing question *)
      dependent destruction p.
      dependent destruction H1.
      dependent destruction H2.
      apply rsp_pq with (m2 := (m3,m4)); cbn; eauto.
      rewrite tstrat_next_pq.
      eapply (IHHs _ _ _ _ _ _ _ (trs_suspended q1 q2 q1' q2' m1 m2 m3 m4)); eauto.
    - (* suspended *)
      dependent destruction p.
      dependent destruction H1.
      dependent destruction H2.
      constructor; cbn; eauto.
    - (* environment answer *)
      dependent destruction p. intros Hm1 Hm2.
      dependent destruction H1.
      dependent destruction H2.
      constructor; cbn; eauto.
      intros [n1' n2'] Hn.
      apply not_and_or in Hn as [ | Hn]; try tauto.
      apply not_and_or in Hn as [ | Hn]; try tauto.
      apply not_or_and in Hn as [Hn1 Hn2].
      assert (tconv (rcnext m1 m1' n1 n1' R1) (rcnext m2 m2' n2 n2' R2) [=
              rcnext (m1,m2) (m1',m2') (n1,n2) (n1',n2') (tconv R1 R2)) as HR.
      { clear - Hm1 Hm2 Hn1 Hn2. cbn. firstorder. }
      rewrite <- HR.
      setoid_rewrite tstrat_next_oa.
      eapply (IHHs _ _ _ _ _ _ _ (trs_running q1 q2 q1' q2')); eauto.
    - (* component answer *)
      dependent destruction p.
      dependent destruction H1.
      dependent destruction H2.
      apply rsp_pa with (r2 := (r3,r4)); cbn; [firstorder | ].
      assert (rcnext (q1,q2) (q1',q2') (r1,r2) (r3,r4) (tconv S1 S2) [=
              tconv (rcnext q1 q1' r1 r3 S1) (rcnext q2 q2' r2 r4 S2)) as HS.
      { cbn. firstorder. }
      rewrite HS.
      rewrite tstrat_next_pa.
      eapply (IHHs _ _ _ _ _ _ _ trs_ready); eauto.
  Qed.
End TRSQ.

(** ** Stateful lenses *)

Section LENS.

  Record lens {U V} :=
    {
      get : U -> V;
      set : U -> V -> U;
      get_set u v : get (set u v) = v;
      set_get u : set u (get u) = u;
      set_set u v v' : set (set u v) v' = set u v';
    }.

  Global Arguments lens : clear implicits.

  Record slens {U V} :=
    {
      slens_state : Type;
      slens_init : slens_state;
      slens_lens :> lens (V * slens_state) U;
    }.

  Global Arguments slens : clear implicits.

  (** Promoting a stateful lens to a strategy *)

  Definition glob U : esig := {| op := U; ar _ := U |}.

  Context {U V : Type}.

  (** Between any two visits back to the [ready] state, the strategy
    associated with a lens only needs to remember which [u] is
    currently the latest candidate for being written back into the
    [(v, p)] pair before we give it back to the environment. Given the
    lens laws, there are many equivalent ways to formulate it as far
    as when [get] and [set] are being used. But since we need to
    remember the latest incoming question for play structure purposes
    anyway, we choose to keep it constant and use this solution. *)

  Variant sls_state {P} : @position (glob U) (glob V) -> Type :=
    | sls_ready (p : P) : sls_state ready
    | sls_running (p : P) v (u : U) : sls_state (running v)
    | sls_suspended (p : P) v u : sls_state (suspended v u).

  Inductive sls_has {P} (f: lens (V*P) U): forall {i}, _ i -> play i -> Prop :=
    | sls_has_ready p :
        sls_has f (sls_ready p) pnil_ready
    | sls_has_oq p v u s :
        sls_has f (sls_running p v u) s ->
        get f (v, p) = u ->
        sls_has f (sls_ready p) (oq v :: s)
    | sls_has_pq p v u s :
        sls_has f (sls_suspended p v u) s ->
        sls_has f (sls_running p v u) (pq u :: s)
    | sls_has_suspended p v u :
        sls_has f (sls_suspended p v u) (pnil_suspended v u)
    | sls_has_oa p v u u' s :
        sls_has f (sls_running p v u') s ->
        sls_has f (sls_suspended p v u) (@oa _ _ v u u' :: s)
    | sls_has_pa p v u p' v' s :
        sls_has f (sls_ready p') s ->
        set f (v, p) u = (v', p') ->
        sls_has f (sls_running p v u) (@pa _ (glob V) v v' :: s).

  Obligation Tactic := cbn.

  Program Definition sls (f : slens U V) : strat (glob U) (glob V) ready :=
    {| Downset.has := sls_has (slens_lens f) (sls_ready (slens_init f)) |}.
  Next Obligation.
    intros f.
    generalize (@ready (glob U) (glob V)), (sls_ready (slens_init f)).
    intros i q x y Hxy Hy. revert q Hy.
    induction Hxy; intros;
      try dependent destruction q;
      try dependent destruction Hy;
      econstructor; eauto.
  Qed.
End LENS.
