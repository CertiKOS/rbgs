Require Import Classical.
Require Import FunctionalExtensionality.
Require Import Program.Equality.
Require Import LogicalRelations.
Require Import Poset.
Require Import Lattice.
Require Import Downset.

(** * Preliminaries *)

(** This instance is needed for rewrites under [sup] and [inf] to work. *)

Instance funext_subrel {A B} :
  subrelation (pointwise_relation _ eq) (@eq (A -> B)).
Proof.
  exact (@functional_extensionality A B).
Qed.

(** Helpful tactic for messy inversions *)

Ltac xsubst :=
  repeat progress
    (match goal with
     | H : ?x = ?x |- _ =>
         clear H
     | H : existT _ _ _ = existT _ _ _ |- _ =>
         apply inj_pair2 in H
     end ||
     subst ||
     discriminate).

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

(** *** Signature homomorphisms *)

(** Although they are not defined explicitly in the paper, signature
  homomorphisms of the following kind capture the patterns in many
  basic strategies with a fixed shape similar to that of [id].
  They correspond to natural transformations between the polynomial
  [Set] endofunctors associated with the signatures.

  Defining such strategies based on their signature homomorphism
  representation is both more convenient and makes it easier to reason
  about them. *)

(** **** Definition *)

(** Although we could use [sigT] and define signature homomorphisms as
  terms of type [forall q : op F, {m : op E & ar m -> ar q}], the
  specialized version below is a little bit easier to use in some cases.
  It is essentially the [Set] endofunctor associated with [E]. *)

Record application (E : esig) (X : Type) :=
  econs {
    operator : op E;
    operand : ar operator -> X;
  }.

Coercion application : esig >-> Funclass.
Arguments econs {E X}.
Arguments operator {E X}.
Arguments operand {E X}.

Definition emor (E F : esig) :=
  forall q : F, application E (ar q).

Declare Scope emor_scope.
Delimit Scope emor_scope with emor.
Bind Scope emor_scope with emor.
Open Scope emor_scope.

(** **** Compositional structure *)

Definition eid {E} : emor E E :=
  fun q => econs q (fun r => r).

Definition ecomp {E F G} (g : emor F G) (f : emor E F) : emor E G :=
  fun q =>
    econs (operator (f (operator (g q))))
          (fun v => operand _ (operand _ v)).

Lemma ecomp_eid_l {E F} (f : emor E F) :
  ecomp eid f = f.
Proof.
  apply functional_extensionality_dep. intros q.
  unfold ecomp. cbn. destruct (f q) as [m k]. cbn. reflexivity.
Qed.

Lemma ecomp_eid_r {E F} (f : emor E F) :
  ecomp f eid = f.
Proof.
  apply functional_extensionality_dep. intros q.
  unfold ecomp. cbn. destruct (f q) as [m k]. cbn. reflexivity.
Qed.

Lemma ecomp_assoc {E F G H} (f : emor E F) (g : emor F G) (h : emor G H) :
  ecomp (ecomp h g) f = ecomp h (ecomp g f).
Proof.
  apply functional_extensionality_dep. intro q.
  reflexivity.
Qed.

Infix "∘" := ecomp : emor_scope.

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

(** *** Monoidal structure with respect to [emor] *)

(** **** Functoriality of [fcomp] *)

Definition fcomp_emor {E1 F1 E2 F2} (f1: emor E1 F1) (f2: emor E2 F2): emor (E1+E2) (F1+F2) :=
  fun q =>
    match q with
      | inl q1 => econs (inl (operator (f1 q1))) (operand (f1 q1))
      | inr q2 => econs (inr (operator (f2 q2))) (operand (f2 q2))
    end.

Infix "+" := fcomp_emor : emor_scope.

Lemma fcomp_eid (E F : esig) :
  @eid E + @eid F = @eid (E + F).
Proof.
  apply functional_extensionality_dep. intros q.
  destruct q; reflexivity.
Qed.

Lemma fcomp_ecomp {E1 F1 G1 E2 F2 G2 : esig} :
  forall (f1 : emor E1 F1) (g1 : emor F1 G1) (f2 : emor E2 F2) (g2 : emor F2 G2),
    (g1 ∘ f1) + (g2 ∘ f2) = (g1 + g2) ∘ (f1 + f2).
Proof.
  intros.
  apply functional_extensionality_dep. intros q.
  unfold ecomp, fcomp_emor.
  destruct q as [q1 | q2]; cbn.
  - destruct (g1 q1) as [m1 k].
    destruct (f1 m1) as [u1 c].
    reflexivity.
  - destruct (g2 q2) as [m2 k].
    destruct (f2 m2) as [u2 c].
    reflexivity.
Qed.

(** **** Left (λ) and right (ρ) unitors and their inverses *)

Definition flu {E} : emor (0 + E) E :=
  fun q => econs (inr q) (fun r => r).

Definition flur {E} : emor E (0 + E) :=
  fun q => match q with
             | inl q => match q with end
             | inr q => econs q (fun r => r)
           end.

Lemma flu_flur {E} :
  ecomp (@flu E) (@flur E) = eid.
Proof.
  apply functional_extensionality_dep. intros q.
  reflexivity.
Qed.

Lemma flur_flu {E} :
  ecomp (@flur E) (@flu E) = eid.
Proof.
  apply functional_extensionality_dep. intros q.
  destruct q as [[] | ]; reflexivity.
Qed.

Definition fru {E} : emor (E + 0) E :=
  fun q => econs (inl q) (fun r => r).

Definition frur {E} : emor E (E + 0) :=
  fun q => match q with
             | inl q => econs q (fun r => r)
             | inr q => match q with end
           end.

Lemma fru_frur {E} :
  ecomp (@fru E) (@frur E) = eid.
Proof.
  apply functional_extensionality_dep. intros q.
  reflexivity.
Qed.

Lemma frur_fru {E} :
  ecomp (@frur E) (@fru E) = eid.
Proof.
  apply functional_extensionality_dep. intros q.
  destruct q as [ | []]; reflexivity.
Qed.

(** **** Associator (α) and its inverse *)

Definition fassoc {E F G} : emor ((E + F) + G) (E + (F + G)) :=
  fun q =>
    match q with
      | inl q1 =>       econs (inl (inl q1)) (fun r => r)
      | inr (inl q2) => econs (inl (inr q2)) (fun r => r)
      | inr (inr q3) => econs (inr q3)       (fun r => r)
    end.

Definition fassocr {E F G} : emor (E + (F + G)) ((E + F) + G) :=
  fun q =>
    match q with
      | inl (inl q1) => econs (inl q1)       (fun r => r)
      | inl (inr q2) => econs (inr (inl q2)) (fun r => r)
      | inr q3 =>       econs (inr (inr q3)) (fun r => r)
    end.

Lemma fassocr_fassoc {E F G} :
  ecomp (@fassocr E F G) (@fassoc E F G) = eid.
Proof.
  apply functional_extensionality_dep. intro q.
  destruct q as [[ | ] | ]; reflexivity.
Qed.

Lemma fassoc_fassocr {E F G} :
  ecomp (@fassoc E F G) (@fassocr E F G) = eid.
Proof.
  apply functional_extensionality_dep. intro q.
  destruct q as [ | [ | ]]; reflexivity.
Qed.

(** **** Triangle and pentagon identities *)

Lemma flu_fassoc E F :
  (@eid E + @flu F) ∘ fassoc = @fru E + @eid F.
Proof.
  apply functional_extensionality_dep. intro q.
  destruct q as [ | ]; reflexivity.
Qed.

Lemma fassoc_fassoc E F G H :
  @fassoc E F (G + H) ∘ @fassoc (E + F) G H =
  (@eid E + @fassoc F G H) ∘ @fassoc E (F + G) H ∘ (@fassoc E F G + @eid H).
Proof.
  apply functional_extensionality_dep. intro q.
  destruct q as [ | [ | [ | ]]]; reflexivity.
Qed.

(** **** Braiding (γ) *)

Definition fswap {E F} : emor (E + F) (F + E) :=
  fun q =>
    match q with
      | inl q => econs (inr q) (fun r => r)
      | inr q => econs (inl q) (fun r => r)
    end.

(** **** Unit coherence property *)

Lemma fswap_unit {E} :
  flu ∘ (@fswap E 0) = fru.
Proof.
  reflexivity.
Qed.

(** **** Hexagon identity *)

Lemma fswap_assoc {E F G} :
  (@eid F + @fswap E G) ∘ @fassoc F E G ∘ (@fswap E F + @eid G) =
  @fassoc F G E ∘ @fswap E (F + G) ∘ @fassoc E F G.
Proof.
  apply functional_extensionality_dep. intros q.
  destruct q as [ | [ | ]]; reflexivity.
Qed.

(** **** The braiding is its own inverse *)

Lemma fswap_fswap {E F} :
  @fswap F E ∘ @fswap E F = @eid (E + F).
Proof.
  apply functional_extensionality_dep. intro q.
  destruct q; reflexivity.
Qed.

(** *** Duplication and projections *)

(** Flat composition is the cartesian product with respect to effect
  signature homomorphisms. This will no longer be true when we move to
  our more sophisticated strategy construction, however the morphisms
  below remain useful as a way to duplicate or forget parts of a
  component's interface. *)

(** **** Terminal morphism *)

Definition fdrop {E} : emor E 0 :=
  fun q => match q with end.

Lemma fdrop_uniq {E} (f : emor E 0) :
  f = fdrop.
Proof.
  apply functional_extensionality_dep.
  intros [ ].
Qed.

(** **** Left projection *)

Definition ffst {E F} : emor (E + F) E :=
  fun q => econs (inl q) (fun r => r).

Lemma ffst_fdrop {E F} :
  @ffst E F = fru ∘ (eid + fdrop).
Proof.
  apply functional_extensionality_dep. intro q.
  reflexivity.
Qed.

(** **** Right projection *)

Definition fsnd {E F} : emor (E + F) F :=
  fun q => econs (inr q) (fun r => r).

Lemma fsnd_fdrop {E F} :
  @fsnd E F = flu ∘ (fdrop + eid).
Proof.
  apply functional_extensionality_dep. intro q.
  reflexivity.
Qed.

(** **** Diagonal morphism *)

Definition fdup {E} : emor E (E + E) :=
  fun q => match q with
             | inl q => econs q (fun r => r)
             | inr q => econs q (fun r => r)
           end.

Lemma ffst_fdup {E} :
  ffst ∘ fdup = @eid E.
Proof.
  apply functional_extensionality_dep. intro q.
  reflexivity.
Qed.

Lemma fsnd_fdup {E} :
  fsnd ∘ fdup = @eid E.
Proof.
  apply functional_extensionality_dep. intro q.
  reflexivity.
Qed.

(** **** Tupling *)

Section FPAIR.
  Context {E F1 F2} (f1 : emor E F1) (f2 : emor E F2).

  Definition fpair : emor E (F1 + F2) :=
    fun q => match q with
               | inl q1 => f1 q1
               | inr q2 => f2 q2
             end. 

  Lemma fpair_uniq (f : emor E (F1 + F2)) :
    ffst ∘ f = f1 ->
    fsnd ∘ f = f2 ->
    f = fpair.
  Proof.
    unfold fpair, ecomp. intros H1 H2. subst.
    apply functional_extensionality_dep. intro q.
    destruct q, f; reflexivity.
  Qed.

  Lemma fpair_expand :
    fpair = (f1 + f2) ∘ fdup.
  Proof.
    symmetry. apply fpair_uniq;
    apply functional_extensionality_dep; intro q;
    unfold ecomp, fdup, fcomp_emor, ffst, fsnd; cbn;
    destruct (_ q); reflexivity.
  Qed.
End FPAIR.


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

  Lemma pref_refl i s :
    @pref i s s.
  Proof.
    induction s; constructor; auto.
  Qed.

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
    poset_carrier (downset (play_poset p)).

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

  Lemma pcons_oa_inv q m (n1 n2 : ar m) (s1 s2: play (running q)) :
    pcons (oa n1) s1 = pcons (oa n2) s2 -> n1 = n2 /\ s1 = s2.
  Proof.
    intro H. dependent destruction H; auto. 
  Qed.

  Lemma pcons_pa_inv q (r1 r2 : ar q) s1 s2 :
    pcons (pa r1) s1 = pcons (pa r2) s2 -> r1 = r2 /\ s1 = s2.
  Proof.
    intro H. dependent destruction H; auto. 
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

Notation "E ->> F" := (strat E F ready) (at level 99, right associativity).
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

(** *** Signature homomorphisms *)

(** Signature homomorphisms define simple strategies. *)

Section EMOR_STRAT.
  Context {E F} (f : emor E F).
  Obligation Tactic := cbn.

  Variant epos : position -> Type :=
    | eready : epos ready
    | esuspended q : epos (suspended q (operator (f q))).

  Inductive emor_has : forall {i}, epos i -> play i -> Prop :=
    | emor_ready :
        emor_has eready pnil_ready
    | emor_question q s :
        emor_has (esuspended q) s ->
        emor_has eready (oq q :: pq (operator (f q)) :: s)
    | emor_suspended q :
        emor_has (esuspended q) (pnil_suspended _ _)
    | emor_answer q r s :
        emor_has eready s ->
        emor_has (esuspended q) (oa r :: pa (operand (f q) r) :: s).

  Program Definition emor_when {i} p : strat E F i :=
    {| Downset.has := emor_has p |}.
  Next Obligation.
    intros i p s t Hst Ht.
    induction Ht; repeat (dependent destruction Hst; try constructor; eauto).
  Qed.

  Definition emor_strat :=
    emor_when eready.

  (** **** Residuals *)

  Lemma emor_next_question q :
    next (pq (operator (f q))) (next (oq q) emor_strat) =
    emor_when (esuspended q).
  Proof.
    apply antisymmetry; cbn; intros s Hs.
    - dependent destruction Hs; auto.
    - constructor; auto.
  Qed.

  Lemma emor_next_answer q r :
    next (pa (operand (f q) r)) (next (oa r) (emor_when (esuspended q))) =
    emor_strat.
  Proof.
    apply antisymmetry; cbn; intros s Hs.
    - dependent destruction Hs; auto.
    - constructor; auto.
  Qed.

  Lemma emor_next q r :
    (next (pa (operand (f q) r))
       (next (oa r)
          (next (pq (operator (f q)))
             (next (oq q) emor_strat)))) =
      emor_strat.
  Proof.
    rewrite emor_next_question, emor_next_answer.
    reflexivity.
  Qed.
End EMOR_STRAT.

Arguments eready {_ _ _}.
Arguments esuspended {_ _ _}.

(** ** §3.2 Layered Composition *)

(** *** Def 3.4 (Layered Composition of Strategies) *)

(** The identity strategy can be defined using the corresponding
  signature homomorphism. *)

Notation id E := (emor_strat (@eid E)).

Lemma id_next {E} q r :
  (next (pa r) (next (oa r) (next (pq q) (next (oq q) (id E))))) = id E.
Proof.
  apply emor_next.
Qed.

(** Layered composition is more complex. *)

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

  Hint Constructors emor_has comp_has : core.

  (** When the identity is composed on the left,
    it passes through incoming interactions unchanged. *)

  Definition id_pos_l (i : @position E F) : @position F F :=
    match i with
      | ready => ready
      | running q => suspended q (operator (eid q))
      | suspended q m => suspended q (operator (eid q))
    end.

  Definition id_idpos_l i : epos eid (id_pos_l i) :=
    match i with
      | ready => eready
      | running q => esuspended q
      | suspended q m => esuspended q
    end.

  Definition id_cpos_l i : cpos (id_pos_l i) i i :=
    match i with
      | ready => cpos_ready
      | running q => cpos_right q q
      | suspended q m => cpos_suspended q q m
    end.

  Lemma compose_id_has_l_gt {i} (s : @play E F i) :
    exists t, emor_has eid (id_idpos_l i) t /\ comp_has (id_cpos_l i) t s s.
  Proof.
    induction s; cbn -[eid]; eauto 10.
    destruct IHs as (t & Ht & Hst).
    dependent destruction m; cbn -[eid] in *; eauto 10.
  Qed.

  Lemma compose_id_has_l_lt {i} (s s': @play E F i) (t: @play F F (id_pos_l i)):
    emor_has eid (id_idpos_l i) t ->
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
    compose_when (id_cpos_l i) (emor_when eid (id_idpos_l i)) σ = σ.
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
      | suspended q m => suspended m (operator (eid m))
    end.

  Definition id_idpos_r i : epos eid (id_pos_r i) :=
    match i with
      | ready => eready
      | running q => eready
      | suspended q m => esuspended m
    end.

  Definition id_cpos_r i : cpos i (id_pos_r i) i :=
    match i with
      | ready => cpos_ready
      | running q => cpos_left q
      | suspended q m => cpos_suspended q m m
    end.

  Lemma compose_id_has_r_gt {i} (s : @play E F i) :
    exists t, emor_has eid (id_idpos_r i) t /\ comp_has (id_cpos_r i) s t s.
  Proof.
    induction s; cbn -[eid]; eauto 10.
    destruct IHs as (t & Ht & Hst).
    dependent destruction m; cbn -[eid] in *; eauto 10.
  Qed.

  Lemma compose_id_has_r_lt {i} (s s': @play E F i) (t: @play E E (id_pos_r i)):
    emor_has eid (id_idpos_r i) t ->
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
    compose_when (id_cpos_r i) σ (emor_when eid (id_idpos_r i)) = σ.
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

Arguments retraction {E F} f {g _}.

Class Isomorphism {E F} (f : E ->> F) (g : F ->> E) :=
  {
    iso_fw :> Retraction f g;
    iso_bw :> Retraction g f;
  }.

Lemma retract {E F G} `{Hfg : Retraction F G} (σ : strat E G ready) :
  f ⊙ g ⊙ σ = σ.
Proof.
  rewrite <- compose_assoc.
  rewrite (retraction f).
  rewrite compose_id_l.
  reflexivity.
Qed.

(** *** Functoriality of [emor_strat] *)

Section ESTRAT_COMPOSE.
  Context {E F G} (g : emor F G) (f : emor E F).

  Variant cepos :
    forall {i j k}, @epos F G g i -> @epos E F f j -> @epos E G (ecomp g f) k ->
                    @cpos E F G i j k -> Type :=
    | cepos_ready :
        cepos eready
              eready
              eready
              cpos_ready
    | cepos_suspended q :
        cepos (esuspended q)
              (esuspended (operator (g q)))
              (esuspended q)
              (cpos_suspended _ _ _).

  Hint Constructors emor_has comp_has.

  Lemma estrat_ecomp_when {i j k pi pj pk pc} (p : @cepos i j k pi pj pk pc) :
    emor_when (ecomp g f) pk =
    compose_when pc (emor_when g pi) (emor_when f pj).
  Proof.
    apply antisymmetry.
    - cbn. intros st Hst. revert i j pi pj pc p.
      induction Hst; intros; dependent destruction p; eauto.
      + (* question *)
        edestruct (IHHst _ _ _ _ _ (cepos_suspended q)) as (?&?&?&?&?); eauto 10.
      + (* answer *)
        edestruct (IHHst _ _ _ _ _ cepos_ready) as (?&?&?&?&?); eauto 10.
    - cbn. intros st (s & t & Hs & Ht & Hst). revert j k pj pk pc p st t Ht Hst.
      induction Hs; intros.
      + (* ready *)
        dependent destruction Hst.
        dependent destruction p.
        constructor.
      + (* question*)
        dependent destruction Hst.
        dependent destruction Hst.
        dependent destruction Ht.
        dependent destruction Hst.
        dependent destruction p.
        apply (emor_question (ecomp g f)).
        eapply (IHHs _ _ _ _ _ (cepos_suspended q)); eauto.
      + (* suspended *)
        dependent destruction p.
        dependent destruction Ht;
          dependent destruction Hst.
        * apply (emor_suspended (ecomp g f)).
        * dependent destruction Hst.
      + (* answer *)
        dependent destruction p.
        dependent destruction Ht;
          dependent destruction Hst.
        * apply (emor_suspended (ecomp g f)).
        * dependent destruction Hst.
          dependent destruction Hst.
          apply (emor_answer (ecomp g f)).
          eapply (IHHs _ _ _ _ _ cepos_ready); eauto.
  Qed.

  Lemma emor_strat_ecomp :
    emor_strat (ecomp g f) = compose (emor_strat g) (emor_strat f).
  Proof.
    apply (estrat_ecomp_when cepos_ready).
  Qed.
End ESTRAT_COMPOSE.

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

  Lemma fcomp_next_oq_l q σ1 σ2 :
    next (oq (inl q)) (fcomp_when fcpos_ready σ1 σ2) =
    fcomp_when (fcpos_running_l q) (next (oq q) σ1) σ2.
  Proof.
    apply antisymmetry; intros s; cbn; intros (s1 & s2 & Hs1 & Hs2 & Hs).
    - dependent destruction Hs. eauto.
    - eauto 10.
  Qed.

  Lemma fcomp_next_oq_r q σ1 σ2 :
    next (oq (inr q)) (fcomp_when fcpos_ready σ1 σ2) =
    fcomp_when (fcpos_running_r q) σ1 (next (oq q) σ2).
  Proof.
    apply antisymmetry; intros s; cbn; intros (s1 & s2 & Hs1 & Hs2 & Hs).
    - dependent destruction Hs. eauto.
    - eauto 10.
  Qed.

  Lemma fcomp_next_pq_l q m σ1 σ2 :
    next (pq (inl m)) (fcomp_when (fcpos_running_l q) σ1 σ2) =
    fcomp_when (fcpos_suspended_l q m) (next (pq m) σ1) σ2.
  Proof.
    apply antisymmetry; intros s; cbn; intros (s1 & s2 & Hs1 & Hs2 & Hs).
    - dependent destruction Hs. eauto.
    - eauto 10.
  Qed.

  Lemma fcomp_next_pq_r q m σ1 σ2 :
    next (pq (inr m)) (fcomp_when (fcpos_running_r q) σ1 σ2) =
    fcomp_when (fcpos_suspended_r q m) σ1 (next (pq m) σ2).
  Proof.
    apply antisymmetry; intros s; cbn; intros (s1 & s2 & Hs1 & Hs2 & Hs).
    - dependent destruction Hs. eauto.
    - eauto 10.
  Qed.

  Lemma fcomp_next_oa_l q m n σ1 σ2 :
    next (oa n) (fcomp_when (fcpos_suspended_l q m) σ1 σ2) =
    fcomp_when (fcpos_running_l q) (next (oa (m:=m) n) σ1) σ2.
  Proof.
    apply antisymmetry; intros s; cbn; intros (s1 & s2 & Hs1 & Hs2 & Hs).
    - simple inversion Hs; xsubst.
      inversion H0. xsubst.
      apply pcons_oa_inv in H6 as [<- <-].
      exists s0, s2. easy.
    - eauto 10.
  Qed.

  Lemma fcomp_next_oa_r q m n σ1 σ2 :
    next (oa n) (fcomp_when (fcpos_suspended_r q m) σ1 σ2) =
    fcomp_when (fcpos_running_r q) σ1 (next (oa (m:=m) n) σ2).
  Proof.
    apply antisymmetry; intros s; cbn; intros (s1 & s2 & Hs1 & Hs2 & Hs).
    - simple inversion Hs; xsubst.
      inversion H1. xsubst. apply pcons_oa_inv in H6 as [<- <-]. eauto.
    - eauto 10.
  Qed.

  Lemma fcomp_next_pa_l q r σ1 σ2 :
    next (pa r) (fcomp_when (fcpos_running_l q) σ1 σ2) =
    fcomp_when fcpos_ready (next (pa (q:=q) r) σ1) σ2.
  Proof.
    apply antisymmetry; intros s; cbn; intros (s1 & s2 & Hs1 & Hs2 & Hs).
    - simple inversion Hs; xsubst.
      inversion H0. xsubst. apply pcons_pa_inv in H6 as [<- <-]. eauto.
    - eauto 10.
  Qed.

  Lemma fcomp_next_pa_r q r σ1 σ2 :
    next (pa r) (fcomp_when (fcpos_running_r q) σ1 σ2) =
    fcomp_when fcpos_ready σ1 (next (pa (q:=q) r) σ2).
  Proof.
    apply antisymmetry; intros s; cbn; intros (s1 & s2 & Hs1 & Hs2 & Hs).
    - simple inversion Hs; xsubst.
      inversion H1. xsubst. apply pcons_pa_inv in H6 as [<- <-]. eauto.
    - eauto 10.
  Qed.
End FCOMP_STRAT.

Notation fcomp_st := (fcomp_when fcpos_ready).
Infix "+" := fcomp_st : strat_scope.

(** *** Embedding signature homomorphisms preserves flat composition *)

Section ESTRAT_FCOMP.
  Context {E1 E2 F1 F2} (f1 : emor E1 F1) (f2 : emor E2 F2).

  Hint Constructors emor_has fcomp_has.

  Lemma emor_strat_fcomp_when {i1 i2 i} p1 p2 p p' :
    @emor_when _ _ (f1 + f2) i p =
    fcomp_when p' (@emor_when E1 F1 f1 i1 p1)
                  (@emor_when E2 F2 f2 i2 p2).
  Proof.
    apply antisymmetry; cbn.
    - intros s Hs. revert i1 i2 p1 p2 p'.
      induction Hs; cbn; intros.
      + (* ready *)
        dependent destruction p'.
        dependent destruction p1.
        dependent destruction p2.
        eauto 10.
      + (* question *)
        dependent destruction p'.
        dependent destruction p1.
        dependent destruction p2.
        destruct q as [q1 | q2].
        * destruct (IHHs _ _ (esuspended q1) eready (fcpos_suspended_l q1 _))
            as (s1 & s2 & Hs1 & Hs2 & Hs12).
          exists (oq q1 :: pq (operator (f1 q1)) :: s1), s2.
          repeat (constructor; auto).
        * destruct (IHHs _ _ eready (esuspended q2) (fcpos_suspended_r q2 _))
            as (s1 & s2 & Hs1 & Hs2 & Hs12).
          exists s1, (oq q2 :: pq (operator (f2 q2)) :: s2).
          repeat (constructor; auto).
      + (* suspended *)
        dependent destruction p';
        dependent destruction p1;
        dependent destruction p2.
        * exists (pnil_suspended _ _), pnil_ready.
          repeat (constructor; auto).
        * exists pnil_ready, (pnil_suspended _ _).
          repeat (constructor; auto).
      + (* answer *)
        destruct (IHHs _ _ eready eready fcpos_ready)
          as (s1 & s2 & Hs1 & Hs2 & Hs12).
        dependent destruction p';
        dependent destruction p1;
        dependent destruction p2.
        * exists (oa (m := operator (f1 q1)) r :: pa (operand (f1 q1) r) :: s1), s2.
          repeat (constructor; auto).
        * exists s1, (oa (m := operator (f2 q2)) r :: pa (operand (f2 q2) r) :: s2).
          repeat (constructor; auto).
    - intros s (s1 & s2 & Hs1 & Hs2 & Hs).
      revert i2 p2 s2 Hs2 i p p' s Hs.
      induction Hs1 as [ | q1 s1 Hs1 IHs1 | q1 | q1 r1 s1 Hs1 IHs1].
      + (** s1 is done, but s2 may have more to do *)
        intros ? ? ? ?.
        induction Hs2 as [ | q2 s2 Hs2 IHs2 | q2 | q2 r2 s2 Hs2 IHs2]; intros;
        do 2 try dependent destruction Hs; dependent destruction p.
        * constructor.
        * constructor; eauto.
        * constructor.
        * apply (emor_answer (f1 + f2) (inr q2)); eauto.
      + (** s1 doing a question next, but s2 may do stuff first *)
        intros ? ? ? ?.
        induction Hs2 as [ | q2 s2 Hs2 IHs2 | q2 | q2 r2 s2 Hs2 IHs2]; intros.
        * dependent destruction Hs; dependent destruction Hs; dependent destruction p.
          constructor; eauto.
        * dependent destruction Hs; dependent destruction Hs; dependent destruction p.
          -- (* s1 goes first *) eapply (emor_question (f1 + f2) (inl q1)); eauto.
          -- (* s2 goes first *) eapply (emor_question (f1 + f2) (inr q2)); eauto.
        * dependent destruction Hs. dependent destruction p.
          constructor.
        * dependent destruction Hs; dependent destruction Hs; dependent destruction p.
          eapply (emor_answer (f1 + f2) (inr q2)); eauto.
      + (** s1 suspended *)
        intros. dependent destruction Hs. dependent destruction p.
        econstructor.
      + (** s1 answer *)
        intros. do 2 dependent destruction Hs. dependent destruction p.
        eapply (emor_answer (f1 + f2) (inl q1)); eauto.
  Qed.

  Lemma emor_strat_fcomp :
    emor_strat (f1 + f2) = emor_strat f1 + emor_strat f2.
  Proof.
    apply (emor_strat_fcomp_when eready eready eready fcpos_ready).
  Qed.
End ESTRAT_FCOMP.

(** More generally, we can reuse the structural isomorphisms defined
  above as signature homomorphisms for strategy-level monoidal
  structure. From now on, we will use [emor_strat] implcitly. *)

Coercion emor_strat : emor >-> strat.

(** *** Theorem 3.7 (Properties of flat composition) *)

Lemma fcomp_id {E1 E2} :
  id E1 + id E2 = id (E1 + E2).
Proof.
  rewrite <- emor_strat_fcomp, fcomp_eid.
  reflexivity.
Qed.

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

  Hint Constructors comp_has fcomp_has pref : core.

  Lemma compose_fcomp_has {i1 i2 j1 j2 i12 j12 ij1 ij2 ij12 p1 p2 p12 qi qj qij} :
    @fccpos i1 i2 j1 j2 i12 j12 ij1 ij2 ij12 p1 p2 p12 qi qj qij ->
    forall s1 s2 t1 t2 st1 st2 st,
      comp_has p1 s1 t1 st1 ->
      comp_has p2 s2 t2 st2 ->
      fcomp_has p12 st1 st2 st ->
      exists s1' s2' t1' t2' s12 t12,
        s1' [= s1 /\ s2' [= s2 /\ t1' [= t1 /\ t2' [= t2 /\
        fcomp_has qi s1' s2' s12 /\
        fcomp_has qj t1' t2' t12 /\
        comp_has qij s12 t12 st.
  Proof.
    intros p s1 s2 t1 t2 st1 st2 st Hst1 Hst2 Hst. cbn.
    revert i2 j2 i12 j12 ij2 ij12 p2 p12 qi qj qij p s2 t2 st2 st Hst2 Hst.
    induction Hst1; intros.
    - (* [σ1 ⊙ τ1] is done; [σ2 ⊙ τ2] may have more to do. *)
      revert i12 j12 ij12 p12 qi qj qij p st Hst.
      induction Hst2; intros.
      + dependent destruction Hst; dependent destruction p.
        eauto 30.
      + dependent destruction Hst; dependent destruction p.
        edestruct (IHHst2 _ _ _ _ _ _ _ (fccpos_left_r q))
          as (?&?&?&?&?&?&?&?&?&?&?&?&?); eauto 30.
      + dependent destruction p.
        edestruct (IHHst2 _ _ _ _ _ _ _ (fccpos_right_r q m))
          as (?&?&?&?&?&?&?&?&?&?&?&?&?); eauto 30.
      + dependent destruction Hst; dependent destruction p.
        edestruct (IHHst2 _ _ _ _ _ _ _ (fccpos_suspended_r q m u))
          as (?&?&?&?&?&?&?&?&?&?&?&?&?); eauto 30.
      + dependent destruction Hst; dependent destruction p.
        eauto 20.
      + dependent destruction Hst; dependent destruction p.
        edestruct (IHHst2 _ _ _ _ _ _ _ (fccpos_right_r q m))
          as (?&?&?&?&?&?&?&?&?&?&?&?&?); eauto 30.
      + dependent destruction p.
        edestruct (IHHst2 _ _ _ _ _ _ _ (fccpos_left_r q))
          as (?&?&?&?&?&?&?&?&?&?&?&?&?); eauto 30.
      + dependent destruction Hst; dependent destruction p.
        edestruct (IHHst2 _ _ _ _ _ _ _ fccpos_ready)
          as (?&?&?&?&?&?&?&?&?&?&?&?&?); eauto 30.
    - (* [σ1 ⊙ τ1] is ready for a question, but [σ2 ⊙ τ2] might go first. *)
      rename q into q1, s into s1, t into t1, w into st1.
      revert i12 j12 ij12 p12 qi qj qij p st Hst.
      induction Hst2; intros.
      + (* if they're done then there's no choice. *)
        dependent destruction Hst; dependent destruction p.
        edestruct (IHHst1 _ _ _ _ _ _ _ _ _ _ _ (fccpos_left_l q1))
          as (?&?&?&?&?&?&?&?&?&?&?&?&?); eauto 30.
      + (* if they can do a question then it could go either way *)
        dependent destruction Hst; dependent destruction p.
        * eapply (IHHst1 _ _ _ _ _ _ _ _ _ _ _ (fccpos_left_l q1)) in Hst
            as (?&?&?&?&?&?&?&?&?&?&?&?&?); eauto 30.
        * eapply (IHHst2 _ _ _ _ _ _ _ (fccpos_left_r q)) in Hst
            as (?&?&?&?&?&?&?&?&?&?&?&?&?); eauto 30.
      + (* for the remaining case we just replay whatever [σ2 ⊙ τ2] does *)
        dependent destruction p.
        eapply (IHHst2 _ _ _ _ _ _ _ (fccpos_right_r q m)) in Hst
          as (?&?&?&?&?&?&?&?&?&?&?&?&?); eauto 30.
      + dependent destruction Hst; dependent destruction p.
        eapply (IHHst2 _ _ _ _ _ _ _ (fccpos_suspended_r q m u)) in Hst
          as (?&?&?&?&?&?&?&?&?&?&?&?&?); eauto 30.
      + dependent destruction Hst; dependent destruction p.
        eauto 30.
      + dependent destruction Hst; dependent destruction p.
        eapply (IHHst2 _ _ _ _ _ _ _ (fccpos_right_r q m)) in Hst
          as (?&?&?&?&?&?&?&?&?&?&?&?&?); eauto 30.
      + dependent destruction p.
        eapply (IHHst2 _ _ _ _ _ _ _ (fccpos_left_r q)) in Hst
          as (?&?&?&?&?&?&?&?&?&?&?&?&?); eauto 30.
      + dependent destruction Hst; dependent destruction p.
        eapply (IHHst2 _ _ _ _ _ _ _ fccpos_ready) in Hst
          as (?&?&?&?&?&?&?&?&?&?&?&?&?); eauto 30.
    - (* now that [σ1 ⊙ τ1] is moving, we just replay what it's doing. *)
      dependent destruction p.
      eapply (IHHst1 _ _ _ _ _ _ _ _ _ _ _ (fccpos_right_l q m)) in Hst
        as (?&?&?&?&?&?&?&?&?&?&?&?&?); eauto 30.
    - dependent destruction Hst; dependent destruction p.
      eapply (IHHst1 _ _ _ _ _ _ _ _ _ _ _ (fccpos_suspended_l q m u)) in Hst
        as (?&?&?&?&?&?&?&?&?&?&?&?&?); eauto 30.
    - dependent destruction Hst; dependent destruction p.
      eauto 30.
    - dependent destruction Hst; dependent destruction p.
      eapply (IHHst1 _ _ _ _ _ _ _ _ _ _ _ (fccpos_right_l q m)) in Hst
        as (?&?&?&?&?&?&?&?&?&?&?&?&?); eauto 30.
    - dependent destruction p.
      eapply (IHHst1 _ _ _ _ _ _ _ _ _ _ _ (fccpos_left_l q)) in Hst
        as (?&?&?&?&?&?&?&?&?&?&?&?&?); eauto 30.
    - dependent destruction Hst; dependent destruction p.
      eapply (IHHst1 _ _ _ _ _ _ _ _ _ _ _ fccpos_ready) in Hst
        as (?&?&?&?&?&?&?&?&?&?&?&?&?); eauto 30.
  Qed.

  Lemma fcomp_compose_has {i1 i2 j1 j2 i12 j12 ij1 ij2 ij12 p1 p2 p12 qi qj qij} :
    @fccpos i1 i2 j1 j2 i12 j12 ij1 ij2 ij12 p1 p2 p12 qi qj qij ->
    forall s1 s2 t1 t2 s12 t12 st,
      fcomp_has qi s1 s2 s12 ->
      fcomp_has qj t1 t2 t12 ->
      comp_has qij s12 t12 st ->
      exists s1' s2' t1' t2' st1 st2,
        s1' [= s1 /\ s2' [= s2 /\ t1' [= t1 /\ t2' [= t2 /\
        comp_has p1 s1' t1' st1 /\
        comp_has p2 s2' t2' st2 /\
        fcomp_has p12 st1 st2 st.
  Proof.
    intros p s1 s2 t1 t2 s12 t12 st Hs12 Ht12 Hst. cbn.
    revert i1 i2 j1 j2 ij1 ij2 p1 p2 p12 qi qj p s1 s2 t1 t2 Hs12 Ht12. 
    induction Hst; intros.
    - dependent destruction Hs12; dependent destruction p.
      eauto 30.
    - (* incoming question *)
      dependent destruction Hs12; dependent destruction p.
      + edestruct (IHHst _ _ _ _ _ _ _ _ _ _ _ (fccpos_left_l q1))
          as (?&?&?&?&?&?&?&?&?&?&?&?&?); eauto 30.
      + edestruct (IHHst _ _ _ _ _ _ _ _ _ _ _ (fccpos_left_r q2))
          as (?&?&?&?&?&?&?&?&?&?&?&?&?); eauto 30.
    - (* internal question *)
      dependent destruction Hs12; dependent destruction Ht12; dependent destruction p.
      + edestruct (IHHst _ _ _ _ _ _ _ _ _ _ _ (fccpos_right_l q1 m1))
          as (?&?&?&?&?&?&?&?&?&?&?&?&?); eauto 30.
      + edestruct (IHHst _ _ _ _ _ _ _ _ _ _ _ (fccpos_right_r q2 m2))
          as (?&?&?&?&?&?&?&?&?&?&?&?&?); eauto 30.
    - (* outgoing question *)
      dependent destruction Ht12; dependent destruction p.
      + edestruct (IHHst _ _ _ _ _ _ _ _ _ _ _ (fccpos_suspended_l q0 q1 m1))
          as (?&?&?&?&?&?&?&?&?&?&?&?&?); eauto 30.
      + edestruct (IHHst _ _ _ _ _ _ _ _ _ _ _ (fccpos_suspended_r q0 q2 m2))
          as (?&?&?&?&?&?&?&?&?&?&?&?&?); eauto 30.
    - (* suspended *)
      dependent destruction Ht12; dependent destruction p; eauto 30.
    - (* environment answer *)
      simple inversion Ht12; clear Ht12; xsubst; intros Ht12;
      inversion H2; clear H2; xsubst;
      apply pcons_oa_inv in H6 as [? ?]; subst;
      dependent destruction p.
      + edestruct IHHst with (1 := fccpos_right_l q0 q1)
          as (?&?&?&?&?&?&?&?&?&?&?&?&?); eauto 30.
      + edestruct IHHst with (1 := fccpos_right_r q0 q2)
          as (?&?&?&?&?&?&?&?&?&?&?&?&?); eauto 30.
    - (* internal answer *)
      simple inversion Ht12; clear Ht12; xsubst; intros Ht12;
      inversion H2; clear H2; xsubst;
      apply pcons_pa_inv in H6 as [? ?]; xsubst;
      simple inversion Hs12; clear Hs12; xsubst; intros Hs12;
      inversion H2; clear H2; xsubst;
      apply pcons_oa_inv in H6 as [? ?]; xsubst;
      dependent destruction p.
      + edestruct IHHst with (1 := fccpos_left_l q0)
          as (?&?&?&?&?&?&?&?&?&?&?&?&?); eauto 30.
      + edestruct IHHst with (1 := fccpos_left_r q0)
          as (?&?&?&?&?&?&?&?&?&?&?&?&?); eauto 30.
    - (* component answer *)
      simple inversion Hs12; clear Hs12; xsubst; intros Hs12;
      inversion H2; clear H2; xsubst;
      apply pcons_pa_inv in H6 as [? ?]; xsubst;
      dependent destruction p;
      edestruct IHHst with (1 := fccpos_ready)
        as (?&?&?&?&?&?&?&?&?&?&?&?&?); eauto 30.
  Qed.

  Lemma fcomp_compose_when {i1 i2 j1 j2 i12 j12 ij1 ij2 ij12 p1 p2 p12 qi qj qij} :
    @fccpos i1 i2 j1 j2 i12 j12 ij1 ij2 ij12 p1 p2 p12 qi qj qij ->
    forall σ1 σ2 τ1 τ2,
      fcomp_when p12 (compose_when p1 σ1 τ1) (compose_when p2 σ2 τ2) =
      compose_when qij (fcomp_when qi σ1 σ2) (fcomp_when qj τ1 τ2).
  Proof.
    intros p σ1 σ2 τ1 τ2.
    apply antisymmetry; cbn.
    - intros s (st1 &st2 &(s1 &t1 &Hs1 &Ht1 &Hst1) &(s2 &t2 &Hs2 &Ht2 &Hst2) &Hs).
      edestruct (compose_fcomp_has p s1 s2 t1 t2 st1 st2)
        as (s1'&s2'&t1'&t2'&?&?&?&?& s12 & t12 & Hs12 & Ht12 & H');
        eauto 100 using Downset.closed.
    - intros s (s12 &t12 &(s1 &s2 &Hs1 &Hs2 &Hs12) &(t1 &t2 &Ht1 &Ht2 &Ht12) &Hs).
      edestruct (fcomp_compose_has p s1 s2 t1 t2)
        as (s1'&s2'&t1'&t2'&?&?&?&?& st1 & st2 & Hst1 & Hst2 & H');
        eauto 100 using Downset.closed.
  Qed.

  Lemma fcomp_compose (σ1: F1->>G1) (σ2: F2->>G2) (τ1: E1->>F1) (τ2: E2->>F2) :
    (σ1 ⊙ τ1) + (σ2 ⊙ τ2) = (σ1 + σ2) ⊙ (τ1 + τ2).
  Proof.
    apply fcomp_compose_when.
    constructor.
  Qed.
End COMPOSE_FCOMP.

(** *** Symmetric monoidal structure *)

(** **** Left unitor properties *)

Global Instance flu_iso {E} :
  Isomorphism (@flu E) (@flur E).
Proof.
  split.
  - constructor.
    rewrite <- emor_strat_ecomp.
    rewrite flu_flur.
    reflexivity.
  - constructor.
    rewrite <- emor_strat_ecomp.
    erewrite flur_flu.
    reflexivity.
Qed.

(** **** Right unitor properties *)

Global Instance fru_iso {E} :
  Isomorphism (@fru E) (@frur E).
Proof.
  split.
  - constructor.
    rewrite <- emor_strat_ecomp.
    rewrite fru_frur.
    reflexivity.
  - constructor.
    rewrite <- emor_strat_ecomp.
    erewrite frur_fru.
    reflexivity.
Qed.

(** **** Associator properties *)

Global Instance fassoc_iso {E F G} :
  Isomorphism (@fassoc E F G) (@fassocr E F G).
Proof.
  split.
  - constructor.
    rewrite <- emor_strat_ecomp.
    rewrite fassoc_fassocr.
    reflexivity.
  - constructor.
    rewrite <- emor_strat_ecomp.
    rewrite fassocr_fassoc.
    reflexivity.
Qed.

(** **** Braiding is its own inverse *)

Global Instance fswap_iso {E F} :
  Isomorphism (@fswap E F) (@fswap F E).
Proof.
  split; constructor;
    rewrite <- emor_strat_ecomp, fswap_fswap;
    reflexivity.
Qed.

(** **** Duplication and projections *)

Global Instance ffst_fdelta {E : esig} :
  Retraction (F:=E) ffst fdup.
Proof.
  constructor.
  rewrite <- emor_strat_ecomp, ffst_fdup.
  reflexivity.
Qed.

Global Instance fsnd_fdelta {E : esig} :
  Retraction (F:=E) fsnd fdup.
Proof.
  constructor.
  rewrite <- emor_strat_ecomp, fsnd_fdup.
  reflexivity.
Qed.


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
    poset_carrier (downset rcp_poset).

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

Infix "<=>" := conv (at level 99, right associativity).

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

Declare Scope rsq_scope.
Delimit Scope rsq_scope with rsq.
Bind Scope rsq_scope with rsq.

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

  Lemma rsq_comp σ1 τ1 σ2 τ2:
    rsq S T σ1 σ2 ->
    rsq R S τ1 τ2 ->
    rsq R T (σ1 ⊙ τ1) (σ2 ⊙ τ2).
  Proof.
    apply rsq_comp_when; auto.
  Qed.
End RSQ_COMP.

Infix "⊙" := (rsq_comp _ _ _ _) : rsq_scope.

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

Infix ";;" := (rsq_vcomp _ _ _ _) : rsq_scope.

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

(* XXX should prove associativity as well? *)

(** ** Signature homomorphisms *)

(** Signature homomorphisms embed into refinement conventions as well
  as strategies. This will again be useful to define the monoidal
  structure associated with flat composition for refinement conventions. *)

Section EMOR_RC.
  Context {E1 E2} (f : emor E1 E2).
  Obligation Tactic := cbn.

  (** *** Definition *)

  Inductive emor_rc_has : rcp E1 E2 -> Prop :=
    | emor_rc_allow m :
        emor_rc_has (rcp_allow (operator (f m)) m)
    | emor_rc_forbid m n1 n2 :
        operand (f m) n1 <> n2 ->
        emor_rc_has (rcp_forbid (operator (f m)) m n1 n2)
    | emor_rc_cont m n1 n2 k :
        (operand (f m) n1 = n2 -> emor_rc_has k) ->
        emor_rc_has (rcp_cont (operator (f m)) m n1 n2 k).

  Hint Constructors emor_rc_has.

  Program Definition emor_rc : conv E1 E2 :=
    {| Downset.has := emor_rc_has |}.
  Next Obligation.
    intros s t Hst Ht. revert s Hst.
    induction Ht; intros; dependent destruction Hst; auto.
    constructor. tauto.
  Qed.

  (** *** Useful lemmas *)

  (** Behavior wrt [rcnext] *)

  Lemma rcnext_emor q r :
    rcnext (operator (f q)) q r (operand (f q) r) emor_rc = emor_rc.
  Proof.
    apply antisymmetry; cbn.
    - intros s Hs.
      dependent destruction Hs.
      auto.
    - intros s Hs.
      constructor.
      auto.
  Qed.

  (** The resulting refinement convention is in fact a companion of
    the embedded strategy (see §5.5). *)

  Hint Constructors rsp emor_has : core.
  Hint Unfold Downset.has : core.

  Variant esepos : forall {i j}, epos f i -> epos eid j -> rspos i j -> Type :=
    | ese_ready :
        esepos eready eready rs_ready
    | ese_suspended (q : E2) :
        esepos (esuspended q) (esuspended q)
               (rs_suspended q q (operator (f q)) q).

  Lemma emor_strat_elim_when {i j pi pj pij} (p : @esepos i j pi pj pij) :
    rsq_when emor_rc vid pij (emor_when f pi) (emor_when eid pj).
  Proof.
    red. cbn. intros s Hs. revert j pj pij p.
    induction Hs; intros.
    - dependent destruction p.
      econstructor; cbn; auto.
    - dependent destruction p.
      econstructor; cbn; eauto. intros _ [ ].
      econstructor; cbn; eauto. setoid_rewrite (emor_next_question eid q).
      apply IHHs with (1 := ese_suspended q).
    - dependent destruction p.
      econstructor; cbn; eauto. constructor.
    - dependent destruction p.
      econstructor; cbn; eauto. { constructor. }
      intros r' Hr'.
      assert (r' = operand (f q) r).
      { destruct (classic (r' = operand (f q) r)); auto.
        elim Hr'. constructor. auto. } subst.
      econstructor; cbn; eauto.
      { intros [_ H]. apply H. reflexivity. }
      setoid_rewrite (emor_next_answer eid q (operand (f q) r)).
      rewrite rcnext_emor, rcnext_vid.
      apply IHHs with (1 := ese_ready).
  Qed.

  Lemma emor_strat_elim :
    rsq emor_rc vid f (id _).
  Proof.
    apply (emor_strat_elim_when ese_ready).
  Qed.

  Variant esipos : forall {i j}, epos eid i -> epos f j -> rspos i j -> Type :=
    | esi_ready :
        esipos eready eready rs_ready
    | esi_suspended (q : E2) :
        esipos (esuspended (operator (f q))) (esuspended q)
               (rs_suspended (operator (f q)) q (operator (f q)) (operator (f q))).

  Lemma emor_strat_intro_when {i j pi pj pij} (p : @esipos i j pi pj pij) :
    rsq_when vid emor_rc pij (emor_when (@eid E1) pi) (emor_when f pj).
  Proof.
    red. cbn. intros s Hs. revert j pj pij p.
    induction Hs; intros.
    - dependent destruction p.
      econstructor; cbn; eauto.
    - dependent destruction p.
      econstructor; cbn; eauto.
      intros m Hm. dependent destruction Hm.
      econstructor; cbn; eauto.
      setoid_rewrite (emor_next_question f m).
      apply IHHs with (1 := esi_suspended m).
    - dependent destruction p.
      econstructor; cbn; eauto.
    - dependent destruction p.
      econstructor; cbn; eauto.
      intros n Hn.
      destruct (classic (r ~= n)); try tauto. subst. clear Hn.
      econstructor; cbn; eauto.
      { cbn. intros H. dependent destruction H. apply H. reflexivity. }
      rewrite rcnext_vid, rcnext_emor.
      setoid_rewrite emor_next_answer.
      apply IHHs with (1 := esi_ready).
  Qed.

  Lemma emor_strat_intro :
    rsq vid emor_rc (id _) f.
  Proof.
    apply (emor_strat_intro_when esi_ready).
  Qed.
End EMOR_RC.

(** *** Functoriality *)

Lemma emor_rc_id {E} :
  emor_rc (@eid E) = vid.
Proof.
  unfold eid.
  apply antisymmetry; cbn; intros s Hs.
  - induction Hs; cbn in *; auto using JMeq_eq.
  - induction s; cbn in *; firstorder subst.
    + apply (emor_rc_allow eid).
    + apply (emor_rc_forbid eid); cbn; intro; subst; auto.
    + apply (emor_rc_cont eid); cbn; intro; subst; auto.
Qed.

Lemma emor_rc_ecomp {E F G} (g : emor F G) (f : emor E F) :
  emor_rc (g ∘ f) = vcomp (emor_rc f) (emor_rc g).
Proof.
  apply antisymmetry.
  - intros s. cbn. induction 1; cbn.
    + exists (operator (g m)). split; constructor.
    + exists (operator (g m)).
      split; [constructor | ].
      split; [constructor | ].
      intros n. cbn in *. 
      destruct (classic (operand (f (operator (g m))) n1 = n));
        eauto using emor_rc_forbid.
      destruct (classic (operand (g m) n = n2));
        eauto using emor_rc_forbid.
      congruence.
    + exists (operator (g m)).
      split; [constructor | ].
      split; [constructor | ].
      intros n. cbn in *. 
      destruct (classic (operand (f (operator (g m))) n1 = n));
        eauto using emor_rc_forbid.
      destruct (classic (operand (g m) n = n2));
        eauto using emor_rc_forbid.
      right. right. subst.
      rewrite ?rcnext_emor. eauto.
  - intros s. cbn. induction s; cbn.
    + intros (mi & Hm1i & Hmi2).
      dependent destruction Hm1i.
      dependent destruction Hmi2.
      apply (emor_rc_allow (g ∘ f)).
    + intros (mi & Hm1i & Hmi2 & Hn).
      dependent destruction Hm1i.
      dependent destruction Hmi2.
      apply (emor_rc_forbid (g ∘ f)).
      destruct (Hn (operand (f (operator (g m2))) n1)) as [Hn' | Hn'];
        dependent destruction Hn'; cbn; congruence.
    + intros (mi & Hm1i & Hmi2 & Hn).
      dependent destruction Hm1i.
      dependent destruction Hmi2.
      apply (emor_rc_cont (g ∘ f)). intro. subst.
      destruct (Hn (operand (f (operator (g m2))) n1)) as [Hn' | [Hn' | Hn']];
        try (dependent destruction Hn'; cbn; congruence).
      cbn in Hn'. rewrite ?rcnext_emor in Hn'. auto.
Qed.

(** ** §4.5 Flat Composition *)

(** *** Definition 4.8 (Flat composition of refinement conventions) *)

Section FCOMP_RC.
  Context {E1 E2 F1 F2 : esig}.
  Obligation Tactic := cbn.

  Fixpoint fcomp_rc_has (R S : conv _ _) (s: rcp (E1 + F1) (E2 + F2)) : Prop :=
    match s with
      | rcp_allow (inl q1) (inl q2) => Downset.has R (rcp_allow q1 q2)
      | rcp_allow (inr q1) (inr q2) => Downset.has S (rcp_allow q1 q2)
      | rcp_allow _ _ => False
      | rcp_forbid (inl q1) (inl q2) r1 r2 => Downset.has R (rcp_forbid q1 q2 r1 r2)
      | rcp_forbid (inr q1) (inr q2) r1 r2 => Downset.has S (rcp_forbid q1 q2 r1 r2)
      | rcp_forbid _ _ _ _ => False
      | rcp_cont (inl q1) (inl q2) r1 r2 k =>
          Downset.has R (rcp_forbid q1 q2 r1 r2) \/
          Downset.has R (rcp_allow q1 q2) /\ fcomp_rc_has (rcnext q1 q2 r1 r2 R) S k
      | rcp_cont (inr q1) (inr q2) r1 r2 k =>
          Downset.has S (rcp_forbid q1 q2 r1 r2) \/
          Downset.has S (rcp_allow q1 q2) /\ fcomp_rc_has R (rcnext q1 q2 r1 r2 S) k
      | rcp_cont _ _ _ _ _ => False
    end.

  Program Definition fcomp_rc R S : conv (E1 + F1) (E2 + F2) :=
    {| Downset.has := fcomp_rc_has R S |}.
  Next Obligation.
    intros R S s t Hst Ht. revert R S s Ht Hst.
    induction t as [[q1|q1] [q2|q2] |
                    [q1|q1] [q2|q2] r1 r2 |
                    [q1|q1] [q2|q2] r1 r2 k]; intros; cbn in *;
    dependent destruction Hst; cbn; eauto.
    - destruct Ht as [ | [? ?]]; eauto.
    - destruct Ht as [ | [? ?]]; eauto.
    - destruct Ht as [ | [? ?]]; eauto.
    - destruct Ht as [ | [? ?]]; eauto.
  Qed.

  Lemma rcnext_fcomp_l q1 q2 r1 r2 R S :
    Downset.has R (rcp_allow q1 q2) ->
    ~ Downset.has R (rcp_forbid q1 q2 r1 r2) ->
    rcnext (inl q1) (inl q2) r1 r2 (fcomp_rc R S) = fcomp_rc (rcnext q1 q2 r1 r2 R) S.
  Proof.
    intros Hq Hr.
    apply Downset.has_eq_ext. cbn.
    firstorder.
  Qed.

  Lemma rcnext_fcomp_r q1 q2 r1 r2 R S :
    Downset.has S (rcp_allow q1 q2) ->
    ~ Downset.has S (rcp_forbid q1 q2 r1 r2) ->
    rcnext (inr q1) (inr q2) r1 r2 (fcomp_rc R S) = fcomp_rc R (rcnext q1 q2 r1 r2 S).
  Proof.
    intros Hq Hr.
    apply Downset.has_eq_ext. cbn.
    firstorder.
  Qed.

  Lemma fcomp_sup_l {I} (R : I -> _) S :
    inhabited I ->
    fcomp_rc (lsup R) S = sup i, fcomp_rc (R i) S.
  Proof.
    assert (HI_ex: forall I P, inhabited I -> (exists i:I, P) <-> P)
      by (split; auto; firstorder).
    intros HI. apply Downset.has_eq_ext. intros s. revert I R S HI.
    induction s as [[q1|q1] [q2|q2] |
                    [q1|q1] [q2|q2] r1 r2 |
                    [q1|q1] [q2|q2] r1 r2 k];
    try (cbn; intros; rewrite ?HI_ex by auto; tauto).
    - intros I R S HI. cbn -[lsup] in *. rewrite rcnext_sup.
      split.
      + intros [[ir Hr] | [[iq Hq] Hnext]]; try solve [cbn; eauto].
        unfold fsup in Hnext. rewrite IHk in Hnext by eauto.
        destruct Hnext as [[i Hi] Hk]. cbn in *. eauto.
      + cbn -[fsup]. intros [i [Hr | [Hq Hk]]]; eauto. right. split; eauto.
        unfold fsup. rewrite IHk by eauto. cbn.
        exists (exist _ i Hq). cbn. assumption.
    - intros I R S HI. cbn -[lsup] in *.
      rewrite IHk by auto. cbn. firstorder.
  Qed.

  Lemma fcomp_sup_r {I} R (S : I -> _) :
    inhabited I ->
    fcomp_rc R (lsup S) = sup i, fcomp_rc R (S i).
  Proof.
    assert (HI_ex: forall I P, inhabited I -> (exists i:I, P) <-> P)
      by (split; auto; firstorder).
    intros HI. apply Downset.has_eq_ext. intros s. revert I R S HI.
    induction s as [[q1|q1] [q2|q2] |
                    [q1|q1] [q2|q2] r1 r2 |
                    [q1|q1] [q2|q2] r1 r2 k];
    try (cbn; intros; rewrite ?HI_ex by auto; tauto).
    - intros I R S HI. cbn -[lsup] in *.
      rewrite IHk by auto. cbn. firstorder.
    - intros I R S HI. cbn -[lsup] in *. rewrite rcnext_sup.
      split.
      + intros [[ir Hr] | [[iq Hq] Hnext]]; try solve [cbn; eauto].
        unfold fsup in Hnext. rewrite IHk in Hnext by eauto.
        destruct Hnext as [[i Hi] Hk]. cbn in *. eauto.
      + cbn -[fsup]. intros [i [Hr | [Hq Hk]]]; eauto. right. split; eauto.
        unfold fsup. rewrite IHk by eauto. cbn.
        exists (exist _ i Hq). cbn. assumption.
  Qed.

  Lemma fcomp_inf_l {I} (R : I -> _) S :
    inhabited I ->
    fcomp_rc (linf R) S = inf i, fcomp_rc (R i) S.
  Proof.
    assert (HI_all: forall I (P:Prop), inhabited I -> (forall i:I, P) <-> P)
      by (split; auto; firstorder).
    intros HI. apply Downset.has_eq_ext. intros s. revert I R S HI.
    induction s as [[q1|q1] [q2|q2] |
                    [q1|q1] [q2|q2] r1 r2 |
                    [q1|q1] [q2|q2] r1 r2 k];
    try (cbn; intros; rewrite ?HI_all by auto; tauto).
    - intros I R S HI. cbn -[linf] in IHk |- *.
      rewrite rcnext_inf. unfold finf.
      destruct (classic (Downset.has (inf j, R j) (rcp_forbid q1 q2 r1 r2))).
      1: { split; auto. }
      rewrite IHk.
      2: { apply not_all_ex_not in H as [? ?]. eauto. }
      cbn. split.
      + intros [? | (Hq & Hr)]; try tauto. intros i.
        destruct (classic (Downset.has (R i) (rcp_forbid q1 q2 r1 r2))); auto. right.
        specialize (Hr (exist _ i H0)); auto.
      + intros Hr. right. split.
        * intros i. specialize (Hr i) as [? | [? _]]; eauto.
        * intros [i Hi]. cbn. destruct (Hr i) as [? | [? ?]]; tauto.
    - intros I R S HI. cbn -[linf] in IHk |- *. rewrite IHk by auto.
      clear - HI. cbn. split.
      + intros [Hr | (Hq & Hk)]; auto.
      + intros H.
        destruct (classic (Downset.has S (rcp_forbid q1 q2 r1 r2))); auto. right.
        destruct HI as [i0]. destruct (H i0) as [ | [? ?]]; try tauto. split; auto.
        intros i. specialize (H i) as [? | [? ?]]; tauto.
  Qed.

  Lemma fcomp_inf_r {I} R (S : I -> _) :
    inhabited I ->
    fcomp_rc R (linf S) = inf i, fcomp_rc R (S i).
  Proof.
    assert (HI_all: forall I (P:Prop), inhabited I -> (forall i:I, P) <-> P)
      by (split; auto; firstorder).
    intros HI. apply Downset.has_eq_ext. intros s. revert I R S HI.
    induction s as [[q1|q1] [q2|q2] |
                    [q1|q1] [q2|q2] r1 r2 |
                    [q1|q1] [q2|q2] r1 r2 k];
    try (cbn; intros; rewrite ?HI_all by auto; tauto).
    - intros I R S HI. cbn -[linf] in IHk |- *. rewrite IHk by auto.
      clear - HI. cbn. split.
      + intros [Hr | (Hq & Hk)]; auto.
      + intros H.
        destruct (classic (Downset.has R (rcp_forbid q1 q2 r1 r2))); auto. right.
        destruct HI as [i0]. destruct (H i0) as [ | [? ?]]; try tauto. split; auto.
        intros i. specialize (H i) as [? | [? ?]]; tauto.
    - intros I R S HI. cbn -[linf] in IHk |- *.
      rewrite rcnext_inf. unfold finf.
      destruct (classic (Downset.has (inf j, S j) (rcp_forbid q1 q2 r1 r2))).
      1: { split; auto. }
      rewrite IHk.
      2: { apply not_all_ex_not in H as [? ?]. eauto. }
      cbn. split.
      + intros [? | (Hq & Hr)]; try tauto. intros i.
        destruct (classic (Downset.has (S i) (rcp_forbid q1 q2 r1 r2))); auto. right.
        specialize (Hr (exist _ i H0)); auto.
      + intros Hr. right. split.
        * intros i. specialize (Hr i) as [? | [? _]]; eauto.
        * intros [i Hi]. cbn. destruct (Hr i) as [? | [? ?]]; tauto.
  Qed.
End FCOMP_RC.

Infix "+" := fcomp_rc : conv_scope.

(** *** Theorem 4.9 (Flat composition properties) *)

(** **** Functoriality of ⊕ *)

Section FCOMP_VID.
  Context {E F : esig}.

  Lemma fcomp_vid :
    (@vid E) + (@vid F) = @vid (E + F).
  Proof.
    apply Downset.has_eq_ext. intros s.
    induction s as [[q1|q1] [q2|q2] |
                    [q1|q1] [q2|q2] r1 r2 |
                    [q1|q1] [q2|q2] r1 r2 k]; cbn in *;
    try firstorder congruence.
    - firstorder; try congruence.
      + subst. dependent destruction H2.
        rewrite rcnext_vid in H3. auto.
      + dependent destruction H1.
        destruct (classic (r1 ~= r2)); auto.
        dependent destruction H1.
        rewrite rcnext_vid. auto.
    - firstorder; try congruence.
      + subst. dependent destruction H2.
        rewrite rcnext_vid in H3. auto.
      + dependent destruction H1.
        destruct (classic (r1 ~= r2)); auto.
        dependent destruction H1.
        rewrite rcnext_vid. auto.
  Qed.
End FCOMP_VID.

Section FCOMP_VCOMP.
  Context {E1 E2 F1 F2 G1 G2 : esig}.

  Lemma fcomp_vcomp (R1: conv E1 F1) (R2: conv E2 F2) (S1: conv F1 G1) (S2: conv F2 G2):
    (R1 ;; S1) + (R2 ;; S2) = (R1 + R2) ;; (S1 + S2).
  Proof.
    assert (Hex: forall A B (P: A+B -> Prop),
               ex P <-> (exists a, P (inl a)) \/ (exists b, P (inr b))).
    {
      firstorder. destruct x; eauto.
    }
    apply Downset.has_eq_ext. intro s. revert R1 R2 S1 S2.
    induction s as [[q1|q1] [q2|q2] | [q1|q1] [q2|q2] r1 r2 | [q1|q1] [q2|q2] r1 r2 k];
    intros; [ cbn in *; rewrite Hex; firstorder .. | | | | ].
    - destruct (classic (inhabited F1)) as [HF1 | ?].
      2: {
        cbn in *; rewrite Hex. split.
        + intros [[? ?] | [[? ?] ?]]; elim H; eauto.
        + intros [[? ?] | (_ & [ ] & _)]; elim H; eauto.
      }
      rewrite (vcomp_expand R1 S1), (vcomp_expand (R1 + R2) (S1 + S2)).
      rewrite fcomp_sup_l by auto. cbn -[linf fcomp_rc].
      setoid_rewrite fcomp_inf_l; auto using None.
      rewrite Hex. cbn in *. split.
      + intros (qi & Hr). left. exists qi.
        intros ri. specialize (Hr ri).
        destruct ri as [ri | ].
        2: { destruct Hr as [(?&?&?)|[[? ?] ?]]; repeat (split; auto); discriminate. }
        destruct Hr as [(Hq1 & Hq2 & Hr) | ((Hq1 & Hq2) & Hr)].
        * repeat (split; auto). intros. edestruct Hr; eauto.
        * repeat (split; auto). intros. symmetry in H. dependent destruction H.
          destruct (classic (Downset.has R1 (rcp_forbid q1 qi r1 ri))); auto.
          destruct (classic (Downset.has S1 (rcp_forbid qi q2 ri r2))); auto.
          right. right.
          rewrite !rcnext_vcomp_at in Hr by auto.
          rewrite !rcnext_fcomp_l by auto.
          apply IHk in Hr. auto.
      + intros [(qi & Hr) | (? & X)]. 2: destruct (X None) as [[ ] _].
        exists qi. intros ri. specialize (Hr ri) as (Hq1 & Hq2 & Hr).
        destruct ri as [ri | ]. 2: { left. repeat (split; auto). discriminate. }
        specialize (Hr _ eq_refl).
        destruct (classic (Downset.has R1 (rcp_forbid q1 qi r1 ri)));
          try solve [left; repeat (split; auto); inversion 1; subst; eauto].
        destruct (classic (Downset.has S1 (rcp_forbid qi q2 ri r2)));
          try solve [left; repeat (split; auto); inversion 1; subst; eauto].
        right. split; auto.
        destruct Hr as [? | Hr]; try tauto.
        destruct Hr as [? | Hr]; try tauto.
        rewrite rcnext_vcomp_at by auto. apply IHk.
        rewrite !rcnext_fcomp_l in Hr; auto.
    - cbn. rewrite ?Hex. split; try tauto.
      intros [(_ & _ & [ ] & _) | (_ & [ ] & _)].
    - cbn. rewrite ?Hex. split; try tauto.
      intros [(_ & [ ] & _) | (_ & _ & [ ] & _)].
    - destruct (classic (inhabited F2)) as [HF2 | ?].
      2: {
        cbn in *; rewrite Hex. split.
        + intros [[? ?] | [[? ?] ?]]; elim H; eauto.
        + intros [(_ & [ ] & _) | [? ?]]; elim H; eauto.
      }
      rewrite (vcomp_expand R2 S2), (vcomp_expand (R1 + R2) (S1 + S2)).
      rewrite fcomp_sup_r by auto. cbn -[linf fcomp_rc].
      setoid_rewrite fcomp_inf_r; auto using None.
      rewrite Hex. cbn in *. split.
      + intros (qi & Hr). right. exists qi.
        intros ri. specialize (Hr ri).
        destruct ri as [ri | ].
        2: { destruct Hr as [(?&?&?)|[[? ?] ?]]; repeat (split; auto); discriminate. }
        destruct Hr as [(Hq1 & Hq2 & Hr) | ((Hq1 & Hq2) & Hr)].
        * repeat (split; auto). intros. edestruct Hr; eauto.
        * repeat (split; auto). intros. symmetry in H. dependent destruction H.
          destruct (classic (Downset.has R2 (rcp_forbid q1 qi r1 ri))); auto.
          destruct (classic (Downset.has S2 (rcp_forbid qi q2 ri r2))); auto.
          right. right.
          rewrite !rcnext_vcomp_at in Hr by auto.
          rewrite !rcnext_fcomp_r by auto.
          apply IHk in Hr. auto.
      + intros [(? & X) | (qi & Hr)]. 1: destruct (X None) as [[ ] _].
        exists qi. intros ri. specialize (Hr ri) as (Hq1 & Hq2 & Hr).
        destruct ri as [ri | ]. 2: { left. repeat (split; auto). discriminate. }
        specialize (Hr _ eq_refl).
        destruct (classic (Downset.has R2 (rcp_forbid q1 qi r1 ri)));
          try solve [left; repeat (split; auto); inversion 1; subst; eauto].
        destruct (classic (Downset.has S2 (rcp_forbid qi q2 ri r2)));
          try solve [left; repeat (split; auto); inversion 1; subst; eauto].
        right. split; auto.
        destruct Hr as [? | Hr]; try tauto.
        destruct Hr as [? | Hr]; try tauto.
        rewrite rcnext_vcomp_at by auto. apply IHk.
        rewrite !rcnext_fcomp_r in Hr; auto.
  Qed.
End FCOMP_VCOMP.

(** **** Flat composition of refinement squares *)

Section FCOMP_RSQ.
  Context {E1 E2 F1 F2 E1' E2' F1' F2' : esig}.

  Variant fcrspos : forall {i1 i2 i j1 j2 j}, rspos i1 j1 -> rspos i2 j2 ->
                                              fcpos i1 i2 i -> fcpos j1 j2 j ->
                                              rspos i j -> Type :=
    | fcrs_ready :
        fcrspos rs_ready rs_ready fcpos_ready fcpos_ready rs_ready
    | fcrs_running_l (q1 : F1) (q2 : F1') :
        fcrspos (rs_running q1 q2) rs_ready
                (fcpos_running_l q1) (fcpos_running_l q2)
                (rs_running (inl q1) (inl q2))
    | fcrs_running_r (q1 : F2) (q2 : F2') :
        fcrspos rs_ready (rs_running q1 q2)
                (fcpos_running_r q1) (fcpos_running_r q2)
                (rs_running (inr q1) (inr q2))
    | fcrs_suspended_l (q1 : F1) (q2 : F1') (m1 : E1) (m2 : E1') :
        fcrspos (rs_suspended q1 q2 m1 m2) rs_ready
                (fcpos_suspended_l q1 m1) (fcpos_suspended_l q2 m2)
                (rs_suspended (inl q1) (inl q2) (inl m1) (inl m2))
    | fcrs_suspended_r (q1 : F2) (q2 : F2') (m1 : E2) (m2 : E2') :
        fcrspos rs_ready (rs_suspended q1 q2 m1 m2)
                (fcpos_suspended_r q1 m1) (fcpos_suspended_r q2 m2)
                (rs_suspended (inr q1) (inr q2) (inr m1) (inr m2)).

  Hint Constructors rsp fcomp_has fcrspos.

  Lemma fcomp_rsp {i1 i2 i j1 j2 j p1 p2 pi pj pij} :
    forall p : @fcrspos i1 i2 i j1 j2 j p1 p2 pi pj pij,
    forall R1 S1 s1 τ1, rsp R1 S1 p1 s1 τ1 ->
    forall R2 S2 s2 τ2, rsp R2 S2 p2 s2 τ2 ->
    forall s, fcomp_has pi s1 s2 s ->
    match p with
      | fcrs_running_l q1 q2 =>
          Downset.has S1 (rcp_allow q1 q2)
      | fcrs_running_r q1 q2 =>
          Downset.has S2 (rcp_allow q1 q2)
      | fcrs_suspended_l q1 q2 m1 m2 =>
          Downset.has S1 (rcp_allow q1 q2) /\
          Downset.has R1 (rcp_allow m1 m2)
      | fcrs_suspended_r q1 q2 m1 m2 =>
          Downset.has S2 (rcp_allow q1 q2) /\
          Downset.has R2 (rcp_allow m1 m2)
      | _ => True
    end ->
    rsp (R1 + R2) (S1 + S2) pij s (fcomp_when pj τ1 τ2).
  Proof.
    intros p R1 S1 s1 τ1 H1. revert i2 i j2 j p2 pi pj pij p.
    induction H1; intros i2 i j2 j p2 pi pj pij p R2 S2 s2 τ2 H2.
    - (* s1 terminated when ready, need to unroll s2 *)
      revert i j pi pj pij p.
      induction H2; intros i j pi pj pij p s12 Hs12.
      + (* s2 ready *)
        dependent destruction Hs12.
        dependent destruction p.
        constructor; cbn; eauto 10.
      + (* environment question for s2 *)
        dependent destruction Hs12.
        dependent destruction p.
        constructor; cbn; eauto.
        intros [q2 | q2] Hq; cbn; try tauto.
        rewrite fcomp_next_oq_r; eauto.
        apply H2 with (p := fcrs_running_r _ _); eauto.
      + (* component question of s2 *)
        dependent destruction Hs12.
        dependent destruction p; intros.
        apply (rsp_pq _ _ _ _ (inr m1) (inr m2)); cbn; auto.
        rewrite fcomp_next_pq_r; eauto.
        apply IHrsp with (p := fcrs_suspended_r q1 q2 m1 m2); eauto.
      + (* suspended *)
        dependent destruction Hs12.
        dependent destruction p.
        constructor; cbn; eauto.
      + (* environment answer in s2 *)
        dependent destruction Hs12.
        dependent destruction p. intros [Hq Hm].
        constructor; cbn; eauto.
        intros n2 Hn.
        rewrite rcnext_fcomp_r; auto.
        rewrite fcomp_next_oa_r.
        apply H2 with (p := fcrs_running_r q1 q2); eauto.
      + (* component answer in s2 *)
        dependent destruction Hs12.
        dependent destruction p. intros.
        econstructor; cbn; eauto.
        rewrite rcnext_fcomp_r; auto.
        rewrite fcomp_next_pa_r.
        apply IHrsp with (p := fcrs_ready); eauto.
    - (* incoming question in s1, could still do s2 first *)
      revert i j pi pj pij p.
      induction H2; intros i j pi pj pij p s12 Hs12.
      + (* s2 is nil, there's no choice *)
        dependent destruction Hs12.
        dependent destruction p. intros [ ].
        constructor; cbn; eauto 10.
        intros [q2 | q2] Hq; try tauto.
        rewrite fcomp_next_oq_l.
        eapply H1 with (p := fcrs_running_l q1 q2); eauto.
      + (* environment question for s2, could go either way *)
        dependent destruction Hs12;
        dependent destruction p; intros [ ];
        constructor; cbn; eauto;
        intros [q2 | q2] Hq; try tauto.
        * rewrite fcomp_next_oq_l.
          eapply H1 with (s2 := oq q0 :: s0) (p := fcrs_running_l _ _); eauto.
        * rewrite fcomp_next_oq_r.
          eapply H4 with (p := fcrs_running_r _ _); eauto.
      + (* component question of s2 *)
        dependent destruction Hs12.
        dependent destruction p; intros.
        apply (rsp_pq _ _ _ _ (inr m1) (inr m2)); cbn; auto.
        rewrite fcomp_next_pq_r; eauto.
        apply IHrsp with (p := fcrs_suspended_r _ _ m1 m2); eauto.
      + (* suspended *)
        dependent destruction Hs12.
        dependent destruction p.
        constructor; cbn; eauto.
      + (* environment answer in s2 *)
        dependent destruction Hs12.
        dependent destruction p. intros [Hq Hm].
        constructor; cbn; eauto.
        intros n2 Hn.
        rewrite rcnext_fcomp_r; auto.
        rewrite fcomp_next_oa_r.
        apply H4 with (p := fcrs_running_r _ _); eauto.
      + (* component answer in s2 *)
        dependent destruction Hs12.
        dependent destruction p. intros.
        econstructor; cbn; eauto.
        rewrite rcnext_fcomp_r; auto.
        rewrite fcomp_next_pa_r.
        apply IHrsp with (p := fcrs_ready); eauto.
    - (* outgoing question in s1 *)
      intros s12 Hs12. dependent destruction Hs12.
      dependent destruction p. intros.
      eapply rsp_pq with (inl m2); eauto.
      rewrite fcomp_next_pq_l.
      eapply IHrsp with (p := fcrs_suspended_l q1 q2 m1 m2); eauto.
    - (* suspended in s1 *)
      intros s12 Hs12. dependent destruction Hs12.
      dependent destruction p. intros [ ].
      dependent destruction H2; constructor; cbn; eauto 10.
    - (* environment answer into s1 *)
      intros s12 Hs12. dependent destruction Hs12.
      dependent destruction p. intros [ ].
      constructor; cbn; eauto.
      + dependent destruction H2; eauto.
      + intros n2 Hn.
        rewrite rcnext_fcomp_l; auto.
        rewrite fcomp_next_oa_l.
        eapply H1 with (p := fcrs_running_l _ _); eauto.
    - (* component answer in s1 *)
      intros s12 Hs12. dependent destruction Hs12.
      dependent destruction p. intro.
      econstructor; cbn; eauto.
      rewrite rcnext_fcomp_l; auto.
      rewrite fcomp_next_pa_l.
      eapply IHrsp with (p := fcrs_ready); eauto.
  Qed.

  Lemma fcomp_rsq :
    forall (R1 : conv E1 E1') (S1 : conv F1 F1') (σ1 : E1 ->> F1) (τ1 : E1' ->> F1')
           (R2 : conv E2 E2') (S2 : conv F2 F2') (σ2 : E2 ->> F2) (τ2 : E2' ->> F2'),
      rsq R1 S1 σ1 τ1 ->
      rsq R2 S2 σ2 τ2 ->
      rsq (R1 + R2) (S1 + S2) (σ1 + σ2)%strat (τ1 + τ2)%strat.
  Proof.
    intros R1 S1 ? ? R2 S2 ? ? H1 H2 s (s1 & s2 & Hs1 & Hs2 & Hs).
    eapply (fcomp_rsp fcrs_ready); eauto.
  Qed.
End FCOMP_RSQ.

Infix "+" := (fcomp_rsq _ _ _ _ _ _ _ _) : rsq_scope.

(** *** Monoidal structure *)

(** Again we can lift the structural isomorphisms we used
  for signature homomorphisms. *)

Coercion emor_rc : emor >-> conv.


(** * §5 SPATIAL COMPOSITION *)

(** ** §5.1 Explicit State *)

(** *** Tensor product of effect signatures *)

(** As with flat composition, we only formalize the nullary and binary cases.
  The unit is a special case of {u : U | u ∈ U}, defined below. *)

Definition glob U : esig :=
  {|
    op := U;
    ar _ := U;
  |}.

Notation "1" := (glob unit) : esig_scope.

(** The binary tensor product is defined as follows. *)

Canonical Structure tens E1 E2 :=
  {|
    op := op E1 * op E2;
    ar m := ar (fst m) * ar (snd m);
  |}%type.

Infix "*" := tens : esig_scope.

(** *** Tensor product of signature homomorphisms *)

(** As with flat composition, we first define the monoidal structure
  in the simpler setting of signature homomorphisms. *)

Section TENS_EMOR.
  Context {E1 E2 F1 F2} (f1 : emor E1 F1) (f2 : emor E2 F2).

  Definition tens_emor : emor (E1 * E2) (F1 * F2) :=
    fun q => econs (operator (f1 (fst q)),
                    operator (f2 (snd q)))
                   (fun r => (operand (f1 (fst q)) (fst r),
                              operand (f2 (snd q)) (snd r))).
End TENS_EMOR.

Infix "*" := tens_emor : emor_scope.

(** **** Functoriality *)

Lemma tens_eid {E F} :
  @eid E * @eid F = @eid (E * F).
Proof.
  apply functional_extensionality_dep. intros [q1 q2].
  unfold eid, tens_emor. cbn. f_equal.
  apply functional_extensionality. intros [r1 r2].
  reflexivity.
Qed.

Lemma tens_compose {E1 E2 F1 F2 G1 G2} :
  forall (g1 : emor F1 G1) (g2 : emor F2 G2) (f1 : emor E1 F1) (f2 : emor E2 F2),
    (g1 ∘ f1) * (g2 ∘ f2) = (g1 * g2) ∘ (f1 * f2).
Proof.
  intros.
  apply functional_extensionality_dep. intros [q1 q2].
  reflexivity.
Qed.

(** **** Left unitor *)

Definition tlu {E} : emor (1 * E) E :=
  fun q => econs (E := 1 * E) (tt, q) (fun r => snd r).

Definition tlur {E} : emor E (1 * E) :=
  fun q => econs (snd q) (fun r => (tt, r)).

Lemma tlur_tlu {E} :
  @tlur E ∘ @tlu E = eid.
Proof.
  apply functional_extensionality_dep. intros [[ ] q].
  unfold eid, ecomp. cbn. f_equal.
  apply functional_extensionality. intros [[ ] r].
  reflexivity.
Qed.

Lemma tlu_tlur {E} :
  @tlu E ∘ @tlur E = eid.
Proof.
  reflexivity.
Qed.

(** **** Right unitor *)

Definition tru {E} : emor (E * 1) E :=
  fun q => econs (E := E * 1) (q, tt) (fun r => fst r).

Definition trur {E} : emor E (E * 1) :=
  fun q => econs (fst q) (fun r => (r, tt)).

Lemma trur_tru {E} :
  @trur E ∘ @tru E = eid.
Proof.
  apply functional_extensionality_dep. intros [q [ ]].
  unfold eid, ecomp. cbn. f_equal.
  apply functional_extensionality. intros [r [ ]].
  reflexivity.
Qed.

Lemma tru_trur {E} :
  @tru E ∘ @trur E = eid.
Proof.
  reflexivity.
Qed.

(** **** Associator *)

Definition tassoc {E F G} : emor ((E * F) * G) (E * (F * G)) :=
  fun q => econs ((fst q, fst (snd q)), snd (snd q))
                 (fun r => (fst (fst r), (snd (fst r), snd r))).

Definition tassocr {E F G} : emor (E * (F * G)) ((E * F) * G) :=
  fun q => econs (fst (fst q), (snd (fst q), snd q))
                 (fun r => ((fst r, fst (snd r)), snd (snd r))).

Lemma tassocr_tassoc {E F G} :
  @tassocr E F G ∘ @tassoc E F G = eid.
Proof.
  apply functional_extensionality_dep. intros [[q1 q2] q3].
  unfold eid, ecomp. cbn. f_equal.
  apply functional_extensionality. intros [[r1 r2] r3].
  reflexivity.
Qed.

Lemma tassoc_tassocr {E F G} :
  @tassoc E F G ∘ @tassocr E F G = eid.
Proof.
  apply functional_extensionality_dep. intros [q1 [q2 q3]].
  unfold eid, ecomp. cbn. f_equal.
  apply functional_extensionality. intros [r1 [r2 r3]].
  reflexivity.
Qed.

(** **** Braiding *)

Definition tswap {E F} : emor (tens E F) (tens F E) :=
  fun q => econs (snd q, fst q) (fun r => (snd r, fst r)).

Lemma tswap_tswap {E F} :
  @tswap E F ∘ @tswap F E = eid.
Proof.
  apply functional_extensionality_dep. intros [q1 q2].
  unfold eid, ecomp. cbn. f_equal.
  apply functional_extensionality. intros [r1 r2].
  reflexivity.
Qed.

(** **** Coherence diagrams *)

(** Triangle diagram *)

Lemma tlu_tassoc {E F} :
  (@eid E * @tlu F) ∘ @tassoc E 1 F = @tru E * @eid F.
Proof.
  reflexivity.
Qed.

(** Pentagon diagram *)

Lemma tassoc_tassoc {E F G H} :
  @tassoc E F (G * H) ∘ @tassoc (E * F) G H =
  (@eid E * @tassoc F G H) ∘ @tassoc E (F * G) H ∘ (@tassoc E F G * @eid H).
Proof.
  reflexivity.
Qed.

(** Unit coherence for braiding *)

Lemma tlu_tswap {E} :
  @tlu E ∘ @tswap E 1 = @tru E.
Proof.
  reflexivity.
Qed.

(** Hexagon *)

Lemma tassoc_tswap {E F G} :
  @tassoc F G E ∘  @tswap E (F * G) ∘  @tassoc E F G =
  (@eid F * @tswap E G) ∘ @tassoc F E G ∘ (@tswap E F * @eid G).
Proof.
  reflexivity.
Qed.

(** *** Tensor product of strategies *)

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

  Program Definition tstrat_when {i1 i2 i} (p : tpos i1 i2 i)
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

  (** **** Residuals *)

  Lemma tstrat_next_oq q1 q2 σ1 σ2 :
    next (oq (q1,q2)) (tstrat_when tp_ready σ1 σ2) =
    tstrat_when (tp_running q1 q2) (next (oq q1) σ1) (next (oq q2) σ2).
  Proof.
    apply antisymmetry; cbn.
    - intros s (s1 & s2 & Hs & Hs1 & Hs2). dependent destruction Hs. eauto.
    - intros s (s1 & s2 & Hs & Hs1 & Hs2). eauto 10.
  Qed.

  Lemma tstrat_next_pq {q1 q2} m1 m2 σ1 σ2 :
    next (pq (m1,m2)) (tstrat_when (tp_running q1 q2) σ1 σ2) =
    tstrat_when (tp_suspended q1 q2 m1 m2) (next (pq m1) σ1) (next (pq m2) σ2).
  Proof.
    apply antisymmetry; cbn.
    - intros s (s1 & s2 & Hs & Hs1 & Hs2). dependent destruction Hs. eauto.
    - intros s (s1 & s2 & Hs & Hs1 & Hs2). eauto 10.
  Qed.

  Lemma tstrat_next_oa {q1 q2 m1 m2} n1 n2 σ1 σ2 :
    next (oa (m := (m1,m2)) (n1,n2)) (tstrat_when (tp_suspended q1 q2 m1 m2) σ1 σ2) =
    tstrat_when (tp_running q1 q2) (next (oa n1) σ1) (next (oa n2) σ2).
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
    next (pa (q := (q1,q2)) (r1,r2)) (tstrat_when (tp_running q1 q2) σ1 σ2) =
    tstrat_when tp_ready (next (pa r1) σ1) (next (pa r2) σ2).
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

Notation tstrat := (tstrat_when tp_ready).
Infix "*" := tstrat : strat_scope.

(** *** Tensor product of refinement conventions *)

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

  (** **** Residuals *)

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

  (** **** Preservation of [sup] and [inf]. *)

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

Infix "*" := tconv : conv_scope.

(** **** Functoriality vs vertical composition *)

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

Lemma tconv_vid {E F} :
  tconv (@vid E) (@vid F) = @vid (E * F).
Proof.
  apply Downset.has_eq_ext. cbn.
  intros s.
  induction s as [[m1 u1] [m2 u2] |
                  [m1 u1] [m2 u2] [n1 u1'] [n2 u2'] |
                  [m1 u1] [m2 u2] [n1 u1'] [n2 u2'] k]; cbn in *.
  - firstorder congruence.
  - firstorder try congruence; xsubst.
    + intros H. dependent destruction H. auto.
    + intros H. dependent destruction H. auto.
    + dependent destruction H.
      destruct (classic (n1 ~= n2)); auto.
      destruct (classic (u1' ~= u2')); auto.
      dependent destruction H.
      dependent destruction H1.
      elim H0; auto.
  - firstorder try congruence; xsubst.
    + dependent destruction H5. elim H4; auto.
    + dependent destruction H5. elim H4; auto.
    + dependent destruction H4.
      rewrite !rcnext_vid in H3. auto.
    + dependent destruction H1.
      destruct (classic (n1 ~= n2)); auto.
      destruct (classic (u1' ~= u2')); auto.
      dependent destruction H1.
      dependent destruction H3.
      right. right. rewrite !rcnext_vid. auto.
Qed.

(** *** Tensor product of refinement squares *)

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
        rsp (tconv R1 R2) (tconv S1 S2) u s (tstrat_when v' τ1 τ2)
      | _ =>
        rsp (tconv R1 R2) (tconv S1 S2) u s (tstrat_when v' τ1 τ2)
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

  Lemma trsq :
    forall {R1 : conv E1 E1'} {S1 : conv F1 F1'} {σ1 : E1 ->> F1} {τ1 : E1' ->> F1'}
           {R2 : conv E2 E2'} {S2 : conv F2 F2'} {σ2 : E2 ->> F2} {τ2 : E2' ->> F2'},
      rsq R1 S1 σ1 τ1 ->
      rsq R2 S2 σ2 τ2 ->
      rsq (R1 * R2) (S1 * S2) (σ1 * σ2) (τ1 * τ2).
  Proof.
    intros. intros s (s1 & s2 & Hs & Hs1 & Hs2).
    eapply (trsp (p := trs_ready)); eauto.
  Qed.
End TRSQ.

Infix "*" := trsq : rsq_scope.

(** ** §5.2 Passing State Through *)

(** ** §5.3 Transforming State *)

(** Since the tensor product of full-blown strategies does not work in
  the general case, we define increasingly sophisticated notions of
  "passive components" to act on global state components of effect
  signatures. As with signature homomorphisms, this approach allows us
  to define and reason simple transformations more easily while
  retaining the expressivity required for the more sophisticated
  constructions. *)

(** *** Bijections *)

Record bijection {U V} :=
  {
    fw : U -> V;
    bw : V -> U;
    bw_fw u : bw (fw u) = u;
    fw_bw v : fw (bw v) = v;
  }.

Arguments bijection : clear implicits.

Declare Scope bijection_scope.
Delimit Scope bijection_scope with bijection.
Bind Scope bijection_scope with bijection.
Open Scope bijection_scope.

Lemma bij_eq_ext {U V} (f g : bijection U V) :
  (forall u, fw f u = fw g u) -> f = g.
Proof.
  destruct f as [ff fb Hfbf Hffb], g as [gf gb Hgbf Hgfb]. cbn.
  intros H. apply functional_extensionality in H. subst.
  assert (fb = gb).
  { apply functional_extensionality. intros v.
    rewrite <- Hgfb at 1.
    rewrite Hfbf. auto. } subst.
  f_equal; apply proof_irrelevance.
Qed.

(** **** Composition *)

Program Definition bid {U} : bijection U U :=
  {| fw u := u;
     bw u := u |}.

Program Definition bcomp {U V W} (g : bijection V W) (f : bijection U V) :=
  {| fw u := fw g (fw f u);
     bw w := bw f (bw g w) |}.
Solve Obligations
  with cbn; intros; rewrite ?bw_fw, ?fw_bw; reflexivity.

Infix "∘" := bcomp : bijection_scope.

Lemma bcomp_bid_l {U V} (f : bijection U V) :
  bcomp bid f = f.
Proof.
  apply bij_eq_ext. reflexivity.
Qed.

Lemma bcomp_bid_r {U V} (f : bijection U V) :
  bcomp f bid = f.
Proof.
  apply bij_eq_ext. reflexivity.
Qed.

Lemma bcomp_bcomp {U V W X} f g h :
  @bcomp U V X (@bcomp V W X h g) f = @bcomp U W X h (@bcomp U V W g f).
Proof.
  apply bij_eq_ext. reflexivity.
Qed.

(** **** Inverse *)

Definition inv {U V} (f : bijection U V) : bijection V U :=
  {| fw := bw f; bw := fw f; bw_fw := fw_bw f; fw_bw := bw_fw f |}.

Lemma inv_invol {U V} (f : bijection U V) :
  inv (inv f) = f.
Proof.
  destruct f. reflexivity.
Qed.

Lemma inv_l {U V} (f : bijection U V) :
  inv f ∘ f = bid.
Proof.
  apply bij_eq_ext; cbn; auto using bw_fw.
Qed.

Lemma inv_r {U V} (f : bijection U V) :
  f ∘ inv f = bid.
Proof.
  apply bij_eq_ext; cbn; auto using fw_bw.
Qed.

(** **** Product *)

Program Definition prod_bij {U1 U2 V1 V2} (f1: bijection U1 V1) (f2: bijection U2 V2) :=
  {| fw u := (fw f1 (fst u), fw f2 (snd u));
     bw v := (bw f1 (fst v), bw f2 (snd v)) |}.
Solve Obligations with
  cbn; intros; rewrite ?bw_fw, ?fw_bw; auto using surjective_pairing.

Infix "*" := prod_bij : bijection_scope.

Lemma prod_bij_id {U V} :
  @bid U * @bid V = @bid (U * V).
Proof.
  apply bij_eq_ext. intros [u v]. reflexivity.
Qed.

Lemma prod_bij_bcomp {U1 U2 V1 V2 W1 W2} :
  forall (g1 : bijection V1 W1) (g2 : bijection V2 W2)
         (f1 : bijection U1 V1) (f2 : bijection U2 V2),
    (g1 ∘ f1) * (g2 ∘ f2) = (g1 * g2) ∘ (f1 * f2).
Proof.
  intros. apply bij_eq_ext. intros [u1 u2]. reflexivity.
Qed.

(** **** Left unitor *)

Program Definition plu {U} : bijection (unit * U) U :=
  {| fw := snd; bw := pair tt |}.
Solve Obligations with
  repeat (intros [[ ] ?] || intro); reflexivity.

(** **** Right unitor *)

Program Definition pru {U} : bijection (U * unit) U :=
  {| fw := fst; bw u := (u, tt) |}.
Solve Obligations with
  repeat (intros [? [ ]] || intro); reflexivity.

(** **** Associator *)

Program Definition passoc {U V W} : bijection ((U * V) * W) (U * (V * W)) :=
  {| fw x := (fst (fst x), (snd (fst x), snd x));
     bw x := ((fst x, fst (snd x)), snd (snd x)) |}.

(** **** Braiding *)

Program Definition pswap {U V} : bijection (U * V) (V * U) :=
  {| fw uv := (snd uv, fst uv);
     bw vu := (snd vu, fst vu) |}.

Lemma pswap_pswap {U V} :
  @pswap U V ∘ @pswap V U = bid.
Proof.
  apply bij_eq_ext; repeat intros [? ?]; reflexivity.
Qed.

Lemma inv_pswap {U V} :
  inv (@pswap U V) = @pswap V U.
Proof.
  apply bij_eq_ext; repeat intros [? ?]; reflexivity.
Qed.

(** **** Triangle diagram *)

Lemma plu_passoc {U V} :
  (@bid U * @plu V) ∘ @passoc U unit V = @pru U * @bid V.
Proof.
  apply bij_eq_ext; reflexivity.
Qed.

(** **** Pentagon diagram *)

Lemma passoc_passoc {U V W X} :
  @passoc U V (W * X) ∘ @passoc (U * V) W X =
  (@bid U * @passoc V W X) ∘ @passoc U (V * W) X ∘ (@passoc U V W * @bid X).
Proof.
  apply bij_eq_ext; reflexivity.
Qed.

(** **** Unit coherence for braiding *)

Lemma plu_pswap {U} :
  @plu U ∘ @pswap U unit = @pru U.
Proof.
  apply bij_eq_ext; reflexivity.
Qed.

(** **** Hexagon *)

Lemma passoc_pswap {U V W} :
  @passoc V W U ∘  @pswap U (V * W) ∘  @passoc U V W =
  (@bid V * @pswap U W) ∘ @passoc V U W ∘ (@pswap U V * @bid W).
Proof.
  apply bij_eq_ext; reflexivity.
Qed.

(** *** Lenses *)

(** Note that in order to match the orientation of the strategies that
  we combine them with, our definition of lens is flipped compared
  with the traditional one. *)

Record lens {U V} :=
  {
    state : Type;
    init_state : state;
    get : state * V -> U;
    set : state * V -> U -> state * V;
    get_set v u : get (set u v) = v;
    set_get v : set v (get v) = v;
    set_set v u u' : set (set v u) u' = set v u';
  }.

Global Arguments lens : clear implicits.
Infix "~>>" := lens (at level 99, right associativity).

Declare Scope lens_scope.
Delimit Scope lens_scope with lens.
Bind Scope lens_scope with lens.
Open Scope lens_scope.

(** **** Equivalence *)

(** Unfortunately the use of state means that equivalent lenses may
  not be equal, so we need to reason up to the following notion of
  equivalence. However, equivalent lenses will yield strategy
  interpretations that are equal. *)

Record lens_eqv {U V} (f g : U ~>> V) : Prop :=
  {
    state_eqv : rel (state f) (state g);
    init_state_eqv : state_eqv (init_state f) (init_state g);
    get_eqv : Related (get f) (get g) (state_eqv * eq ++> eq);
    set_eqv : Related (set f) (set g) (state_eqv * eq ++> - ==> state_eqv * eq);
}.

Global Instance slens_eqv_equiv {U V} :
  Equivalence (@lens_eqv U V).
Proof.
  split.
  - intros f. exists eq; rauto.
  - intros f g [R Hinit Hget Hset].
    exists (flip R); try rauto.
    + repeat rstep. destruct H. symmetry. apply Hget. split; auto.
    + repeat rstep. destruct H. edestruct (Hset y x); eauto.
      * split; auto.
      * split; eauto.
  - intros f g h [R Hinit_fg Hget_fg Hset_fg] [S Hinit_gh Hget_gh Hset_gh].
    exists (rel_compose R S); eauto.
    + repeat rstep.
      destruct H as ((m & Hxm & Hmy) & H).
      transitivity (get g (m, snd x)).
      * apply Hget_fg. split; auto.
      * apply Hget_gh. split; auto.
    + repeat rstep.
      destruct H as ((m & Hxm & Hmy) & H).
      split.
      * exists (fst (set g (m, snd x) x0)).
        split; eauto.
        -- rstep. apply Hset_fg. split; auto.
        -- rstep. apply Hset_gh. split; auto.
      * transitivity (snd (set g (m, snd x) x0)).
        -- rstep. apply Hset_fg. split; auto.
        -- rstep. apply Hset_gh. split; auto.
Qed.

Infix "==" := lens_eqv (at level 70, right associativity).

(** **** Embedding bijections *)

Program Definition bij_lens {U V} (f : bijection U V) : U ~>> V :=
  {|
    state := unit;
    init_state := tt;
    get x := bw f (snd x);
    set _ x := (tt, fw f x);
  |}.
Next Obligation.
  apply bw_fw.
Qed.
Next Obligation.
  destruct u. rewrite fw_bw. auto.
Qed.

Coercion bij_lens : bijection >-> lens.

(** **** Composition *)

Notation lid := (bij_lens bid).

Program Definition lcomp {U V W} (g : lens V W) (f : lens U V) : lens U W :=
  {|
    state := state g * state f;
    init_state := (init_state g, init_state f);
    get w := get f (snd (fst w), get g (fst (fst w), snd w));
    set w u :=
      let v  := get g (fst (fst w), snd w) in
      let v' := set f (snd (fst w), v) u in
      let w' := set g (fst (fst w), snd w) (snd v') in
      ((fst w', fst v'), snd w')
  |}.
Next Obligation.
  cbn. repeat rewrite <- ?surjective_pairing, ?get_set. auto.
Qed.
Next Obligation.
  cbn. repeat (rewrite <- ?surjective_pairing, ?set_get; cbn). auto.
Qed.
Next Obligation.
  cbn. repeat (rewrite <- ?surjective_pairing, ?get_set, ?set_get, ?set_set; cbn). auto.
Qed.

Infix "∘" := lcomp : lens_scope.

Lemma lcomp_lid_l {U V} (f : lens U V) :
  lid ∘ f == f.
Proof.
  exists (fun x y => snd x = y); cbn; auto.
  - repeat rstep. destruct H as [H1 H2].
    rewrite H1, H2, <- surjective_pairing. auto.
  - repeat rstep. destruct H as [H1 H2].
    rewrite H1, H2, <- surjective_pairing. split; cbn; auto.
Qed.

Lemma lcomp_lid_r {U V} (f : lens U V) :
  f ∘ lid == f.
Proof.
  exists (fun x y => fst x = y); cbn; auto.
  - repeat rstep. destruct H as [H1 H2].
    rewrite H1, H2, <- surjective_pairing. auto.
  - repeat rstep. destruct H as [H1 H2].
    rewrite H1, H2, <- surjective_pairing. split; cbn; auto.
Qed.

Lemma lcomp_lcomp {U V W X} :
  forall (h : lens W X) (g : lens V W) (f : lens U V),
    (h ∘ g) ∘ f == h ∘ (g ∘ f).
Proof.
  intros.
  exists (fun x y => x = ((fst y, fst (snd y)), snd (snd y))); auto.
  - repeat rstep. cbn in *.
    destruct x as [[[s1 s2] s3] x], y as [[t1 [t2 t3]] y], H as [H1 H2].
    cbn in *. congruence.
  - repeat rstep. cbn in *.
    destruct x as [[[s1 s2] s3] x], y as [[t1 [t2 t3]] y], H as [H1 H2].
    cbn in *. inversion H1; clear H1; subst. split; reflexivity.
Qed.

Lemma bij_lens_bcomp {U V W} (g : bijection V W) (f : bijection U V) :
  bij_lens (g ∘ f) == bij_lens g ∘ bij_lens f.
Proof.
  exists rel_top; cbn.
  - constructor.
  - repeat rstep. destruct H as [_ H]. congruence.
  - repeat rstep.
Qed.

(** **** Tensor product *)

Program Definition prod_lens {U1 U2 V1 V2} (f1 : lens U1 V1) (f2 : lens U2 V2) :=
  {|
    init_state := (init_state f1, init_state f2);
    get v := (get f1 (fst (fst v), fst (snd v)),
              get f2 (snd (fst v), snd (snd v)));
    set v u :=
      let v1 := set f1 (fst (fst v), fst (snd v)) (fst u) in
      let v2 := set f2 (snd (fst v), snd (snd v)) (snd u) in
      ((fst v1, fst v2), (snd v1, snd v2));
  |}.
Next Obligation.
  cbn. rewrite <- ?surjective_pairing, ?get_set. reflexivity.
Qed.
Next Obligation.
  cbn. rewrite ?set_get. cbn. reflexivity.
Qed.
Next Obligation.
  cbn. rewrite <- ?surjective_pairing, ?set_set. reflexivity.
Qed.

Infix "*" := prod_lens : lens_scope.

(** **** Initial lens *)

Program Definition ldrop {U} : lens unit U :=
  {| init_state := tt; get _ := tt; set x _ := x |}.
Next Obligation.
  destruct v; auto.
Qed.

(** **** Promoting a stateful lens to a strategy *)

Section LENS_STRAT.
  Context {U V : Type} (f : lens U V).

  (** Between any two visits back to the [ready] state, the strategy
    associated with a lens only needs to remember which [u] is
    currently the latest candidate for being written back into the
    [(v, p)] pair before we give it back to the environment. Given the
    lens laws, there are many equivalent ways to formulate it as far
    as when [get] and [set] are being used. But since we need to
    remember the latest incoming question for play structure purposes
    anyway, we choose to keep it constant and use this solution. *)

  Variant lpos : @position (glob U) (glob V) -> Type :=
    | lready (p : state f) : lpos ready
    | lrunning (p : state f) (v : glob V) (u : glob U) : lpos (running v)
    | lsuspended (p : state f) (v : glob V) (u : glob U) : lpos (suspended v u).

  Inductive lens_has : forall {i}, lpos i -> play i -> Prop :=
    | lens_ready p :
        lens_has (lready p) pnil_ready
    | lens_oq p v u s :
        lens_has (lrunning p v u) s ->
        get f (p, v) = u ->
        lens_has (lready p) (oq v :: s)
    | lens_pq p v u s :
        lens_has (lsuspended p v u) s ->
        lens_has (lrunning p v u) (pq u :: s)
    | lens_suspended p v u :
        lens_has (lsuspended p v u) (pnil_suspended v u)
    | lens_oa p v u u' s :
        lens_has (lrunning p v u') s ->
        lens_has (lsuspended p v u) (@oa _ _ v u u' :: s)
    | lens_pa p v u p' v' s :
        lens_has (lready p') s ->
        set f (p, v) u = (p', v') ->
        lens_has (lrunning p v u) (@pa _ (glob V) v v' :: s).

  Obligation Tactic := cbn.

  Program Definition lens_strat_when {i} (p : lpos i) : strat (glob U) (glob V) i :=
    {| Downset.has := lens_has p |}.
  Next Obligation.
    intros i q x y Hxy Hy. revert q Hy.
    induction Hxy; intros;
      try dependent destruction q;
      try dependent destruction Hy;
      econstructor; eauto.
  Qed.

  Definition lens_strat :=
    lens_strat_when (lready (init_state f)).

  (** Some properties *)

  Lemma lens_strat_next_oq (p : state f) (v : glob V) (u : U) :
    get f (p, v) = u ->
    next (oq v) (lens_strat_when (lready p)) = lens_strat_when (lrunning p v u).
  Proof.
    intros Hv.
    apply antisymmetry; cbn; intros s Hs.
    - dependent destruction Hs. congruence.
    - econstructor; eauto.
  Qed.

  Lemma lens_strat_next_pq (p : state f) (v : glob V) (u : glob U) :
    next (pq u) (lens_strat_when (lrunning p v u)) =
    lens_strat_when (lsuspended p v u).
  Proof.
    apply antisymmetry; cbn; intros s Hs.
    - dependent destruction Hs. auto.
    - econstructor; eauto.
  Qed.

  Lemma lens_strat_next_oa (p : state f) (v : glob V) (u : glob U) (u' : ar u) :
    next (oa u') (lens_strat_when (lsuspended p v u)) =
    lens_strat_when (lrunning p v u').
  Proof.
    apply antisymmetry; cbn; intros s Hs.
    - dependent destruction Hs. auto.
    - econstructor; eauto.
  Qed.

  Lemma lens_strat_next_pa (p : state f) (v : glob V) (u : U) p' (v' : ar v) :
    set f (p, v) u = (p', v') ->
    next (pa v') (lens_strat_when (lrunning p v u)) =
    lens_strat_when (lready p').
  Proof.
    intros Hv'.
    apply antisymmetry; cbn; intros s Hs.
    - dependent destruction Hs. setoid_rewrite H in Hv'. congruence.
    - econstructor; eauto.
  Qed.
End LENS_STRAT.

Section LENS_STRAT_REF.
  Context {U V : Type} (f g : U ~>> V).

  Inductive lpos_eqv (R : rel _ _) : forall {i j}, rel (lpos f i) (lpos g j) :=
    | lready_eqv pf pg :
        R pf pg ->
        lpos_eqv R (lready f pf) (lready g pg)
    | lrunning_eqv pf pg v u :
        R pf pg ->
        lpos_eqv R (lrunning f pf v u) (lrunning g pg v u)
    | lsuspended_eqv pf pg v u :
        R pf pg ->
        lpos_eqv R (lsuspended f pf v u) (lsuspended g pg v u).

  Hint Constructors lens_has lpos_eqv.

  Lemma lens_strat_ref :
    lens_eqv f g -> lens_strat f [= lens_strat g.
  Proof.
    intros Hfg s. cbn.
    destruct Hfg as [Rfg Hinit Hget Hset].
    generalize (lready_eqv Rfg _ _ Hinit). clear Hinit.
    generalize (lready f (init_state f)) as pf, (lready g (init_state g)) as pg.
    intros pf pg Hp H. revert pg Hp.
    induction H; intros pg Hp; dependent destruction Hp; eauto 10.
    - econstructor; eauto.
      replace (get g (pg0, v)) with (get f (p, v)) by (apply Hget; rauto).
      assumption.
    - edestruct (Hset (p, v) (pg0, v) rauto u) as [Hp' ?].
      edestruct (set g (pg0, v) u) as [pg' xv'] eqn:Hgset.
      rewrite H0 in *. cbn in *. subst.
      econstructor; eauto.
  Qed.
End LENS_STRAT_REF.

Global Instance lens_strat_eq :
  Monotonic (@lens_strat) (forallr -, forallr -, lens_eqv ==> eq).
Proof.
  repeat rstep.
  apply antisymmetry; apply lens_strat_ref; rauto.
Qed.

(** **** Refinement conventions and refinement squares *)

(** Giving lenses a strategy representation means that we can reuse
  the notions of refinement conventions and refinement square that we
  defined in that broader setting. Below we provide specialized
  definitions. *)

Definition lconv U V := conv (glob U) (glob V).
Infix "<~>" := lconv (at level 99, right associativity).

Definition lsq {U1 U2 V1 V2} (R : U1 <~> U2) (S : V1 <~> V2) (f1 : U1 ~>> V1) (f2 : U2 ~>> V2) :=
  rsq R S (lens_strat f1) (lens_strat f2).

(** *** §5.4 State Encapsulation *)

(** **** Encapsulation primitive *)

(** This allows to hide part of the global state. All stateful lenses
  can be obtained as normal lense plus state encapsulation. *)

Program Definition encap {U} (u : U) : lens U unit :=
  {|
    state := U;
    init_state := u;
    get := fst;
    set _ u' := (u', tt);
  |}.
Next Obligation.
  destruct u1; auto.
Qed.

Lemma encap_prod {U V} (u : U) (v : V) :
  encap u * encap v == inv plu ∘ encap (u, v).
Proof.
Abort.

(** **** Companion and conjoint of a stateful lens *)

Section LENS_RC.
  Context {U V : Type} (f : lens U V).
  Obligation Tactic := cbn.
  Hint Constructors rsp lens_has : core.

  Fixpoint lcp_has (p : state f) (s : rcp (glob U) (glob V)) : Prop :=
    match s with
      | rcp_allow u v =>
          get f (p, v) = u
      | rcp_forbid u v u' v' =>
          get f (p, v) = u /\
          forall p', set f (p, v) u' <> (p', v')
      | rcp_cont u v u' v' k =>
          get f (p, v) = u /\
          forall p', set f (p, v) u' = (p', v') -> lcp_has p' k
    end.

  Program Definition lcp_when p : U <~> V :=
    {| Downset.has := lcp_has p |}.
  Next Obligation.
    intros p s t Hst Ht. revert p Ht.
    induction Hst; firstorder.
  Qed.

  Definition lcp :=
    lcp_when (init_state f).

  (** Useful lemmas *)

  Lemma rcnext_lcp pf (u : glob U) (v : glob V) pf' u' v' :
    get f (pf, v) = u ->
    set f (pf, v) u' = (pf', v') ->
    rcnext u v u' v' (lcp_when pf) = lcp_when pf'.
  Proof.
    intros Hu Hv'.
    apply antisymmetry; intros s; cbn.
    - intros [H H']. eauto.
    - intros Hs. split; auto. intros ? ?.
      setoid_rewrite H in Hv'. congruence.
  Qed.

  (** Companion properties *)

  Variant lcpipos pf : forall {i j}, lpos lid i -> lpos f j -> rspos i j -> Type :=
    | lcpi_ready :
      lcpipos pf (lready lid tt)
                 (lready f pf) rs_ready
    | lcpi_running (u : glob U) (v : glob V) u' :
      lcpipos pf (lrunning lid tt u u')
                 (lrunning f pf v u') (rs_running u v)
    | lcpi_suspended (u : glob U) (v : glob V) u' :
      lcpipos pf (lsuspended lid tt u u')
                 (lsuspended f pf v u') (rs_suspended u v u' u').

  Lemma lcp_intro_when {pf i j pi pj pij} (q : @lcpipos pf i j pi pj pij) :
    match q with
      | lcpi_running _ u v _ | lcpi_suspended _ u v _ => get f (pf, v) = u
      | _ => True
    end ->
    rsq_when vid (lcp_when pf) pij (lens_strat_when lid pi) (lens_strat_when f pj).
  Proof.
    intros Hq s Hs. revert pf j pj pij q Hq. cbn in *.
    induction Hs; intros.
    - dependent destruction q.
      constructor; cbn; eauto.
    - dependent destruction q. rename v into u.
      econstructor; cbn; eauto. intros v Hv.
      erewrite lens_strat_next_oq by eauto.
      apply IHHs with (q := lcpi_running pf u v u); auto.
    - dependent destruction q. rename v into u, u into u', v0 into v.
      econstructor; cbn; eauto.
      rewrite lens_strat_next_pq.
      apply IHHs with (q := lcpi_suspended pf u v u'); auto.
    - dependent destruction q. rename v into u, u into u', v0 into v.
      econstructor; cbn; eauto.
    - dependent destruction q. rename v into u, u into u', v0 into v, u' into u''.
      econstructor; cbn; eauto. intros xu'' Hxu''.
      assert (u'' ~= xu'') as HX by tauto.
      clear Hxu''. subst xu''.
      rewrite rcnext_vid, lens_strat_next_oa.
      apply IHHs with (q := lcpi_running pf u v u''); auto.
    - dependent destruction q. rename v into u, v' into u', v0 into v.
      destruct (set f (pf, v) u') as [pf' v'] eqn:Hv'.
      eapply (rsp_pa (F1:=glob U) (F2:=glob V) _ _ u v u' v').
      { cbn. intros [H H']. apply (H' pf'). auto. }
      erewrite rcnext_lcp, lens_strat_next_pa by eauto.
      apply IHHs with (q := lcpi_ready pf'); auto.
  Qed.

  Lemma lcp_intro :
    lsq vid lcp lid f.
  Proof.
    apply (lcp_intro_when (lcpi_ready (init_state f))); auto.
  Qed.

  Variant lcpepos : forall pf {i j}, lpos f i -> lpos lid j -> rspos i j -> Type :=
    | lcpe_ready pf :
      lcpepos pf (lready f pf)
                 (lready lid tt) rs_ready
    | lcpe_running pf (u : glob U) (v : glob V) (pf' : state f) u' v' :
      lcpepos pf' (lrunning f pf v u')
                 (lrunning lid tt v v') (rs_running v v)
    | lcpe_suspended pf (u : glob U) (v : glob V) (pf' : state f) u' v' :
      lcpepos pf' (lsuspended f pf v u')
                 (lsuspended lid tt v v') (rs_suspended v v u' v').

  Lemma lcp_elim_when {pf i j pi pj pij} (q : @lcpepos pf i j pi pj pij) :
    match q with
      | lcpe_running pf u v pf' u' v'
      | lcpe_suspended pf u v pf' u' v' =>
          get f (pf, v) = u /\
          set f (pf, v) u' = (pf', v')
      | _ => True
    end ->
    rsq_when (lcp_when pf) vid pij (lens_strat_when f pi) (lens_strat_when lid pj).
  Proof.
    intros Hq s Hs. revert pf j pj pij q Hq. cbn in *.
    induction Hs; intros.
    - dependent destruction q.
      constructor; cbn; eauto.
    - dependent destruction q.
      econstructor; cbn; eauto. intros v' Hv'. subst v'.
      erewrite lens_strat_next_oq by eauto. cbn.
      apply IHHs with (q := lcpe_running p u v p u v); auto.
      split; auto. rewrite <- H, set_get. reflexivity.
    - dependent destruction q. rename u0 into u, u into u'.
      destruct Hq as [Hu Hv'].
      apply (rsp_pq _ _ v v u' v'). { cbn. rewrite <- Hv', get_set. auto. }
      rewrite lens_strat_next_pq.
      apply IHHs with (q := lcpe_suspended p u v pf' u' v'); auto.
    - dependent destruction q.
      econstructor; cbn; eauto.
    - dependent destruction q. rename p into pf, u0 into u, u into u', u' into u''.
      destruct Hq as [Hu Hv'].
      econstructor; cbn; eauto. intros v'' Hv''.
      apply not_and_or in Hv'' as [Hv'' | Hv''].
      { rewrite <- Hv', get_set in Hv''. tauto. }
      apply not_all_ex_not in Hv'' as [pf'' Hv''].
      apply NNPP in Hv''.
      erewrite rcnext_lcp, lens_strat_next_oa; eauto.
      2: setoid_rewrite <- Hv'; rewrite get_set; reflexivity.
      apply IHHs with (q := lcpe_running pf u v pf'' u'' v''); auto.
      rewrite <- Hv', set_set in Hv''. auto. 
    - dependent destruction q. destruct Hq as [Hu Hv'].
      rename p into pf, p' into pf', pf' into pf'',
             u0 into u, u into u'.
      rewrite Hv' in H. dependent destruction H.
      eapply (rsp_pa (F1:=glob V) (F2:=glob V) _ _ v v v' v').
      { cbn. intros [H H']. elim H'; auto. }
      erewrite rcnext_vid, lens_strat_next_pa by (cbn; eauto).
      apply IHHs with (q := lcpe_ready pf'); auto.
  Qed.

  Lemma lcp_elim :
    lsq lcp vid f lid.
  Proof.
    apply (lcp_elim_when (lcpe_ready (init_state f))); auto.
  Qed.

  (** This is just the transpose, maybe we could introduce that operation. *)

  Fixpoint lcj_has (p : state f) (s : rcp (glob V) (glob U)) : Prop :=
    match s with
      | rcp_allow v u =>
          get f (p, v) = u
      | rcp_forbid v u v' u' =>
          get f (p, v) = u /\
          forall p', set f (p, v) u' <> (p', v')
      | rcp_cont v u v' u' k =>
          get f (p, v) = u /\
          forall p', set f (p, v) u' = (p', v') -> lcj_has p' k
    end.

  Program Definition lcj_when pf : V <~> U :=
    {| Downset.has := lcj_has pf |}.
  Next Obligation.
    intros pf s t Hst Ht. revert pf Ht.
    induction Hst; firstorder.
  Qed.

  Definition lcj :=
    lcj_when (init_state f).

  (** Useful lemmas *)

  Lemma rcnext_lcj pf (u : glob U) (v : glob V) pf' u' v' :
    get f (pf, v) = u ->
    set f (pf, v) u' = (pf', v') ->
    rcnext v u v' u' (lcj_when pf) = lcj_when pf'.
  Proof.
    intros Hu Hv'.
    apply antisymmetry; intros s; cbn.
    - intros [H H']. eauto.
    - intros Hs. split; auto. intros ? ?.
      setoid_rewrite H in Hv'. congruence.
  Qed.

  (** Companion properties *)

  Variant lcjipos : forall pf {i j}, lpos lid i -> lpos f j -> rspos i j -> Type :=
    | lcji_ready pf :
      lcjipos pf (lready lid tt)
                 (lready f pf) rs_ready
    | lcji_running pf (u : glob U) (v : glob V) (pf' : state f) u' v' :
      lcjipos pf' (lrunning lid tt v v')
                  (lrunning f pf v u') (rs_running v v)
    | lcji_suspended pf (u : glob U) (v : glob V) (pf' : state f) u' v' :
      lcjipos pf' (lsuspended lid tt v v')
                  (lsuspended f pf v u') (rs_suspended v v v' u').

  Lemma lcj_intro_when {pf i j pi pj pij} (q : @lcjipos pf i j pi pj pij) :
    match q with
      | lcji_running pf u v pf' u' v'
      | lcji_suspended pf u v pf' u' v' =>
          get f (pf, v) = u /\
          set f (pf, v) u' = (pf', v')
      | _ => True
    end ->
    rsq_when (lcj_when pf) vid pij (lens_strat_when lid pi) (lens_strat_when f pj).
  Proof.
    intros Hq s Hs. revert pf j pj pij q Hq. cbn in *.
    induction Hs; intros.
    - dependent destruction q.
      constructor; cbn; eauto.
    - dependent destruction q.
      econstructor; cbn; eauto. intros v' Hv'. subst v'.
      erewrite lens_strat_next_oq by eauto.
      set (u := get f (pf, v)).
      apply IHHs with (q := lcji_running pf u v pf u v); auto.
      split; auto. subst u. rewrite set_get. reflexivity.
    - dependent destruction q. destruct Hq as [Hu Hv'].
      rename u0 into u, u into v'.
      apply (rsp_pq _ _ v v v' u'). { cbn. rewrite <- Hv', get_set. auto. }
      rewrite lens_strat_next_pq.
      apply IHHs with (q := lcji_suspended pf u v pf' u' v'); auto.
    - dependent destruction q.
      econstructor; cbn; eauto.
    - dependent destruction q. destruct Hq as [Hu Hv'].
      rename u0 into u, u'0 into u', u into v', u' into v''.
      econstructor; cbn; eauto. intros u'' Hu''.
      apply not_and_or in Hu'' as [Hu'' | Hu''].
      { rewrite <- Hv', get_set in Hu''. tauto. }
      apply not_all_ex_not in Hu'' as [pf'' Hv''].
      apply NNPP in Hv''.
      erewrite rcnext_lcj, lens_strat_next_oa; eauto.
      2: setoid_rewrite <- Hv'; rewrite get_set; reflexivity.
      apply IHHs with (q := lcji_running pf u v pf'' u'' v''); auto.
      rewrite <- Hv', set_set in Hv''. auto. 
    - dependent destruction q. destruct Hq as [Hu Hv'].
      rename u0 into u.
      eapply (rsp_pa (F1:=glob V) (F2:=glob V) _ _ v v v' v').
      { cbn. intros [H H']. elim H'; auto. }
      erewrite rcnext_vid, lens_strat_next_pa by (cbn; eauto).
      apply IHHs with (q := lcji_ready pf'); auto.
  Qed.

  Lemma lcj_intro :
    lsq lcj vid lid f.
  Proof.
    apply (lcj_intro_when (lcji_ready (init_state f))); auto.
  Qed.

  Variant lcjepos pf : forall {i j}, lpos f i -> lpos lid j -> rspos i j -> Type :=
    | lcje_ready :
      lcjepos pf (lready f pf)
                 (lready lid tt) rs_ready
    | lcje_running (u : glob U) (v : glob V) u' :
      lcjepos pf (lrunning f pf v u')
                 (lrunning lid tt u u') (rs_running v u)
    | lcje_suspended (u : glob U) (v : glob V) u' :
      lcjepos pf (lsuspended f pf v u')
                 (lsuspended lid tt u u') (rs_suspended v u u' u').

  Lemma lcj_elim_when {pf i j pi pj pij} (q : @lcjepos pf i j pi pj pij) :
    match q with
      | lcje_running _ u v _ | lcje_suspended _ u v _ => get f (pf, v) = u
      | _ => True
    end ->
    rsq_when vid (lcj_when pf) pij (lens_strat_when f pi) (lens_strat_when lid pj).
  Proof.
    intros Hq s Hs. revert pf j pj pij q Hq. cbn in *.
    induction Hs; intros.
    - dependent destruction q.
      constructor; cbn; eauto.
    - dependent destruction q. rename p into pf.
      econstructor; cbn; eauto. intros u' Hu'.
      setoid_rewrite H in Hu'. subst u'.
      erewrite lens_strat_next_oq by eauto.
      apply IHHs with (q := lcje_running pf u v u); auto.
    - dependent destruction q. rename p into pf, u0 into u, u into u'.
      econstructor; cbn; eauto.
      rewrite lens_strat_next_pq.
      apply IHHs with (q := lcje_suspended pf u v u'); auto.
    - dependent destruction q. rename p into pf, u0 into u, u into u'.
      econstructor; cbn; eauto.
    - dependent destruction q. rename p into pf, u0 into u, u into u', u' into u''.
      econstructor; cbn; eauto. intros xu'' Hxu''.
      assert (u'' ~= xu'') as HX by tauto.
      clear Hxu''. subst xu''.
      rewrite rcnext_vid, lens_strat_next_oa.
      apply IHHs with (q := lcje_running pf u v u''); auto.
    - dependent destruction q. rename p into pf, u0 into u, u into u', p' into pf'.
      eapply (rsp_pa (F1:=glob V) (F2:=glob U) _ _ v u v' u').
      { cbn. intros [Hu H']. apply (H' pf'). auto. }
      erewrite rcnext_lcj, lens_strat_next_pa by (cbn; eauto).
      apply IHHs with (q := lcje_ready pf'); auto.
  Qed.

  Lemma lcj_elim :
    lsq vid lcj f lid.
  Proof.
    apply (lcj_elim_when (lcje_ready (init_state f))); auto.
  Qed.
End LENS_RC.

(** *** Spatial Composition *)

(** Based on the ingredients above, we can develop our theory of
  spatial composition, which is analogous to the tensor product but
  accepts only lenses on the right-hand side. *)

(** **** Definitions *)

(** Effect signatures *)

Definition scomp (E : esig) (U : Type) : esig :=
  E * glob U.

Infix "@" := scomp (at level 40, left associativity) : esig_scope.

(** Strategies and lenses *)

Definition scomp_strat {E F U V} (σ: E ->> F) (f: lens U V) : E @ U ->> F @ V :=
  tstrat σ (lens_strat f).

Infix "@" := scomp_strat : strat_scope.

Global Instance scomp_strat_eq :
  Monotonic
    (@scomp_strat)
    (forallr -, forallr -, forallr -, forallr -, - ==> lens_eqv ==> eq).
Proof.
  unfold scomp_strat. repeat rstep. f_equal. rauto.
Qed.

(** Refinement conventions *)

Definition scomp_conv {E1 E2 U1 U2} (R : conv E1 E2) (S : conv (glob U1) (glob U2)) : conv (E1 @ U1) (E2 @ U2) :=
  tconv R S.

Infix "@" := scomp_conv : conv_scope.

(** Refinement squares *)

Lemma scomp_rsq {E1 E2 F1 F2 U1 U2 V1 V2} :
  forall (R : E1 <=> E2) (S : F1 <=> F2) (R' : U1 <~> U2) (S' : V1 <~> V2)
         (σ1 : E1 ->> F1) (σ2 : E2 ->> F2) (f1 : U1 ~>> V1) (f2 : U2 ~>> V2),
    rsq R S σ1 σ2 ->
    lsq R' S' f1 f2 ->
    rsq (R @ R') (S @ S') (σ1 @ f1) (σ2 @ f2).
Proof.
  eauto using trsq.
Qed.

Infix "@" := (scomp_rsq _ _ _ _ _ _ _ _) : rsq_scope.

(** **** Functoriality *)

(** Horizontal component *)

Section SCOMP_ID.
  Context {E : esig} {U : Type}.

  Variant scipos : forall {i j ij}, epos eid i -> lpos lid j -> tpos i j ij -> epos eid ij -> Type :=
    | sci_ready :
      scipos eready (lready lid tt) tp_ready eready
    | sci_suspended (q : E) (u : U) :
      scipos (esuspended q) (lsuspended lid tt u u)
        (tp_suspended (E2:=glob U) (F2:=glob U) q u q u)
        (esuspended (f := @eid (E @ U)) (q, u)).

  Hint Constructors tstrat_has emor_has lens_has.

  Lemma scomp_id_when {i j ij pi pj pij p} (x : @scipos i j ij pi pj pij p) :
    tstrat_when pij (emor_when eid pi) (lens_strat_when lid pj) = emor_when eid p.
  Proof.
    apply antisymmetry; cbn.
    - intros s (s1 & s2 & Hs & Hs1 & Hs2).
      revert j ij pj pij p x s s2 Hs Hs2.
      induction Hs1; intros.
      + dependent destruction Hs.
        dependent destruction x.
        constructor.
      + dependent destruction Hs. dependent destruction Hs2.
        dependent destruction Hs. dependent destruction Hs2.
        dependent destruction x.
        constructor.
        eapply (IHHs1 _ _ _ _ _ (sci_suspended q m2)); eauto.
      + dependent destruction Hs.
        dependent destruction x0.
        constructor.
      + dependent destruction Hs. dependent destruction Hs2.
        dependent destruction Hs. dependent destruction Hs2.
        dependent destruction x.
        constructor.
        eapply (IHHs1 _ _ _ _ _ sci_ready); eauto.
    - intros s Hs. revert i j pi pj pij x.
      induction Hs; intros.
      + dependent destruction x.
        eauto.
      + dependent destruction x.
        destruct q as [q u].
        edestruct (IHHs _ _ _ _ _ (sci_suspended q u))
          as (s1 & s2 & Hs' & Hs1 & Hs2); eauto.
        exists (oq q :: pq q :: s1), (oq u :: pq u :: s2).
        split. { constructor. constructor. assumption. }
        split. { constructor. assumption. }
        eauto.
      + dependent destruction x.
        exists (pnil_suspended _ _), (pnil_suspended _ _).
        split; eauto.
        constructor.
      + dependent destruction x.
        destruct r as [r u']. cbn in *.
        edestruct (IHHs _ _ _ _ _ sci_ready)
          as (s1 & s2 & Hs' & Hs1 & Hs2); eauto.
        exists (oa r :: pa r :: s1), (oa (E:=glob U) u' :: pa (F:=glob U) u' :: s2). 
        split. { constructor. constructor. eauto. }
        split. { constructor. eauto. }
        eauto.
  Qed.

  Lemma scomp_id :
    (id E @ lid = id (E @ U))%strat.
  Proof.
    apply (scomp_id_when sci_ready).
  Qed.
End SCOMP_ID.

Section SCOMP_COMPOSE.
  Context {E F G : esig} {U V W : Type} {g : V ~>> W} {f : U ~>> V}.

  Variant sccpos :
    forall {i1 j1 i2 j2 ij1 ij2 i12 j12 ij12}, @cpos E F G i1 j1 ij1 ->
                                               lpos (g ∘ f) ij2 ->
                                               tpos ij1 ij2 ij12 ->
                                               lpos g i2 -> tpos i1 i2 i12 ->
                                               lpos f j2 -> tpos j1 j2 j12 ->
                                               cpos i12 j12 ij12 -> Type :=
      | scc_ready pg pf :
        sccpos cpos_ready
               (lready (g∘f) (pg,pf))
               tp_ready
               (lready g pg) tp_ready
               (lready f pf) tp_ready
               cpos_ready
      | scc_left pg pf (**) q (w : glob W) pf' (v : glob V) :
        sccpos (cpos_left q)
               (lrunning (g∘f) (pg,pf) w (get f (pf',v)))
               (tp_running q w)
               (lrunning g pg w v) (tp_running q w)
               (lready f pf') tp_ready
               (cpos_left (q,w))
      | scc_right pg pf (**) q (w : glob W) pf' (v : glob V) (**) m (u : glob U) :
        sccpos (cpos_right q m)
               (lrunning (g∘f) (pg,pf) w u)
               (tp_running q w)
               (lsuspended g pg w v) (tp_suspended q w m v)
               (lrunning f pf' v u) (tp_running m v)
               (cpos_right (q,w) (m,v))
      | scc_suspended pg pf (**) q (w : glob W) pf' (v : glob V) (**) m u (**) x :
        sccpos (cpos_suspended q m x)
               (lsuspended (g∘f) (pg,pf) w u)
               (tp_suspended q w x u)
               (lsuspended g pg w v) (tp_suspended q w m v)
               (lsuspended f pf' v u) (tp_suspended m v x u)
               (cpos_suspended (q,w) (m,v) (x,u)).

  Hint Constructors lens_has tstrat_has comp_has pref sccpos.

  Lemma scomp_compose_when_1 {i1 j1 i2 j2 ij1 ij2 i12 j12 ij12 pij1 pij2 pij12 pi2 pi12 pj2 pj12 pij12'} :
    forall p: @sccpos i1 j1 i2 j2 ij1 ij2 i12 j12 ij12 pij1 pij2 pij12 pi2 pi12 pj2 pj12 pij12',
    forall s1 t1 st1, comp_has pij1 s1 t1 st1 ->
    forall st2, lens_has (g∘f) pij2 st2 ->
    forall st12, tstrat_has pij12 st1 st2 st12 ->
    match p with
      | scc_ready pg pf =>
        True
      | scc_left pg pf q w pf' v
      | scc_right pg pf q w pf' v _ _
      | scc_suspended pg pf q w pf' v _ _ _ =>
        set f (pf, get g (pg, w)) (get f (pf', v)) = (pf', v)
    end ->
    exists s1' t1' s2 t2 s12 t12,
      s1' [= s1 /\ t1' [= t1 /\
      lens_has g pi2 s2 /\
      lens_has f pj2 t2 /\
      tstrat_has pi12 s1' s2 s12 /\
      tstrat_has pj12 t1' t2 t12 /\
      comp_has pij12' s12 t12 st12.
  Proof.
    intros p s1 t1 st1 Hst1. cbn.
    revert i2 j2 ij2 i12 j12 ij12 pij2 pij12 pi2 pi12 pj2 pj12 pij12' p.
    induction Hst1; intros until p; intros st2 Hst2 st12 Hst12 Hp.
    - (* ready *)
      dependent destruction Hst12.
      dependent destruction Hst2.
      dependent destruction p.
      eauto 20.
    - (* env question *)
      dependent destruction Hst12.
      dependent destruction Hst2.
      dependent destruction p.
      rename s into s1, t into t1, w into st1, s2 into st2, s0 into st12, q2 into w.
      edestruct IHHst1 with (p := scc_left pg pf q w pf (get g (pg, w)))
        as (s1' & t1' & s2 & t2 & s12 & t12 &
            Hs1' & Ht1' & Hs2 & Ht2 & Hs12 & Ht12 & Hst12'); eauto using set_get.
      exists (oq q :: s1'), t1', (oq w :: s2), t2, (oq (q,w) :: s12), t12.
      eauto 20 using pref_refl.
    - (* left question *)
      dependent destruction p.
      rename s into s1, t into t1, w into st1, w0 into w.
      edestruct IHHst1 with (p := scc_right pg pf q w pf' v m (get f (pf',v)))
        as (s1' & t1' & s2 & t2 & s12 & t12 &
            Hs1' & Ht1' & Hs2 & Ht2 & Hs12 & Ht12 & Hst12'); eauto.
      exists (pq m :: s1'), (oq m ::t1'), (pq v :: s2), (oq v :: t2),
             (pq (m,v) :: s12), (oq (m,v) :: t12); eauto 20.
    - (* right question *)
      dependent destruction Hst12.
      dependent destruction Hst2.
      dependent destruction p.
      rename s into s1, t into t1, w into st1, q2 into w, u into x, m2 into u,
             s2 into st2, s0 into st12.
      edestruct IHHst1 with (p := scc_suspended pg pf q w pf' v m u x)
        as (s1' & t1' & s2 & t2 & s12 & t12 &
            Hs1' & Ht1' & Hs2 & Ht2 & Hs12 & Ht12 & Hst12'); eauto.
      exists s1', (pq x :: t1'), s2, (pq u :: t2),
             s12, (pq (x,u) :: t12); eauto 20.
    - (* suspended *)
      dependent destruction Hst12.
      dependent destruction Hst2.
      dependent destruction p.
      eauto 20.
    - (* environment answer *)
      dependent destruction Hst12.
      dependent destruction Hst2.
      dependent destruction p.
      rename s into s1, t into t1, w into st1, q2 into w, v into y, v0 into v,
             u into x, m2 into u, n2 into u', s2 into st2, s0 into st12.
      edestruct IHHst1 with (p := scc_right pg pf q w pf' v m u')
        as (s1' & t1' & s2 & t2 & s12 & t12 &
            Hs1' & Ht1' & Hs2 & Ht2 & Hs12 & Ht12 & Hst12'); eauto.
      exists s1', (oa y :: t1'), s2, (oa u' :: t2),
        s12, (oa (m:=(x,u)) (y,u') :: t12); eauto 20.
    - (* right answer *)
      dependent destruction p.
      rename s into s1, t into t1, w into st1, w0 into w.
      destruct (set f (pf', v) u) as [pf'' v'] eqn:H''.
      edestruct IHHst1 with (p := scc_left pg pf q w pf'' v') (st2 := st2) (st12 := st12)
        as (s1' & t1' & s2 & t2 & s12 & t12 &
            Hs1' & Ht1' & Hs2 & Ht2 & Hs12 & Ht12 & Hst12'); auto.
      { setoid_rewrite <- H''. rewrite get_set. auto. }
      { setoid_rewrite <- H''. rewrite get_set.
        setoid_rewrite <- Hp. rewrite set_set. auto. }
      exists (oa n :: s1'), (pa n :: t1'), (oa (m:=v) v' :: s2), (pa (q:=v) v' :: t2),
             (oa (m:=(m,v)) (n, v') :: s12), (pa (q:=(m,v)) (n, v') :: t12); eauto 20.
      repeat (split; eauto 20).
      + econstructor; eauto.
      + econstructor; eauto.
    - (* left answer *)      
      dependent destruction Hst12.
      dependent destruction Hst2.
      dependent destruction p. cbn in *.
      rename s into s1, t into t1, w into st1, q2 into w, s2 into st2, s0 into st12.
      rewrite Hp in Hst2. cbn in *.
      destruct (set g (pg, w) v) as [pg' w'] eqn:H''. cbn in *.
      edestruct IHHst1 with (p := scc_ready pg' pf') (st2 := st2)
        as (s1' & t1' & s2 & t2 & s12 & t12 &
            Hs1' & Ht1' & Hs2 & Ht2 & Hs12 & Ht12 & Hst12'); eauto.
      exists (pa r :: s1'), t1', (pa (F:=glob W) w' :: s2), t2,
             (pa (F:=G@W) (q:=(q,w)) (r,w') :: s12), t12; eauto 30.
      repeat (split; eauto 20).
      + econstructor; eauto.
      + rewrite Hp; cbn.
        rewrite H''; cbn.
        econstructor; eauto.
  Qed.

  Lemma scomp_compose_when_2 {i1 j1 i2 j2 ij1 ij2 i12 j12 ij12 pij1 pij2 pij12 pi2 pi12 pj2 pj12 pij12'} :
    forall p: @sccpos i1 j1 i2 j2 ij1 ij2 i12 j12 ij12 pij1 pij2 pij12 pi2 pi12 pj2 pj12 pij12',
    forall s12 t12 st12, comp_has pij12' s12 t12 st12 ->
    forall s1 s2 t1 t2,
    lens_has g pi2 s2 ->
    lens_has f pj2 t2 ->
    tstrat_has pi12 s1 s2 s12 ->
    tstrat_has pj12 t1 t2 t12 ->
    match p with
      | scc_ready pg pf =>
        True
      | scc_left pg pf q w pf' v
      | scc_right pg pf q w pf' v _ _
      | scc_suspended pg pf q w pf' v _ _ _ =>
        set f (pf, get g (pg, w)) (get f (pf', v)) = (pf', v)
    end ->
    exists st1 st2,
      comp_has pij1 s1 t1 st1 /\
      lens_has (g∘f) pij2 st2 /\
      tstrat_has pij12 st1 st2 st12.
  Proof.
    intros p s12 t12 st12 Hst12.
    revert i1 j1 i2 j2 ij1 ij2 pij1 pij2 pij12 pi2 pi12 pj2 pj12 p.
    induction Hst12; intros until p; intros s1 s2 t1 t2 Hs2 Ht2 Hs12 Ht12 Hp.
    - (* ready *)
      dependent destruction Hs12.
      dependent destruction Hs2.
      dependent destruction p.
      eauto 20.
    - (* env question *)
      dependent destruction Hs12.
      dependent destruction Hs2.
      dependent destruction p.
      rename q2 into w, q1 into q, s into s12, t into t12, w into st12.
      rename p0 into pg, s0 into s2.
      edestruct IHHst12 with (p := scc_left pg pf q w pf (get g (pg, w)))
        as (st1 & st2 & Hst1 & Hst2 & Hst12'); eauto using set_get.
      exists (oq q :: st1), (oq w :: st2).
      repeat (split; eauto).
      constructor; auto.
    - (* left question *)
      dependent destruction Hs12.
      dependent destruction Hs2.
      dependent destruction Ht12.
      dependent destruction Ht2.
      dependent destruction p.
      clear x x0 x1.
      rename q2 into w, q1 into q, s into s12, t into t12, w into st12.
      rename p1 into pf', p0 into pg, s0 into s2, s2 into t1, s3 into t2.
      rename m1 into m, m2 into v.
      edestruct IHHst12 with (p := scc_right pg pf q w pf' v m (get f (pf',v)))
        as (st1 & st2 & Hst1 & Hst2 & Hst12'); eauto.
      exists st1, st2; eauto 20.
    - (* right question *)
      dependent destruction Ht12.
      dependent destruction Ht2.
      dependent destruction p.
      clear x x0 x1.
      rename q0 into q, w0 into w, q2 into v, q1 into m, m2 into u, m1 into x,
        s into s12, t into t12, w into st12, p0 into pf', s3 into t2, s0 into t1.
      edestruct IHHst12 with (p := scc_suspended pg pf q w pf' v m u x)
        as (st1 & st2 & Hst1 & Hst2 & Hst12'); eauto.
      exists (pq x :: st1), (pq u :: st2); eauto 20.
      repeat split; eauto.
      constructor; eauto.
    - (* suspended *)
      dependent destruction Ht12.
      dependent destruction Ht2.
      dependent destruction p.
      clear x x0 x1 x2.
      rename q0 into q, q2 into v, q1 into m, m2 into u, m1 into x,
        s into s12, p0 into pf'.
      exists (pnil_suspended _ _), (pnil_suspended _ _).
      repeat split; eauto.
      constructor; eauto.
    - (* environment answer *)
      simple inversion Ht12; clear Ht12; xsubst. intros Ht12.
      dependent destruction H2. xsubst.
      apply pcons_oa_inv in H6 as [? ?]. subst.
      dependent destruction Ht2.
      dependent destruction p.
      clear x x0 x1.
      rename q0 into q, w0 into w, q2 into v, q1 into m, m2 into u, m1 into x,
        s into s12, t into t12, w into st12, p0 into pf', s3 into t2, s0 into t1,
        n1 into y, n2 into u'.
      edestruct IHHst12 with (p := scc_right pg pf q w pf' v m u')
        as (st1 & st2 & Hst1 & Hst2 & Hst12'); eauto.
      exists (oa y :: st1), (oa u' :: st2); eauto 20.
      repeat split; eauto.
      constructor; eauto.
    - (* right answer *)
      simple inversion Ht12; clear Ht12; xsubst. intros Ht12.
      dependent destruction H2. xsubst.
      apply pcons_pa_inv in H6 as [? ?]. subst.
      simple inversion Hs12; clear Hs12; xsubst. intros Hs12.
      dependent destruction H2. xsubst.
      apply pcons_oa_inv in H6 as [? ?]. subst.
      dependent destruction H.
      dependent destruction Ht2.
      dependent destruction Hs2.
      dependent destruction p1.
      clear x x0 x1 x2.
      rename q0 into q, q3 into w, q2 into v, q1 into m, s into s12, t into t12,
        w into st12, p0 into pf', r2 into v', s5 into s2, s3 into t2, p' into pf'',
        r1 into n, s0 into t1, s4 into s1, p into pg.
      edestruct IHHst12 with (p := scc_left pg pf q w pf'' v')
        as (st1 & st2 & Hst1 & Hst2 & Hst12'); eauto.
      { setoid_rewrite <- H. rewrite get_set.
        setoid_rewrite <- Hp. rewrite set_set. auto. }
      setoid_rewrite <- H in Hst2. rewrite get_set in Hst2.
      exists st1, st2. eauto.
    - (* left answer *)
      simple inversion Hs12; clear Hs12; xsubst. intros Hs12.
      dependent destruction H2. xsubst.
      apply pcons_pa_inv in H6 as [? ?]. subst.
      dependent destruction Hs2.
      dependent destruction p.
      clear x x0 x1.
      rename q1 into q, q2 into w, s into s12, t into t12, w into st12,
        p0 into pg, r2 into w', s3 into s2, r1 into r, s0 into s1, p' into pg'.
      edestruct IHHst12 with (p := scc_ready pg' pf')
        as (st1 & st2 & Hst1 & Hst2 & Hst12'); eauto.
      exists (pa r :: st1), (pa w' :: st2).
      repeat split; eauto.
      + econstructor; eauto. cbn.
        setoid_rewrite Hp. cbn.
        setoid_rewrite H. cbn. auto.
      + constructor. auto.
  Qed.
End SCOMP_COMPOSE.

Lemma scomp_compose {E F G U V W} :
  forall (σ : F ->> G) (τ : E ->> F) (g : V ~>> W) (f : U ~>> V),
    ((σ ⊙ τ) @ (g ∘ f) = (σ @ g) ⊙ (τ @ f))%strat.
Proof.
  intros. apply antisymmetry; cbn.
  - intros s (st1 & st2 & Hs & (s1 & t1 & Hs1 & Ht1 & Hst1) & Hst2).
    edestruct (@scomp_compose_when_1 E F G U V W)
      with (p := @scc_ready E F G U V W g f (init_state g) (init_state f))
      as (s1' & t1' & s2 & t2 & s12 & t12 & Hs1' & Ht1' & Hs2 & Ht2 & Hs12 & Ht12 & Hs');
    eauto 20 using Downset.closed.
  - intros s (s12 & t12 & (s1 & s2 & Hs12 & Hs1 & Hs2) &
                          (t1 & t2 & Ht12 & Ht1 & Ht2) & Hs).
    edestruct (@scomp_compose_when_2 E F G U V W)
      with (p := @scc_ready E F G U V W g f (init_state g) (init_state f))
      as (st1 & st2 & Hst1 & Hst2 & Hs');
    eauto 20.
Qed.

(** Vertical component *)

Lemma scomp_vid {E U} :
  ((@vid E) @ (@vid (glob U)) = @vid (E @ U))%conv.
Proof.
  eauto using tconv_vid.
Qed.

Lemma scomp_vcomp {E F G U V W} :
  forall (R1 : conv E F) (S1 : conv F G)
         (R2 : conv (glob U) (glob V)) (S2 : conv (glob V) (glob W)),
    ((R1 ;; S1) @ (R2 ;; S2) = (R1 @ R2) ;; (S1 @ S2))%conv.
Proof.
  eauto using tconv_vcomp.
Qed.

(** **** Horizontal structural isomorphisms *)

(** XXX not sure if the left unitor makes that much sense here *)

Definition slu {U} : 1 @ U ->> glob U := tlu.
Definition slur {U} : glob U ->> 1 @ U := tlur.

Global Instance slu_iso {U} : @Isomorphism (1 @ U) (glob U) slu slur.
Proof.
  unfold slu, slur. split.
  - constructor. rewrite <- emor_strat_ecomp. setoid_rewrite tlu_tlur. auto.
  - constructor. rewrite <- emor_strat_ecomp. setoid_rewrite tlur_tlu. auto.
Qed.

Definition sru {E} : E @ unit ->> E := tru.
Definition srur {E} : E ->> E @ unit := trur.

Global Instance sru_iso {E} : @Isomorphism (E @ unit) E sru srur.
Proof.
  unfold sru, srur. split.
  - constructor. rewrite <- emor_strat_ecomp. setoid_rewrite tru_trur. auto.
  - constructor. rewrite <- emor_strat_ecomp. setoid_rewrite trur_tru. auto.
Qed.

Definition sassoc {E U V} : E @ U @ V ->> E @ (U * V) := @tassoc E (glob U) (glob V).
Definition sassocr {E U V} : E @ (U * V) ->> E @ U @ V := @tassocr E (glob U) (glob V).

Global Instance sassoc_iso {E U V}: Isomorphism (@sassoc E U V) (@sassocr E U V).
Proof.
  unfold sassoc, sassocr. split.
  - constructor. rewrite <- emor_strat_ecomp.
    setoid_rewrite (@tassoc_tassocr E (glob U) (glob V)). auto.
  - constructor. rewrite <- emor_strat_ecomp.
    setoid_rewrite (@tassocr_tassoc E (glob U) (glob V)). auto.
Qed.

(** **** Coherence diagrams *)

(** XXX could need some property that

      id @ bij_lens f = id ⊗ bij_emor f

 and reuse anything that uses the bijection f.
 The subtlety is that [bij_lens f] yields a nondeterministic strategy
 with all ask/answer choices whereas [bij_emor f] would yield a sig
 homomorphism style of strategy with the 4-move OQ PQ OA PA shape.
 But once synchronized with [id] the nondeterminism should reduce and
 leave only the 4 moves. *)

Open Scope strat_scope.
Coercion eid : esig >-> emor.
Coercion bid : Sortclass >-> bijection.

Lemma slu_passoc {E : esig} {U : Type} :
  E @ (@plu U) ⊙ (@sassoc E unit U) = (@sru E) @ U.
Proof.
Admitted.

Lemma sassoc_sassoc {E : esig} {U V W : Type} :
  @sassoc E U (V * W) ⊙ @sassoc (E @ U) V W =
  E @ (@passoc U V W) ⊙ @sassoc E (U * V) W ⊙ (@sassoc E U V) @ W.
Proof.
Admitted.

(** **** Additional properties of embedded structural isomorphisms *)

(** Naturality of [sru] *)

Lemma sru_natural {E F} (σ : E ->> F) :
  σ ⊙ sru = sru ⊙ (σ @ unit).
Proof.
Admitted.

Lemma srur_natural {E F} (σ : E ->> F) :
  srur ⊙ σ = (σ @ unit) ⊙ srur.
Proof.
  rewrite <- (compose_id_r (srur ⊙ σ)), <- (retraction sru).
  rewrite compose_assoc, <- !(compose_assoc _ _ srur). f_equal.
  rewrite <- (compose_id_l (σ @ unit)), <- (retraction srur).
  rewrite compose_assoc. f_equal.
  apply sru_natural.
Qed.
