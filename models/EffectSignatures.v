Require Import interfaces.Category.
Require Import interfaces.FunctorCategory.
Require Import interfaces.Functor.
Require Import FunctionalExtensionality.


(** * Effect signatures *)

(** Category of effect signatures and their homomorphisms.
  This is also known as [Poly] and corresponds to one common
  definition of polynomial endofunctors on [Set]. Here we
  choose to adopt the more algebraic view and terminology
  which is prevalent in computer science applications. *)

Module Sig <: Category.

  (** ** Definition *)

  (** For now we adopt the dependent type presentation of
    effect signatures used in the interaction trees library,
    where in a signature [E : Type -> Type] the set [E N]
    contains the operations with an arity set [N]. It may
    prove easier to use an alternative presentation with a
    flat set of operations and a separate arity operation,
    as can be found in other parts of this library. *)

  Definition t := Type -> Type.

  (** For now we provide the set [op] and arity map [ar]
    as derived constructions. *)

  Record op {E : t} :=
    mkop {
      ar : Type;
      eop : E ar;
    }.

  Arguments op : clear implicits.

  (** ** Applications *)

  (** The following type encodes simple terms of the form
    [m(x_n)_{n∈ar(m)}] consisting of an operation [m] of [E]
    with arguments [x_n] taken in the set [X]. In other words,
    this is the type [∑m∈E · ∏n∈ar(m) · X] *)

  Record application {E : t} {X : Type} :=
    apply {
      operator : op E;
      operand : ar operator -> X;
    }.

  Arguments application : clear implicits.
  Arguments apply {E X} _ _.

  (** We will sometimes use the following notation for simple terms,
    which evokes the game/effects interpretation of signatures. *)

  Notation "m >= n => x" :=
    {| operator := m; operand n := x |}
    (at level 70, n at next level).

  (** We can transform an application by using a given function
    on every argument. *)

  Definition amap {E : t} {X Y} (f : X -> Y) : application E X -> application E Y :=
    fun '(apply m x) => (m >= n => f (x n)).

  (** This forms the morphism part of a [Set] endofunctor
    associated with [application E], as shown below. *)

  Lemma amap_id {E : t} {X} (u : application E X) :
    amap (fun x => x) u = u.
  Proof.
    destruct u; reflexivity.
  Qed.

  Lemma amap_compose {E : t} {X Y Z} (g : Y -> Z) (f : X -> Y) (u : application E X) :
    amap g (amap f u) = amap (fun x => g (f x)) u.
  Proof.
    destruct u; reflexivity.
  Qed.

  (** ** Homomorphisms *)

  (** A homomorphism between signatures maps operations forward 
    and outcomes (argument positions) backward. We can use the
    definitions above to formalize this in the following way:
    for each operation of [E], we give a simple term in [F],
    and the arguments used in this term refer back to the valid
    argument positions for the operation of [E]. *)

  Definition m (E F : t) :=
    forall (m : op E), application F (ar m).

  (** Signature homomorphisms can be used to transform simple terms
    of the signature [E] into simple terms of the signature [F]. *)

  Definition hmap {E F} (ϕ : m E F) X : application E X -> application F X :=
    fun '(apply m x) => amap x (ϕ m).

  (** So whereas [amap f : application E X -> application E Y] acts
    on the arguments, [hmap φ : application E X -> application F X]
    acts on structure of the term (operator and argument positions).
    The structure and arguments can be transformed independently:
    the result will be the same no matter which one we tranform first. *)

  Lemma hmap_natural {E F} (ϕ : m E F) {X Y} (f : X -> Y) (u : application E X) :
    amap f (hmap ϕ X u) = hmap ϕ Y (amap f u).
  Proof.
    destruct u as [m x]; cbn.
    apply amap_compose.
  Qed.

  (** In fact, [application], [amap] and [hmap] together define a
    functor from the category of signatures and signature homomorphisms
    to the category of endofunctors on Set and natural transformations. *)

  (** ** Compositional structure *)

  Definition id E : m E E :=
    fun m => m >= n => n.

  Definition compose {E F G} (ψ : m F G) (ϕ : m E F) : m E G :=
    fun m => hmap ψ _ (ϕ m).

  Lemma hmap_id {E : t} :
    forall X u, hmap (@id E) X u = u.
  Proof.
    destruct u as [m k].
    reflexivity.
  Qed.

  Lemma hmap_compose {E F G} (ψ : m F G) (ϕ : m E F) :
    forall X t, hmap (compose ψ ϕ) X t = hmap ψ X (hmap ϕ X t).
  Proof.
    intros X [m x]; cbn.
    apply hmap_natural.
  Qed.

  Lemma compose_id_left {E F} (ϕ : m E F) :
    compose (id F) ϕ = ϕ.
  Proof.
    apply functional_extensionality_dep; intros m.
    unfold compose.
    apply hmap_id.
  Qed.

  Lemma compose_id_right {E F} (ϕ : m E F) :
    compose ϕ (id E) = ϕ.
  Proof.
    apply functional_extensionality_dep; intros m.
    unfold compose; cbn.
    apply amap_id.
  Qed.

  Lemma compose_assoc {E F G H} (ϕ: m E F) (ψ: m F G) (θ: m G H) :
    compose (compose θ ψ) ϕ = compose θ (compose ψ ϕ).
  Proof.
    apply functional_extensionality_dep; intros m.
    unfold compose.
    apply hmap_compose.
  Qed.

  Include CategoryTheory.
End Sig.

(** TODO:
    - products and coproducts
    - tensor product
    - composition product / before
    - dual
 *)


(** * Interpretation in [SET] endofunctors *)

Module SigEnd <: FullAndFaithfulFunctor Sig (SET.End).
  Import (notations) Sig.
  Import (coercions) SET.End.

  (** As mentioned above, effect signatures can be interpreted
    as polynomial endofunctors on [SET]. Here we formalize this
    interpretation as an official functor. *)

  Program Definition omap (E : Sig.t) : SET.End.t :=
    {|
      SET.End.oapply := Sig.application E;
      SET.End.fapply X Y f := Sig.amap f;
    |}.
  Next Obligation.
    apply functional_extensionality. intro a.
    apply Sig.amap_id.
  Qed.
  Next Obligation.
    apply functional_extensionality. intro a.
    unfold SET.compose.
    rewrite Sig.amap_compose.
    reflexivity.
  Qed.

  Program Definition fmap {E F} (f : Sig.m E F) : SET.End.m (omap E) (omap F) :=
    {|
      SET.End.comp := Sig.hmap f;
    |}.
  Next Obligation.
    apply functional_extensionality. intros x.
    unfold SET.compose.
    rewrite Sig.hmap_natural.
    reflexivity.
  Qed.

  Proposition fmap_id E :
    fmap (Sig.id E) = SET.End.id (omap E).
  Proof.
    apply SET.End.meq. intro X. cbn.
    apply functional_extensionality. intro x.
    apply Sig.hmap_id.
  Qed.

  Proposition fmap_compose {A B C} (g : Sig.m B C) (f : Sig.m A B) :
    fmap (Sig.compose g f) = SET.End.compose (fmap g) (fmap f).
  Proof.
    apply SET.End.meq. intro X. cbn.
    apply functional_extensionality. intro x.
    apply Sig.hmap_compose.
  Qed.

  (** Every natural transformation between endofunctors derived from
    signatures is completely determined by its action on the terms
    [m >= n => n], so the functor is full and faithful. *)

  Proposition full {E F} (η : SET.End.m (omap E) (omap F)) :
    exists f, fmap f = η.
  Proof.
    exists (fun m => η (Sig.ar m) (m >= n => n)).
    apply SET.End.meq. intros X. cbn.
    apply functional_extensionality. intros u.
    destruct u as [m k]. cbn. symmetry.
    apply (SET.natural η k (m >= n => n)).
  Qed.

  Proposition faithful {E F} (f g : Sig.m E F) :
    fmap f = fmap g -> f = g.
  Proof.
    intros H.
    apply functional_extensionality_dep. intros m.
    assert (Hm : fmap f _ (m >= n => n) = fmap g _ (m >= n => n)) by congruence.
    cbn in Hm. destruct (f m), (g m). assumption.
  Qed.

End SigEnd.
