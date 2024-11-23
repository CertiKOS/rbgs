Require Export interfaces.Category.
Require Import FunctionalExtensionality.
Require Import ProofIrrelevance.


(** * Mathematical structures and enrichment *)

(** Our development uses a variety of mathematical structures,
  for example various notions of partial orders. Specifications
  of models can then require that they be equipped with these
  structures in a systemactic way. *)


(** * Concrete categories *)

(** Mathematical structures are formalized following a limited
  unbundled approach, which allows the underlying sets and
  functions to be manipulated in an unintrusive way.
  We will define an instance of the following module type for each
  kind of structure we want to formalize (poset, lattice, etc.) *)

(** ** Definition *)

Module Type ConcreteCategoryDefinition.

  (** First, we must define a typeclass which provides the extra
    structure for a given set. This should consist of any constants,
    operations and relations for the structure of interest, together
    with the axioms they must satisfy. *)

  Parameter Structure : Type -> Type.
  Existing Class Structure.

  (** Then, we must give the properties satisfied by structure-
    preserving functions. These properties should be satisfied by
    identity functions and preserved by composition. *)

  Parameter Morphism : forall {A B} `{Structure A} `{Structure B}, (A -> B) -> Prop.
  Existing Class Morphism.

  Axiom id_mor :
    forall `{Structure}, Morphism (fun x => x).

  Axiom compose_mor :
    forall {A B C} `{Structure A} `{Structure B} `{Structure C} (g: B -> C) (f: A -> B),
      Morphism g ->
      Morphism f ->
      Morphism (fun x => g (f x)).

  Global Existing Instance id_mor.
  Global Existing Instance compose_mor.

End ConcreteCategoryDefinition.

(** ** Theory *)

Module Type ConcreteCategoryTheory (C : ConcreteCategoryDefinition) <: Category.

  (** The unbundled form of mathematical structures is flexible, for
    example we use it below to formulate enrichment as a supplementary
    structure on an existing category. However we can also derive a
    bundled form to use in cases where the unbundled form is too
    cumbersome, and to equip a [ConcreteCategory] with the standard
    [Category] interface. *)

  (** *** Objects *)

  Record structured_set :=
    mkt {
      carrier :> Type;
      structure : C.Structure carrier
    }.

  Arguments mkt _ {_}.
  Global Existing Instance structure.

  Definition t := structured_set.
  Identity Coercion tss : t >-> structured_set.

  (** *** Morphisms *)

  Record structured_map (A B : t) :=
    mkm {
      apply :> A -> B;
      morphism : C.Morphism apply
    }.

  Arguments mkm {_ _} _ {_}.
  Global Existing Instance morphism.

  Definition m A B := structured_map A B.
  Identity Coercion msm : m >-> structured_map.

  Lemma meq {A B} (f g : m A B) :
    (forall x, f x = g x) -> f = g.
  Proof.
    destruct f as [f Hf], g as [g Hg]; cbn. intros.
    assert (f = g) by (apply functional_extensionality; auto); subst.
    f_equal. apply proof_irrelevance.
  Qed.

  (** *** Composition *)

  Definition id A : m A A :=
    mkm (fun x => x).

  Definition compose {A B C} (g : m B C) (f : m A B) : m A C :=
    mkm (fun x => g (f x)).

  Lemma compose_id_left {A B} (f : m A B) :
    compose (id B) f = f.
  Proof.
    apply meq; reflexivity.
  Qed. 

  Lemma compose_id_right {A B} (f : m A B) :
    compose f (id A) = f.
  Proof.
    apply meq; reflexivity.
  Qed.

  Lemma compose_assoc {A B C D} (f : m A B) (g : m B C) (h : m C D) :
    compose (compose h g) f = compose h (compose g f).
  Proof.
    apply meq; reflexivity.
  Qed.

  (** *** Derived constructions *)

  Include CategoryTheory.

End ConcreteCategoryTheory.

(** ** Overall interface *)

Module Type ConcreteCategory :=
  ConcreteCategoryDefinition <+
  ConcreteCategoryTheory.


(** * Basic instances *)

(** The simplest one possible is the category of sets and functions,
  where the structure and properties of morphisms are both trivial.
  Note however that this gives an overly contrived definition for
  [SET.t] and [SET.m], so we may want to define an instance of
  [Category] directly where they would be convertible with [Type]
  and function types. *)

Module SET <: ConcreteCategory.

  Definition Structure (X : Type) := unit.
  Existing Class Structure.

  Definition Morphism {A B} `{Structure A} `{Structure B} (f : A -> B) := True.
  Existing Class Morphism.

  Global Instance id_mor `{Structure} :
    Morphism (fun x => x).
  Proof.
    constructor.
  Qed.

  Global Instance compose_mor {A B C} `{Structure A} `{Structure B} `{Structure C} :
    forall (g : B -> C) (f : A -> B),
      Morphism g ->
      Morphism f ->
      Morphism (fun x => g (f x)).
  Proof.
    constructor.
  Qed.

  Include ConcreteCategoryTheory.

End SET.


(** * Enrichment *)

(** Although the full-blown definition of enriched category would
  require duplicating the [Category] interface among other things,
  by restricting it to concrete categories we can easily define
  enrichment as an add-on to the basic interface. Likewise, for the
  sake of simplicity we can specify composition as a bimorphism
  instead of using a general monoidal structure. *)

Module Type Enriched (V : ConcreteCategoryDefinition) (C : CategoryDefinition).

  Parameter hom_structure : forall (X Y : C.t), V.Structure (C.m X Y).
  Global Existing Instance hom_structure.

  Axiom compose_mor_l :
    forall {A B C} (f : C.m A B),
      V.Morphism (fun g : C.m B C => C.compose g f).

  Axiom compose_mor_r :
    forall {A B C} (g : C.m B C),
      V.Morphism (fun f : C.m A B => C.compose g f).

End Enriched.
