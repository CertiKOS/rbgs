Require Import interfaces.Category.
Require Import interfaces.ConcreteCategory.
Require Import interfaces.MonoidalCategory.
Require Import interfaces.Functor.

(** * Concrete cartesian categories *)

(** We generally expect products in concrete categories to use
  products of underlying sets. When that is the case, the cartesian
  structure can be defined using the following data. *)

(** ** Definition *)

Module Type ConcreteCartesianDefinition (C : ConcreteCategoryDefinition).

  Axiom unit_structure :
    C.Structure unit.

  Axiom prod_structure :
    forall {A B : Type},
      C.Structure A ->
      C.Structure B ->
      C.Structure (A * B).

  Global Existing Instances unit_structure prod_structure.

  Axiom ter_mor :
    forall {A} `{Astruct : !C.Structure A},
      C.Morphism (A := A) (B := unit) (fun _ => tt).

  Axiom fst_mor :
    forall {A B} `{Astruct : !C.Structure A} `{Bstruct : !C.Structure B},
      C.Morphism (@fst A B).

  Axiom snd_mor :
    forall {A B} `{Astruct : !C.Structure A} `{Bstruct : !C.Structure B},
      C.Morphism (@snd A B).

  Axiom pair_mor :
    forall {X A B} `{Xstruct : !C.Structure X}
                   `{Astruct : !C.Structure A}
                   `{Bstruct : !C.Structure B} (f : X -> A) (g : X -> B),
      C.Morphism f ->
      C.Morphism g ->
      C.Morphism (fun x => (f x, g x)).

  Global Existing Instances ter_mor fst_mor snd_mor pair_mor.

End ConcreteCartesianDefinition.

(** ** Theory *)

Module ConcreteCartesianStructure
  (C : ConcreteCategory)
  (M : ConcreteCartesianDefinition C) <: CartesianStructure C.

  Import C.

  (** Terminal object and morphisms *)

  Canonical Structure unit : C.t :=
    C.mkt Datatypes.unit.

  Definition ter X : C.m X unit :=
    C.mkm (A := X) (B := unit) (fun _ => tt).

  Proposition ter_uni {X} (f g : C.m X unit) :
    f = g.
  Proof.
    apply C.meq. intros x.
    repeat destruct (C.apply X).
    reflexivity.
  Qed.

  (** Product and projections *)

  Canonical Structure omap (A B : C.t) : C.t :=
    C.mkt (C.carrier A * C.carrier B).

  Definition p1 {A B} : C.m (omap A B) A :=
    C.mkm fst.

  Definition p2 {A B} : C.m (omap A B) B :=
    C.mkm snd.

  Definition pair {X A B} (f : C.m X A) (g : C.m X B) : C.m X (omap A B) :=
    C.mkm (fun x => (f x, g x)).

  Proposition p1_pair {X A B} (f : C.m X A) (g : C.m X B) :
    p1 @ pair f g = f.
  Proof.
    apply C.meq.
    reflexivity.
  Qed.

  Proposition p2_pair {X A B} (f : C.m X A) (g : C.m X B) :
    p2 @ pair f g = g.
  Proof.
    apply C.meq.
    reflexivity.
  Qed.

  Proposition pair_pi {X A B} f :
    @pair X A B (p1 @ f) (p2 @ f) = f.
  Proof.
    apply C.meq. intro x. cbn.
    destruct (f x). reflexivity.
  Qed.

  Include CartesianStructureTheory C.
  Include BifunctorTheory C C C.

End ConcreteCartesianStructure.

(** We can now implement the [Cartesian] interface. *)

Module ConcreteCartesianTheory
  (C : ConcreteCategory)
  (M : ConcreteCartesianDefinition C) <: Cartesian C.

  Module Prod <: MonoidalStructure C :=
    ConcreteCartesianStructure C M.

  Include CartesianTheory C.

End ConcreteCartesianTheory.

(** A concrete category [C] is [ConcreteCartesian] when it has a
  cartesian structure that has been defined in this way. *)

Module Type ConcreteCartesian (C : ConcreteCategory) <: Cartesian C :=
  ConcreteCartesianDefinition C <+
  ConcreteCartesianTheory C.
