Require Import Coq.Lists.List.
Import ListNotations.

(** A small typed kappa-calculus skeleton (first-order internal language)
    using de Bruijn variables for ground constants. *)

Module Kappa.

  (** Types: unit and binary products only. *)
  Inductive kty :=
  | kunit
  | kprod (A B : kty).

  Notation "A × B" := (kprod A B) (at level 40).

  (** Variables for ground constants of type [1 -> A]. *)
  Inductive var : list kty -> kty -> Type :=
  | vz A Γ : var (A :: Γ) A
  | vs A B Γ : var Γ A -> var (B :: Γ) A.

  (** Terms are morphisms [A -> B] with constants in [Γ]. *)
  Inductive term : list kty -> kty -> kty -> Type :=
  | tid Γ A : term Γ A A
  | tbang Γ A : term Γ A kunit
  | tcomp Γ A B C : term Γ A B -> term Γ B C -> term Γ A C
  | tlift Γ A B : term Γ kunit A -> term Γ B (A × B)
  | tvar Γ A : var Γ A -> term Γ kunit A
  | tkappa Γ A B C : term (A :: Γ) B C -> term Γ (A × B) C.

  Arguments tid {Γ A}.
  Arguments tbang {Γ A}.
  Arguments tcomp {Γ A B C} _ _.
  Arguments tlift {Γ A B} _.
  Arguments tvar {Γ A} _.
  Arguments tkappa {Γ A B C} _.

  Notation "f ∘ g" := (tcomp g f) (at level 40, left associativity).

  (** Example: drop the unit component from a pair. *)
  Definition drop_unit {Γ A} : term Γ (A × kunit) A :=
    tkappa (tvar (vz A Γ)).

End Kappa.
