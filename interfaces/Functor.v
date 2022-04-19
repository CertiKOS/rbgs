Require Import interfaces.Category.


(** * Functors *)

Module Type Functor (C D : CategoryDefinition).

  Parameter omap : C.t -> D.t.
  Parameter fmap : forall {A B}, C.m A B -> D.m (omap A) (omap B).

  Axiom fmap_id :
    forall A, fmap (C.id A) = D.id (omap A).

  Axiom fmap_compose :
    forall {A B C} (g : C.m B C) (f : C.m A B),
      fmap (C.compose g f) = D.compose (fmap g) (fmap f).

End Functor.


(** * Bifunctors *)

(** ** Definition *)

Module Type BifunctorDefinition (C1 C2 D : CategoryDefinition).

  Parameter omap : C1.t -> C2.t -> D.t.

  Parameter fmap :
    forall {A1 A2 B1 B2},
      C1.m A1 B1 -> C2.m A2 B2 -> D.m (omap A1 A2) (omap B1 B2).

  Axiom fmap_id :
    forall A1 A2, fmap (C1.id A1) (C2.id A2) = D.id (omap A1 A2).

  Axiom fmap_compose :
    forall {A1 A2 B1 B2 C1 C2},
      forall (g1 : C1.m B1 C1) (g2 : C2.m B2 C2) (f1 : C1.m A1 B1) (f2 : C2.m A2 B2),
        fmap (C1.compose g1 f1) (C2.compose g2 f2) =
          D.compose (fmap g1 g2) (fmap f1 f2).

End BifunctorDefinition.

(** ** Properties *)

Module BifunctorTheory (C1 C2 D : CategoryDefinition) (F : BifunctorDefinition C1 C2 D).

  (** A bifunctor can be seen as a functor from the product category. *)

  Module PC := Prod C1 C2.

  Module PF <: Functor PC D.

    Definition omap (X : PC.t) : D.t :=
      F.omap (fst X) (snd X).

    Definition fmap {A B} (f : PC.m A B) : D.m (omap A) (omap B) :=
      F.fmap (fst f) (snd f).

    Proposition fmap_id {A} :
      fmap (PC.id A) = D.id (omap A).
    Proof.
      apply F.fmap_id.
    Qed.

    Proposition fmap_compose {A B C} (g : PC.m B C) (f : PC.m A B) :
      fmap (PC.compose g f) = D.compose (fmap g) (fmap f).
    Proof.
      apply F.fmap_compose.
    Qed.
      
  End PF.

End BifunctorTheory.

(** ** Bundled interface *)

Module Type Bifunctor (C1 C2 D : CategoryDefinition).
  Include BifunctorDefinition C1 C2 D.
  Include BifunctorTheory C1 C2 D.
End Bifunctor.
