Require Import interfaces.Category.
Require Import interfaces.Functor.
Require Import models.DCPO.

Module Type DCPOCategoryDefinition <: CategoryDefinition.
    Declare Module C : CategoryDefinition.
    Include C.

    Parameter hom_dcpo : forall A B, DirectedComplete (m A B).

    Parameter compose_continuous_l : forall A B C (g : m B C),
        @ScottContinuous _ _ (hom_dcpo A B) (@dc_po _ (hom_dcpo A C)) (fun f => compose g f).

    Parameter compose_continuous__r : forall A B C (f : m A B),
        @ScottContinuous _ _ (hom_dcpo B C) (@dc_po _ (hom_dcpo A C)) (fun g => compose g f).
End DCPOCategoryDefinition.

Module DCPOCategoryTheory (C : DCPOCategoryDefinition).
    Include CategoryTheory C.
End DCPOCategoryTheory.

Module Type DCPOCategory.
  Include DCPOCategoryDefinition.
  Include DCPOCategoryTheory.
End DCPOCategory.

(** Scott-continuous bifunctors for DCPO-enriched categories *)

Module Type DCPOBifunctorDefinition
  (C1 : DCPOCategoryDefinition) (C2 : DCPOCategoryDefinition) (D : DCPOCategoryDefinition).

  Declare Module F : BifunctorDefinition C1 C2 D.
  Include F.

  (** fmap is Scott-continuous in the first argument *)
  Parameter fmap_continuous_l :
    forall {A1 A2 B1 B2} (f2 : C2.m A2 B2),
      @ScottContinuous _ _
        (C1.hom_dcpo A1 B1)
        (@dc_po _ (D.hom_dcpo (omap A1 A2) (omap B1 B2)))
        (fun f1 => fmap f1 f2).

  (** fmap is Scott-continuous in the second argument *)
  Parameter fmap_continuous_r :
    forall {A1 A2 B1 B2} (f1 : C1.m A1 B1),
      @ScottContinuous _ _
        (C2.hom_dcpo A2 B2)
        (@dc_po _ (D.hom_dcpo (omap A1 A2) (omap B1 B2)))
        (fun f2 => fmap f1 f2).

End DCPOBifunctorDefinition.

Module DCPOBifunctorTheory (C1 C2 D : DCPOCategory) (F : DCPOBifunctorDefinition C1 C2 D).
  Include BifunctorTheory C1 C2 D F.

End DCPOBifunctorTheory.

Module Type DCPOBifunctor (C1 C2 D : DCPOCategory).
  Include DCPOBifunctorDefinition C1 C2 D.
  Include DCPOBifunctorTheory C1 C2 D.
End DCPOBifunctor.
