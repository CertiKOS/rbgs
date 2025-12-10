Require Import interfaces.Category.
Require Import interfaces.Functor.
Require Import interfaces.MonoidalCategory.
Require Import interfaces.Limits.
Require Import models.oalts.AsyncEvent.

(** * Time Functor: AsyncEvent × C → C *)

(** C must be bicartesian (both cartesian and cocartesian) *)
Module TimeFunctorDefinition (C : BicartesianCategory) (T : Terminals C)
  (Ev : AsyncEvents C T) <: BifunctorDefinition Ev C C.

  Definition omap (E : Ev.t) (S : C.t) : C.t := C.Prod.omap (Ev.L.omap E) S.

  Definition fmap {E1 : Ev.t} {X1 : C.t} {E2 : Ev.t} {X2 : C.t}
    (e : Ev.m E1 E2) (f : C.m X1 X2) : C.m (omap E1 X1) (omap E2 X2) :=
    C.Prod.fmap (Ev.L.KlU.fmap e) f.

  Proposition fmap_id : forall E X,
    fmap (Ev.id E) (C.id X) = C.id (omap E X).
  Proof.
    intros. unfold fmap. rewrite Ev.L.KlU.fmap_id. rewrite C.Prod.fmap_id.
    reflexivity.
  Qed.

  Proposition fmap_compose :
    forall {A1 : Ev.t} {A2 : C.t} {B1 : Ev.t} {B2 : C.t} {C1 : Ev.t} {C2 : C.t}
      (g1 : Ev.m B1 C1) (g2 : C.m B2 C2) (f1 : Ev.m A1 B1) (f2 : C.m A2 B2),
    fmap (Ev.compose g1 f1) (C.compose g2 f2) =
      C.compose (fmap g1 g2) (fmap f1 f2).
  Proof.
    intros. unfold fmap. rewrite Ev.L.KlU.fmap_compose.
    rewrite C.Prod.fmap_compose. reflexivity.
  Qed.

End TimeFunctorDefinition.

(** Include the derived theory *)
Module TimeFunctor (C : BicartesianCategory) (T : Terminals C)
  (Ev : AsyncEvents C T) <: Bifunctor Ev C C.

  Include TimeFunctorDefinition C T Ev.
  Include BifunctorTheory Ev C C.

End TimeFunctor.