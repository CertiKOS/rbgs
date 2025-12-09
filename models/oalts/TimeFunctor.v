Require Import interfaces.Category.
Require Import interfaces.Functor.
Require Import interfaces.MonoidalCategory.
Require Import interfaces.Limits.

(** * Time Functor: AsyncEvent × C → C *)

(** C must be bicartesian (both cartesian and cocartesian) *)
Module TimeFunctor (C : BicartesianCategory) (T : Terminals C)
  (Ev : AsyncEvents C T) <: BifunctorDefinition Ev C C.

  Import C.
  Open Scope obj_scope.

  (** ** Object mapping *)
  (** Maps an event type E : Ev.t and an object X : C.t to C.t *)
  Definition omap (E : Ev.t) (X : C.t) : C.t :=
    (* TODO: Define your construction here *)
    (* Now you can use both products (E && X) and coproducts (E + X) *)
    E && X.  (* placeholder - product of E and X *)

  (** ** Morphism mapping *)
  (** Maps e : Ev.m E1 E2 (a Kleisli morphism) and f : C.m X1 X2
      to a morphism C.m (omap E1 X1) (omap E2 X2) *)
  Definition fmap {E1 E2 : Ev.t} {X1 X2 : C.t}
    (e : Ev.m E1 E2) (f : C.m X1 X2) : C.m (omap E1 X1) (omap E2 X2) :=
    (* TODO: Define your construction here *)
    (* e : C.m E1 (Ev.L.omap E2) = C.m E1 (T.unit + E2) is a Kleisli morphism *)
    (* f : C.m X1 X2 is a regular morphism *)
    (* You need to produce C.m (E1 && X1) (E2 && X2) *)
    Prod.pair (Ev.L.KlU.fmap e @ Prod.p1) (f @ Prod.p2).  (* placeholder *)

  (** ** Functor laws *)

  Proposition fmap_id : forall E X,
    fmap (Ev.id E) (C.id X) = C.id (omap E X).
  Proof.
    intros.
    (* TODO: Prove identity preservation *)
  Admitted.

  Proposition fmap_compose :
    forall {E1 E2 E3 : Ev.t} {X1 X2 X3 : C.t}
      (e2 : Ev.m E2 E3) (e1 : Ev.m E1 E2)
      (f2 : C.m X2 X3) (f1 : C.m X1 X2),
    fmap (Ev.compose e2 e1) (C.compose f2 f1) =
      C.compose (fmap e2 f2) (fmap e1 f1).
  Proof.
    intros.
    (* TODO: Prove composition preservation *)
  Admitted.

End TimeFunctor.

(** Include the derived theory *)
Module TimeFunctorWithTheory (C : BicartesianCategory) (T : Terminals C)
  (Ev : AsyncEvents C T) <: Bifunctor Ev C C.

  Include TimeFunctor C T Ev.
  Include BifunctorTheory Ev C C.

End TimeFunctorWithTheory.
