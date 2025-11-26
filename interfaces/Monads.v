Require Import interfaces.Category.
Require Import interfaces.Functor.
Require Import interfaces.Adjunctions.


(** * Monad on a category *)

(** ** Definition *)

(** We follow the traditional category theory definition of equipping
  an endofunctor with unit and multiplication natural transformations.
  The "bind" operation (Kleisli extension) is derived from them in the
  theory module below. *)

Module Type MonadDefinition (C : CategoryDefinition).
  Include FunctorDefinition C C.

  Parameter eta : forall X, C.m X (omap X).
  Parameter mu : forall X, C.m (omap (omap X)) (omap X).

  Axiom eta_natural :
    forall {X Y} (f : C.m X Y),
      C.compose (eta Y) f = C.compose (fmap f) (eta X).

  Axiom mu_natural :
    forall {X Y} (f : C.m X Y),
      C.compose (mu Y) (fmap (fmap f)) = C.compose (fmap f) (mu X).

  Axiom mu_eta_l :
    forall X,
      C.compose (mu X) (eta (omap X)) = C.id (omap X).

  Axiom mu_eta_r :
    forall X,
      C.compose (mu X) (fmap (eta X)) = C.id (omap X).

  Axiom mu_mu :
    forall X,
      C.compose (mu X) (mu (omap X)) = C.compose (mu X) (fmap (mu X)).

End MonadDefinition.

(** ** General theory *)

Module MonadTheory (C : Category) (T : MonadDefinition C).
  Import T.

  (** ** Kleisli extension and its properties *)

  Definition ext {X Y} (f : C.m X (T.omap Y)) : C.m (T.omap X) (T.omap Y) :=
    C.compose (mu Y) (fmap f).

  Proposition ext_eta_l X :
    ext (eta X) = C.id (omap X).
  Proof.
    unfold ext.
    apply mu_eta_r.
  Qed.

  Proposition ext_eta_r {X Y} (f : C.m X (omap Y)) :
    C.compose (ext f) (eta X) = f.
  Proof.
    unfold ext.
    rewrite C.compose_assoc, <- eta_natural.
    rewrite <- C.compose_assoc, mu_eta_l.
    rewrite C.compose_id_left.
    reflexivity.
  Qed.

  Proposition ext_ext {X Y Z} (f : C.m X (omap Y)) (g : C.m Y (omap Z)) :
    C.compose (ext g) (ext f) = ext (C.compose (ext g) f).
  Proof.
    unfold ext.
    rewrite C.compose_assoc, <- (C.compose_assoc (fmap f)), <- mu_natural.
    repeat rewrite ?C.compose_assoc, ?fmap_compose.
    rewrite <- C.compose_assoc, mu_mu, C.compose_assoc.
    reflexivity.
  Qed.

  (** ** Kleisli category *)

  (** *** Definition *)

  Module Kl <: Category.
    Definition t := C.t.
    Definition m X Y := C.m X (T.omap Y).

    Definition id X := eta X.
    Definition compose {X Y Z} (g : m Y Z) (f : m X Y) := C.compose (ext g) f.

    Proposition compose_id_left {X Y} (f : m X Y) :
      compose (id Y) f = f.
    Proof.
      unfold compose, id.
      rewrite ext_eta_l, C.compose_id_left.
      reflexivity.
    Qed.

    Proposition compose_id_right {X Y} (f : m X Y) :
      compose f (id X) = f.
    Proof.
      unfold compose, id.
      rewrite ext_eta_r.
      reflexivity.
    Qed.

    Proposition compose_assoc {X Y Z T} (f : m X Y) (g : m Y Z) (h : m Z T) :
      compose (compose h g) f = compose h (compose g f).
    Proof.
      unfold compose.
      rewrite <- ext_ext, C.compose_assoc.
      reflexivity.
    Qed.

    Include CategoryTheory.
  End Kl.

  (** *** Adjunction between the base and Kleisli categories *)

  Module KlF <: Functor C Kl.

    Definition omap (X : C.t) : Kl.t := X.
    Definition fmap {X Y} (f : C.m X Y) : Kl.m X Y := C.compose (eta Y) f.

    Proposition fmap_id X :
      fmap (C.id X) = Kl.id X.
    Proof.
      unfold fmap, Kl.id.
      rewrite C.compose_id_right.
      reflexivity.
    Qed.

    Proposition fmap_compose {X Y Z} (g : C.m Y Z) (f : C.m X Y) :
      fmap (C.compose g f) = Kl.compose (fmap g) (fmap f).
    Proof.
      unfold fmap, Kl.compose.
      rewrite <- (C.compose_assoc f (eta Y)), ext_eta_r, C.compose_assoc.
      reflexivity.
    Qed.

    Include FunctorTheory C Kl.
  End KlF.

  Module KlU <: Functor Kl C.

    Definition omap (X : Kl.t) : C.t := T.omap X.
    Definition fmap {X Y} (f : Kl.m X Y) : C.m (omap X) (omap Y) := ext f.

    Proposition fmap_id X :
      fmap (Kl.id X) = C.id (omap X).
    Proof.
      unfold fmap, Kl.id.
      rewrite ext_eta_l.
      reflexivity.
    Qed.

    Proposition fmap_compose {X Y Z} (g : Kl.m Y Z) (f : Kl.m X Y) :
      fmap (Kl.compose g f) = C.compose (fmap g) (fmap f).
    Proof.
      unfold fmap, Kl.compose.
      rewrite ext_ext.
      reflexivity.
    Qed.

    Include FunctorTheory Kl C.
  End KlU.

  Module KlA <: AdjointFunctors C Kl KlF KlU.

    Definition unit A : C.m A (KlU.omap (KlF.omap A)) :=
      T.eta A.
    Definition counit X : Kl.m (KlF.omap (KlU.omap X)) X :=
      C.id (T.omap X).

    Proposition unit_natural {A V} (f : C.m A V) :
      C.compose (unit V) f = C.compose (KlU.fmap (KlF.fmap f)) (unit A).
    Proof.
      unfold unit, counit, KlU.fmap, KlF.fmap.
      rewrite ext_eta_r.
      reflexivity.
    Qed.

    Proposition counit_natural {X Y} (ϕ : Kl.m X Y) :
      Kl.compose (counit Y) (KlF.fmap (KlU.fmap ϕ)) = Kl.compose ϕ (counit X).
    Proof.
      unfold Kl.compose, counit, KlF.fmap, KlU.fmap, KlU.omap.
      rewrite <- C.compose_assoc, ext_eta_r.
      rewrite C.compose_id_left, C.compose_id_right.
      reflexivity.
    Qed.

    Proposition unit_counit X :
      C.compose (KlU.fmap (counit X)) (unit (KlU.omap X)) = C.id (KlU.omap X).
    Proof.
      unfold KlU.fmap, KlU.omap, unit, counit.
      rewrite ext_eta_r.
      reflexivity.
    Qed.

    Proposition counit_unit A :
      Kl.compose (counit (KlF.omap A)) (KlF.fmap (unit A)) = Kl.id (KlF.omap A).
    Proof.
      unfold Kl.compose, KlF.omap, KlF.fmap, Kl.id, unit, counit.
      rewrite <- C.compose_assoc.
      rewrite ext_eta_r, C.compose_id_left.
      reflexivity.
    Qed.

    Include AdjointFunctorsTheory C Kl KlF KlU.
  End KlA.

End MonadTheory.

Module Type Monad (C : Category) :=
  MonadDefinition C <+
  MonadTheory C.


(** * Monads on concrete categories *)

(** We can give specialized for the special case of concrete
  categories, where objects are sets with additional structure,
  we can provide some additional tools. *)

Require Import ConcreteCategory.

(** ** Definition *)

(** XXX it's probably much easier in general to define monads on [Set]
  and other concrete categories using bind + ret and minimal
  conditions to establish the required functoriality and naturality
  properties.*)

(** ** Theory *)

Module ConcreteMonadTheory (C : ConcreteCategory) (T : Monad C).

  Notation "'do' x <- t ;; f" := (C.apply (T.ext (fun x => f)) t)
    (right associativity, x binder, at level 60).

  Notation ret := (C.apply (T.eta _)).

  (** Could add here: rewrite database, etc. *)

End ConcreteMonadTheory.

Module Type ConcreteMonad (C : ConcreteCategory) :=
  Monad C <+
  ConcreteMonadTheory C.


(** * Monads on [Set] *)

(** It could be useful here to specialize [ConcreteMonadDefinition] to the
  case where [C := Set] so that we're not encumbered by the trivial
  "extra structure" carried by plain sets. *)
