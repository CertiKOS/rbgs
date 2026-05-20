Require Import interfaces.Category.
Require Import interfaces.Functor.
Require Import interfaces.Adjunctions.


(** * Defining monads *)

(** Below we provide two possible ways to define a monad
  and show that they are equivalent. Both involve
  an object map [M : C.t -> C.t] together with
  a unit morphism [η : ∀ X · X → M X]. *)

(** ** Full interface *)

(** The interface below has some redundant axioms, but
  it is not expected to be the usual way to define a monad.
  Rather, it will be constructed using one of the two options
  below where the chosen half of the interface is defined,
  and the other half is derived. *)

Module Type MonadDefinition (C : Category).
  Import (notations) C.

  Include Functor.Functor C C.

  Parameter eta : forall X, X ~~> omap X.
  Parameter mu : forall X, omap (omap X) ~~> omap X.
  Parameter ext : forall {X Y}, (X ~~> omap Y) -> (omap X ~~> omap Y).

  Axiom eta_natural :
    forall {X Y} (f : X ~~> Y),
      eta Y @ f = fmap f @ eta X.

  Axiom mu_natural :
    forall {X Y} (f : X ~~> Y),
      mu Y @ fmap (fmap f) = fmap f @ mu X.

  (** Properties of [ext] *)

  Axiom ext_eta :
    forall {X Y} (f : C.m X (omap Y)),
      ext f @ eta X = f.

  Axiom eta_ext :
    forall X,
      ext (eta X) = C.id (omap X).

  Axiom ext_ext :
    forall {X Y Z} (g : Y ~~> omap Z) (f : X ~~> omap Y),
      ext g @ ext f = ext (ext g @ f).

  (** Properties of [mu] and [fmap] *)

  Axiom mu_eta_l :
    forall X,
      mu X @ eta (omap X) = C.id (omap X).

  Axiom mu_eta_r :
    forall X,
      mu X @ fmap (eta X) = C.id (omap X).

  Axiom mu_mu :
    forall X,
      mu X @ mu (omap X) = mu X @ fmap (mu X).

  (** Property relating the two approaches. *)

  Axiom ext_spec :
    forall {X Y} (f : X ~~> omap Y),
      ext f = mu Y @ fmap f.

End MonadDefinition.

(** ** By the Kleisli extension operator *)

(** The more compact approach is then to define
  the Kleisli extension operator and show that
  it satisfies some basic properties. *)

Module Type KleisliMonadDefinition (C : Category).
  Import (notations) C.

  Parameter omap : C.t -> C.t.
  Parameter eta : forall X, X ~~> omap X.
  Parameter ext : forall {X Y}, (X ~~> omap Y) -> (omap X ~~> omap Y).

  Axiom ext_eta :
    forall {X Y} (f : C.m X (omap Y)),
      ext f @ eta X = f.

  Axiom eta_ext :
    forall X,
      ext (eta X) = C.id (omap X).

  Axiom ext_ext :
    forall {X Y Z} (g : Y ~~> omap Z) (f : X ~~> omap Y),
      ext g @ ext f = ext (ext g @ f).

End KleisliMonadDefinition.

(** This allows us to define both the multiplication and
  the morphism part of the functor. *)

Module ExpandKleisliMonadDefinition (C : Category) (T : KleisliMonadDefinition C).
  Import (notations) C.

  Definition fmap {X Y} (f : X ~~> Y) : T.omap X ~~> T.omap Y :=
    T.ext (T.eta Y @ f).

  Definition mu X : T.omap (T.omap X) ~~> T.omap X :=
    T.ext (C.id (T.omap X)).

  Lemma fmap_id X :
    fmap (C.id X) = C.id (T.omap X).
  Proof.
    unfold fmap.
    rewrite C.compose_id_right.
    rewrite T.eta_ext.
    reflexivity.
  Qed.

  Lemma fmap_compose {X Y Z} (g : Y ~~> Z) (f : X ~~> Y) :
    fmap (g @ f) = fmap g @ fmap f.
  Proof.
    unfold fmap.
    rewrite T.ext_ext. f_equal.
    rewrite <- (C.compose_assoc _ (T.eta Y)), T.ext_eta, C.compose_assoc.
    reflexivity.
  Qed.

  Lemma eta_natural {X Y} (f : C.m X Y) :
    T.eta Y @ f = fmap f @ T.eta X.
  Proof.
    unfold fmap.
    rewrite T.ext_eta.
    reflexivity.
  Qed.

  Lemma mu_natural {X Y} (f : C.m X Y) :
    mu Y @ fmap (fmap f) = fmap f @ mu X.
  Proof.
    unfold fmap, mu.
    rewrite !T.ext_ext.
    rewrite <- (C.compose_assoc _ (T.eta (T.omap Y))), T.ext_eta.
    rewrite C.compose_id_left, C.compose_id_right.
    reflexivity.
  Qed.

  Lemma mu_eta_l X :
    mu X @ T.eta (T.omap X) = C.id (T.omap X).
  Proof.
    unfold mu.
    rewrite T.ext_eta.
    reflexivity.
  Qed.

  Lemma mu_eta_r X :
    mu X @ fmap (T.eta X) = C.id (T.omap X).
  Proof.
    unfold fmap, mu.
    rewrite T.ext_ext.
    rewrite <- C.compose_assoc, T.ext_eta, C.compose_id_left.
    rewrite T.eta_ext.
    reflexivity.
  Qed.

  Lemma mu_mu X :
    mu X @ mu (T.omap X) = mu X @ fmap (mu X).
  Proof.
    unfold fmap, mu.
    rewrite !T.ext_ext.
    rewrite <- C.compose_assoc, T.ext_eta.
    rewrite C.compose_id_left, C.compose_id_right.
    reflexivity.
  Qed.

  Lemma ext_spec {X Y} (f : X ~~> T.omap Y) :
    T.ext f = mu Y @ fmap f.
  Proof.
    unfold fmap, mu.
    rewrite T.ext_ext.
    rewrite <- C.compose_assoc, T.ext_eta, C.compose_id_left.
    reflexivity.
  Qed.

End ExpandKleisliMonadDefinition.

(** ** As functor with extra structure *)

(** The more traditional category theory approach defines a monad as
  an endofunctor with unit and multiplication natural transformations. *)

Module Type FunctorMonadDefinition (C : Category).
  Import (notations) C.

  (** This definition is more verbose and starts with a functor. *)

  Include Functor.Functor C C.

  (** We then define the unit and multiplication natural transformations. *)

  Parameter eta : forall X, X ~~> omap X.
  Parameter mu : forall X, omap (omap X) ~~> omap X.

  Axiom eta_natural :
    forall {X Y} (f : X ~~> Y),
      eta Y @ f = fmap f @ eta X.

  Axiom mu_natural :
    forall {X Y} (f : X ~~> Y),
      mu Y @ fmap (fmap f) = fmap f @ mu X.

  (** Finally the following diagrams must commute. *)

  Axiom mu_eta_l :
    forall X,
      mu X @ eta (omap X) = C.id (omap X).

  Axiom mu_eta_r :
    forall X,
      mu X @ fmap (eta X) = C.id (omap X).

  Axiom mu_mu :
    forall X,
      mu X @ mu (omap X) = mu X @ fmap (mu X).

End FunctorMonadDefinition.

(** Given a monad defined in this way, it is easy to define
  the Kleisli extension and validate the properties above. *)

Module ExpandFunctorMonadDefinition (C : Category) (T : FunctorMonadDefinition C).
  Import C.

  Definition ext {X Y} (f : X ~~> T.omap Y) :=
    T.mu Y @ T.fmap f.

  Lemma ext_eta {X Y} (f : X ~~> T.omap Y) :
    ext f @ T.eta X = f.
  Proof.
    unfold ext.
    rewrite compose_assoc, <- T.eta_natural.
    rewrite <- compose_assoc, T.mu_eta_l.
    rewrite compose_id_left. reflexivity.
  Qed.

  Lemma eta_ext X :
    ext (T.eta X) = id (T.omap X).
  Proof.
    unfold ext.
    apply T.mu_eta_r.
  Qed.

  Lemma ext_ext {X Y Z} (g : Y ~~> T.omap Z) (f : X ~~> T.omap Y) :
    ext g @ ext f = ext (ext g @ f).
  Proof.
    unfold ext.
    rewrite !T.fmap_compose, !compose_assoc.
    rewrite <- (compose_assoc _ (T.mu Y)), <- T.mu_natural, !compose_assoc.
    rewrite <- (compose_assoc _ (T.mu (T.omap Z))), T.mu_mu, !compose_assoc.
    reflexivity.
  Qed.

  Lemma ext_def {X Y} (f : X ~~> T.omap Y) :
    ext f = T.mu Y @ T.fmap f.
  Proof.
    reflexivity.
  Qed.

End ExpandFunctorMonadDefinition.


(** * Derived theory *)

(** Once a monad has been defined using either option, and expanded
  into a full [MonadDefinition] by including
  the appropriate [ExpandFooMonadDefinition] module,
  the following theory becomes available. *)

Module MonadTheory (C : Category) (T : MonadDefinition C).
  Import (notations) C.

  (** ** Rewriting version of the core properties *)

  Lemma ext_eta_rewrite {X Y} (f : X ~~> T.omap Y) {W} (w : W ~~> X) :
    T.ext f @ T.eta X @ w = f @ w.
  Proof.
    rewrite <- C.compose_assoc, T.ext_eta.
    reflexivity.
  Qed.

  Lemma ext_ext_rewrite {X Y Z} (g: Y ~~> T.omap Z) (f: X~~>_) {W} (w: W~~>_):
    T.ext g @ T.ext f @ w = T.ext (T.ext g @ f) @ w.
  Proof.
    rewrite <- C.compose_assoc, T.ext_ext.
    reflexivity.
  Qed.

  Lemma eta_natural_rewrite {X Y} (f : X ~~> Y) {W} (w : W ~~> X) :
    T.eta Y @ f @ w = T.fmap f @ T.eta X @ w.
  Proof.
    rewrite <- C.compose_assoc, T.eta_natural, C.compose_assoc.
    reflexivity.
  Qed.

  Lemma mu_natural_rewrite {X Y} (f : X ~~> Y) {W} (w : W ~~> _) :
    T.mu Y @ T.fmap (T.fmap f) @ w = T.fmap f @ T.mu X @ w.
  Proof.
    rewrite <- C.compose_assoc, T.mu_natural, C.compose_assoc.
    reflexivity.
  Qed.

  Lemma mu_eta_l_rewrite X {W} (w : W ~~> _) :
    T.mu X @ T.eta (T.omap X) @ w = w.
  Proof.
    rewrite <- C.compose_assoc, T.mu_eta_l, C.compose_id_left.
    reflexivity.
  Qed.

  Lemma mu_eta_r_rewrite X {W} (w : W ~~> _) :
    T.mu X @ T.fmap (T.eta X) @ w = w.
  Proof.
    rewrite <- C.compose_assoc, T.mu_eta_r, C.compose_id_left.
    reflexivity.
  Qed.

  Lemma mu_mu_rewrite X {W} (w : W ~~> _) :
    T.mu X @ T.mu (T.omap X) @ w =
    T.mu X @ T.fmap (T.mu X) @ w.
  Proof.
    rewrite <- C.compose_assoc, T.mu_mu, C.compose_assoc.
    reflexivity.
  Qed.

  Lemma ext_spec_rewrite {X Y} (f : X ~~> T.omap Y) {W} (w : W ~~> _) :
    T.ext f @ w = T.mu Y @ T.fmap f @ w.
  Proof.
    rewrite T.ext_spec, C.compose_assoc.
    reflexivity.
  Qed.

  (** ** Inter-definition of the various constructions *)

  (** We provide an [ext_spec]-style property for each one. *)

  Lemma mu_spec X :
    T.mu X = T.ext (C.id (T.omap X)).
  Proof.
    rewrite T.ext_spec.
    rewrite T.fmap_id, C.compose_id_right.
    reflexivity.
  Qed.

  Lemma fmap_spec {X Y} (f : X ~~> Y) :
    T.fmap f = T.ext (T.eta Y @ f).
  Proof.
    rewrite T.ext_spec.
    rewrite T.eta_natural.
    rewrite T.fmap_compose.
    rewrite mu_natural_rewrite.
    rewrite T.mu_eta_r, C.compose_id_right.
    reflexivity.
  Qed.

  (** ** Kleisli category *)

  (** *** Definition *)

  Module Kl <: Category.
    Definition t := C.t.
    Definition m X Y := C.m X (T.omap Y).

    Definition id X := T.eta X.
    Definition compose {X Y Z} (g : m Y Z) (f : m X Y) := T.ext g @ f.

    Proposition compose_id_left {X Y} (f : m X Y) :
      compose (id Y) f = f.
    Proof.
      unfold compose, id.
      rewrite T.eta_ext, C.compose_id_left.
      reflexivity.
    Qed.

    Proposition compose_id_right {X Y} (f : m X Y) :
      compose f (id X) = f.
    Proof.
      unfold compose, id.
      rewrite T.ext_eta.
      reflexivity.
    Qed.

    Proposition compose_assoc {X Y Z T} (f : m X Y) (g : m Y Z) (h : m Z T) :
      compose (compose h g) f = compose h (compose g f).
    Proof.
      unfold compose.
      rewrite <- ext_ext_rewrite.
      reflexivity.
    Qed.

    Include CategoryTheory.
  End Kl.

  (** *** Adjunction between the base and Kleisli categories *)

  Module KlF <: Functor C Kl.

    Definition omap (X : C.t) : Kl.t := X.
    Definition fmap {X Y} (f : X ~~> Y) : Kl.m X Y := T.eta Y @ f.

    Proposition fmap_id X :
      fmap (C.id X) = Kl.id X.
    Proof.
      unfold fmap, Kl.id.
      rewrite C.compose_id_right.
      reflexivity.
    Qed.

    Proposition fmap_compose {X Y Z} (g : Y ~~> Z) (f : X ~~> Y) :
      fmap (g @ f) = Kl.compose (fmap g) (fmap f).
    Proof.
      unfold fmap, Kl.compose.
      rewrite ext_eta_rewrite, C.compose_assoc.
      reflexivity.
    Qed.

    Include FunctorTheory C Kl.
  End KlF.

  Module KlU <: Functor Kl C.

    Definition omap (X : Kl.t) : C.t := T.omap X.
    Definition fmap {X Y} (f : Kl.m X Y) : omap X ~~> omap Y := T.ext f.

    Proposition fmap_id X :
      fmap (Kl.id X) = C.id (omap X).
    Proof.
      unfold fmap, Kl.id.
      rewrite T.eta_ext.
      reflexivity.
    Qed.

    Proposition fmap_compose {X Y Z} (g : Kl.m Y Z) (f : Kl.m X Y) :
      fmap (Kl.compose g f) = fmap g @ fmap f.
    Proof.
      unfold fmap, Kl.compose.
      rewrite T.ext_ext.
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
      unit V @ f = KlU.fmap (KlF.fmap f) @ unit A.
    Proof.
      unfold unit, counit, KlU.fmap, KlF.fmap.
      rewrite T.ext_eta.
      reflexivity.
    Qed.

    Proposition counit_natural {X Y} (ϕ : Kl.m X Y) :
      Kl.compose (counit Y) (KlF.fmap (KlU.fmap ϕ)) = Kl.compose ϕ (counit X).
    Proof.
      unfold Kl.compose, counit, KlF.fmap, KlU.fmap, KlU.omap.
      rewrite <- C.compose_assoc, T.ext_eta.
      rewrite C.compose_id_left, C.compose_id_right.
      reflexivity.
    Qed.

    Proposition unit_counit X :
      KlU.fmap (counit X) @ unit (KlU.omap X) = C.id (KlU.omap X).
    Proof.
      unfold KlU.fmap, KlU.omap, unit, counit.
      rewrite T.ext_eta.
      reflexivity.
    Qed.

    Proposition counit_unit A :
      Kl.compose (counit (KlF.omap A)) (KlF.fmap (unit A)) = Kl.id (KlF.omap A).
    Proof.
      unfold Kl.compose, KlF.omap, KlF.fmap, Kl.id, unit, counit.
      rewrite <- C.compose_assoc.
      rewrite T.ext_eta, C.compose_id_left.
      reflexivity.
    Qed.

    Include AdjointFunctorsTheory C Kl KlF KlU.
  End KlA.

End MonadTheory.

Module Type Monad (C : Category) :=
  MonadDefinition C <+
  MonadTheory C.
