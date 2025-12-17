Require Import interfaces.Category.
Require Import interfaces.Functor.

(** * Adjoint functors *)

(** ** Definition *)

(** There are many ways to define adjunctions. Here we will assume
  that the two functors are known ahead of time and provide two
  options for establishing an adjunction. Note that we follow the
  naming convention used in nlab where adjunctions of the form
  [F ⊣ G : D -> C] are described, as opposed to the Wikipedia page
  on adjoint functors, which reverses [C] and [D]. *)

Module Type AdjointFunctorsDefinition
    (C D : Category) (F : Functor C D) (G : Functor D C).

  Parameter unit : forall A, C.m A (G.omap (F.omap A)).
  Parameter counit : forall X, D.m (F.omap (G.omap X)) X.

  Axiom unit_natural :
    forall {A V} (f : C.m A V),
      C.compose (unit V) f = C.compose (G.fmap (F.fmap f)) (unit A).

  Axiom counit_natural :
    forall {X Y} (ϕ : D.m X Y),
      D.compose (counit Y) (F.fmap (G.fmap ϕ)) = D.compose ϕ (counit X).

  Axiom unit_counit :
    forall X,
      C.compose (G.fmap (counit X)) (unit (G.omap X)) = C.id (G.omap X).

  Axiom counit_unit :
    forall A,
      D.compose (counit (F.omap A)) (F.fmap (unit A)) = D.id (F.omap A).

End AdjointFunctorsDefinition.

(** ** Properties *)

Module Type AdjointFunctorsTheory
    (C D : Category) (F : Functor C D) (G : Functor D C)
    (FG : AdjointFunctorsDefinition C D F G).

  Import FG.
  Obligation Tactic := cbn.

  (** *** Universal morphisms *)

  (** The unit and counit can be characterized as universal morphisms. *)

  Global Program Instance unit_universal (A : C.t) : G.Universal A (unit A) :=
    {
      G.transpose X (f : C.m A (G.omap X)) :=
        D.compose (counit X) (F.fmap f) : D.m (F.omap A) X
    }.
  Next Obligation.
    intros A X f.
    rewrite G.fmap_compose, C.compose_assoc.
    rewrite <- unit_natural, <- C.compose_assoc.
    rewrite unit_counit, C.compose_id_left.
    reflexivity.
  Qed.
  Next Obligation.
    intros A X f ϕ H. destruct H.
    rewrite F.fmap_compose, <- D.compose_assoc.
    rewrite counit_natural, D.compose_assoc.
    rewrite counit_unit, D.compose_id_right.
    reflexivity.
  Qed.

  Global Program Instance counit_couniversal X : F.Couniversal X (counit X) :=
    {
      F.cotranspose A (ϕ : D.m (F.omap A) X) :=
        C.compose (G.fmap ϕ) (unit A) : C.m A (G.omap X)
    }.
  Next Obligation.
    intros X A ϕ.
    rewrite F.fmap_compose, <- D.compose_assoc.
    rewrite counit_natural, D.compose_assoc.
    rewrite counit_unit, D.compose_id_right.
    reflexivity.
  Qed.
  Next Obligation.
    intros X A ϕ f H. destruct H.
    rewrite G.fmap_compose, C.compose_assoc.
    rewrite <- unit_natural, <- C.compose_assoc.
    rewrite unit_counit, C.compose_id_left.
    reflexivity.
  Qed.

  (** *** Natural bijection *)

  (** The (co-)transpose operations are inverse of each other *)

  Proposition transpose_cotranspose {A X} (ϕ : D.m (F.omap A) X) :
    G.transpose _ (F.cotranspose _ ϕ) = ϕ.
  Proof.
    apply G.transpose_uniq. symmetry.
    apply F.cotranspose_uniq.
    rewrite F.fmap_compose, <- D.compose_assoc.
    rewrite counit_natural, D.compose_assoc.
    rewrite counit_unit, D.compose_id_right.
    reflexivity.
  Qed.

  Proposition cotranspose_transpose {A X} (f : C.m A (G.omap X)) :
    F.cotranspose _ (G.transpose _ f) = f.
  Proof.
    apply F.cotranspose_uniq. symmetry.
    apply G.transpose_uniq.
    rewrite G.fmap_compose, C.compose_assoc.
    rewrite <- unit_natural, <- C.compose_assoc.
    rewrite unit_counit, C.compose_id_left.
    reflexivity.
  Qed.

  (** Naturality *)

  Proposition transpose_natural_l {A B X} (a : C.m B A) (f : C.m A (G.omap X)) :
    G.transpose _ (C.compose f a) = D.compose (G.transpose _ f) (F.fmap a).
  Proof.
    apply G.transpose_uniq.
    rewrite !G.fmap_compose, !C.compose_assoc.
    rewrite <- unit_natural, <- C.compose_assoc. f_equal.
    apply G.transpose_prop.
  Qed.

  Proposition transpose_natural_r {A X Y} (f : C.m A (G.omap X)) (x : D.m X Y) :
    G.transpose _ (C.compose (G.fmap x) f) = D.compose x (G.transpose _ f).
  Proof.
    apply G.transpose_uniq.
    rewrite !G.fmap_compose, !C.compose_assoc. f_equal.
    apply G.transpose_prop.
  Qed.

  Proposition cotranspose_natural_l {A B X} (a: C.m B A) (ϕ: D.m (F.omap A) X) :
    F.cotranspose _ (D.compose ϕ (F.fmap a)) = C.compose (F.cotranspose _ ϕ) a.
  Proof.
    apply F.cotranspose_uniq.
    rewrite !F.fmap_compose, <- D.compose_assoc.
    rewrite F.cotranspose_prop.
    reflexivity.
  Qed.

  Proposition cotranspose_natural_r {A X Y} (ϕ : D.m (F.omap A) X) (x : D.m X Y) :
    F.cotranspose _ (D.compose x ϕ) = C.compose (G.fmap x) (F.cotranspose _ ϕ).
  Proof.
    apply F.cotranspose_uniq.
    rewrite !F.fmap_compose, <- D.compose_assoc.
    rewrite counit_natural, D.compose_assoc.
    rewrite F.cotranspose_prop.
    reflexivity.
  Qed.

End AdjointFunctorsTheory.

Module Type AdjointFunctors (C D : Category) (F : Functor C D) (G : Functor D C) :=
  AdjointFunctorsDefinition C D F G <+
  AdjointFunctorsTheory C D F G.
