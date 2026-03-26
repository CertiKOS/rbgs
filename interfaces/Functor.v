(** In this library we define module interfaces
  for various kind of fixed functors between category modules.
  Note that functors can also be treated as first-order objects;
  see the [FunctorCategory] library. *)

Require Import interfaces.Category.


(** * Functors *)

(** ** Quiver homorphisms *)

(** In some cases it is useful to define mappings between quivers or
  mappings between categories which do not preserve composition and
  identities. The following interface is used for this. *)

Module Type QuiverHomomorphism (C D : Quiver).
  Parameter omap : C.t -> D.t.
  Parameter fmap : forall {A B}, C.m A B -> D.m (omap A) (omap B).
End QuiverHomomorphism.

(** ** Functors *)

(** Most of the time, we do want the extra properties that the
  identities and composites are preserved. *)

Module Type FunctorDefinition (C D : CategoryDefinition).
  Include QuiverHomomorphism C D.

  Axiom fmap_id :
    forall A, fmap (C.id A) = D.id (omap A).

  Axiom fmap_compose :
    forall {A B C} (g : C.m B C) (f : C.m A B),
      fmap (C.compose g f) = D.compose (fmap g) (fmap f).

End FunctorDefinition.

(** ** Theory *)

(** In that case, the following properties and definitions can be derived. *)

Module FunctorTheory (C D : Category) (F : FunctorDefinition C D).
  Import F.

  Program Canonical Structure fmap_iso {A B} (f : C.iso A B) : D.iso (omap A) (omap B) :=
    {|
      D.fw := fmap (C.fw f);
      D.bw := fmap (C.bw f);
    |}.
  Next Obligation.
    rewrite <- F.fmap_compose, C.bw_fw, F.fmap_id. auto.
  Qed.
  Next Obligation.
    rewrite <- F.fmap_compose, C.fw_bw, F.fmap_id. auto.
  Qed.

  (** *** Universal morphisms *)

  (** Universal properties can be formalized using the notion of
    universal morphism into and out of a particular functor.
    Morover, a functor is a right adjoint when there is a universal
    morphisms into it from every object of [D], and conversely
    it is a left adjoint when there is a "couniversal" morphism
    from the functor to every object of [D].

    The terminology of "universal" vs "couniversal" is not standard,
    but we adopt it because we need two different names.
    Given the fundamental connection between universal morphisms and
    adjoint functors, we follow the convention used in that context,
    so that the unit of an adjunction is a "universal" morphism into
    the right adjoint, while the counit is a "couniversal" moprhism
    into the left adjoint.

    A universal morphism from [X] to a functor [G] is given by
    an object [U∈C] and a morphism [u : X → GU ∈ D]
    which satisfy the property below. If [G] has a left adjoint [F]
    then the object [U := FX] and the unit component [ηX : X → GFX]
    constitute a universal morphism from [X] to [G]. *)

  Class Universal (X : D.t) {U : C.t} (u : D.m X (omap U)) :=
    {
      transpose {A} (f : D.m X (omap A)) : C.m U A;
      transpose_prop {A} f : D.compose (fmap (@transpose A f)) u = f;
      transpose_uniq {A f} g : D.compose (fmap g) u = f -> @transpose A f = g;
    }.

  Arguments transpose {X U} u {_ A} f.

  (** Universal morphisms are unique up to isomorphism. *)

  Lemma transpose_self `{Hu : Universal} :
    transpose u u = C.id U.
  Proof.
    apply transpose_uniq.
    rewrite fmap_id, D.compose_id_left.
    reflexivity.
  Qed.

  Section UNIVERSAL_ISO.
    Context {X : D.t}.
    Context {U} (u : D.m X (omap U)) `{Hu : !Universal X u}.
    Context {V} (v : D.m X (omap V)) `{Hv : !Universal X v}.

    Program Definition universal_iso : C.iso U V :=
      {|
        C.fw := transpose u v;
        C.bw := transpose v u;
      |}.
    Next Obligation.
      rewrite <- transpose_self. symmetry.
      apply transpose_uniq.
      rewrite fmap_compose, D.compose_assoc.
      rewrite !transpose_prop.
      reflexivity.
    Qed.
    Next Obligation.
      rewrite <- transpose_self. symmetry.
      apply transpose_uniq.
      rewrite fmap_compose, D.compose_assoc.
      rewrite !transpose_prop.
      reflexivity.
    Qed.

    Theorem universal_up_to_iso :
      D.compose (fmap (C.fw universal_iso)) u = v.
    Proof.
      cbn.
      apply transpose_prop.
    Qed.
  End UNIVERSAL_ISO.

  (** Conversely, what we call a "couniversal" morphism from
    a functor [F : C → D] to an object [X∈D] is an object [U∈C] and
    a morphism [u : FU → X ∈ D] which satisfy the dual property
    below. If [F] has a right adjoint [G] then the object [U := GX]
    and the counit component [εX : FGX → X] constitute a couniversal
    morphism from [F] to [X]. *)

  Class Couniversal (X : D.t) {U : C.t} (u : D.m (omap U) X) :=
    {
      cotranspose {A} (f : D.m (omap A) X) : C.m A U;
      cotranspose_prop {A} f: D.compose u (fmap (@cotranspose A f)) = f;
      cotranspose_uniq {A f} g: D.compose u (fmap g) = f -> @cotranspose A f = g;
    }.

  Arguments cotranspose {X U} u {_ A} f.

  Lemma cotranspose_self `{Hu : Couniversal} :
    cotranspose u u = C.id U.
  Proof.
    apply cotranspose_uniq.
    rewrite fmap_id, D.compose_id_right.
    reflexivity.
  Qed.

  Section COUNIVERSAL_ISO.
    Context {X : D.t}.
    Context {U} (u : D.m (omap U) X) `{Hu : !Couniversal X u}.
    Context {V} (v : D.m (omap V) X) `{Hv : !Couniversal X v}.

    Program Definition couniversal_iso : C.iso U V :=
      {|
        C.fw := cotranspose v u;
        C.bw := cotranspose u v;
      |}.
    Next Obligation.
      rewrite <- cotranspose_self. symmetry.
      apply cotranspose_uniq.
      rewrite fmap_compose, <- D.compose_assoc.
      rewrite !cotranspose_prop.
      reflexivity.
    Qed.
    Next Obligation.
      rewrite <- cotranspose_self. symmetry.
      apply cotranspose_uniq.
      rewrite fmap_compose, <- D.compose_assoc.
      rewrite !cotranspose_prop.
      reflexivity.
    Qed.

    Theorem couniversal_up_to_iso :
      D.compose v (fmap (C.fw couniversal_iso)) = u.
    Proof.
      cbn.
      apply cotranspose_prop.
    Qed.
  End COUNIVERSAL_ISO.

End FunctorTheory.

Module Type Functor (C D : Category) :=
  FunctorDefinition C D <+
  FunctorTheory C D.

(** ** Additional properties *)

Module Type Faithful (C D : Quiver) (F : QuiverHomomorphism C D).

  Axiom faithful :
    forall {A B} (f g : C.m A B), F.fmap f = F.fmap g -> f = g.

End Faithful.

Module Type Full (C D : Quiver) (F : QuiverHomomorphism C D).

  Axiom full :
    forall {A B} (d : D.m (F.omap A) (F.omap B)),
    exists (c : C.m A B), F.fmap c = d.

End Full.

Module Type FullFunctor (C D : Category) :=
  Functor C D <+ Full C D.

Module Type FaithfulFunctor (C D : Category) :=
  Functor C D <+ Faithful C D.

Module Type FullAndFaithfulFunctor (C D : Category) :=
  Functor C D <+ Full C D <+ Faithful C D.


(** * Bifunctors *)

(** We also provide separate definitions for bifunctors,
  which we use to define monoidal structures.
  Although bifunctors can be described as functors from
  product categories (see [BifunctorTheory] below),
  it is much more convenient to give a direct definition
  in terms of binary functions. *)

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

Module BifunctorTheory (C1 C2 D : Category) (F : BifunctorDefinition C1 C2 D).

  (** Preservation of isomorphisms *)

  Program Canonical Structure fmap_iso {A1 A2 B1 B2} (f1 : C1.iso A1 B1) (f2 : C2.iso A2 B2) :=
    {|
      D.fw := F.fmap (C1.fw f1) (C2.fw f2);
      D.bw := F.fmap (C1.bw f1) (C2.bw f2);
    |}.
  Next Obligation.
    rewrite <- F.fmap_compose, C1.bw_fw, C2.bw_fw, F.fmap_id. auto.
  Qed.
  Next Obligation.
    rewrite <- F.fmap_compose, C1.fw_bw, C2.fw_bw, F.fmap_id. auto.
  Qed.

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

    Include FunctorTheory PC D.
  End PF.

End BifunctorTheory.

(** ** Bundled interface *)

Module Type Bifunctor (C1 C2 D : Category).
  Include BifunctorDefinition C1 C2 D.
  Include BifunctorTheory C1 C2 D.
End Bifunctor.
