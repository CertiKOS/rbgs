Require Import interfaces.Category.
Require Import interfaces.Functor.
Require Import interfaces.Monads.

(** * Lifting an endofunctor to a Kleisli category *)

(** Given a monad M on C and an endofunctor F : C → C with a distributive law
    λ : F∘M → M∘F, we can lift F to an endofunctor F̃ : Kl(M) → Kl(M).

    On objects:  F̃(X) = F(X)
    On morphisms: given f : X → MY in Kl(M),
                  F̃(f) = λ_Y ∘ F(f) : FX → MFY
*)

(** ** Distributive law interface *)

Module Type DistributiveLaw (C : Category) (M : Monad C) (F : Functor C C).
  (** The distributive law λ : FM → MF *)
  Parameter distr : forall X, C.m (F.omap (M.omap X)) (M.omap (F.omap X)).

  (** Naturality: for f : X → Y,
      dist Y ∘ F(M f) = M(F f) ∘ dist X *)
  Axiom distr_natural : forall {X Y} (f : C.m X Y),
    C.compose (distr Y) (F.fmap (M.fmap f)) =
    C.compose (M.fmap (F.fmap f)) (distr X).

  (** Compatibility with unit: dist ∘ F(η) = η_F *)
  Axiom distr_unit : forall X,
    C.compose (distr X) (F.fmap (M.eta X)) = M.eta (F.omap X).

  (** Compatibility with multiplication: dist ∘ F(μ) = μ_F ∘ M(dist) ∘ dist_M *)
  Axiom distr_mult : forall X,
    C.compose (distr X) (F.fmap (M.mu X)) =
    C.compose (M.mu (F.omap X))
      (C.compose (M.fmap (distr X)) (distr (M.omap X))).
End DistributiveLaw.

(** ** The lifted functor *)

Module LiftToKleisliDefinition (C : Category) (M : Monad C) (F : Functor C C)
  (D : DistributiveLaw C M F) <: FunctorDefinition M.Kl M.Kl.
  Import C.

  (** Objects: F̃(X) = F(X) *)
  Definition omap (X : M.Kl.t) : M.Kl.t := F.omap X.

  (** Morphisms: F̃(f) = λ ∘ F(f) for f : X → MY *)
  Definition fmap {X Y : M.Kl.t} (f : M.Kl.m X Y) : M.Kl.m (omap X) (omap Y) :=
    (D.distr Y) @ (F.fmap f).

  Proposition fmap_id : forall X, fmap (M.Kl.id X) = M.Kl.id (omap X).
  Proof.
    intros. unfold fmap, M.Kl.id, omap.
    rewrite D.distr_unit.
    reflexivity.
  Qed.

  Proposition fmap_compose :
    forall {X Y Z} (g : M.Kl.m Y Z) (f : M.Kl.m X Y),
    fmap (M.Kl.compose g f) = M.Kl.compose (fmap g) (fmap f).
  Proof.
    intros. unfold fmap, omap, M.Kl.compose, M.ext.
    rewrite !F.fmap_compose. rewrite <- !compose_assoc.
    rewrite D.distr_mult. rewrite M.fmap_compose.
    f_equal. rewrite !compose_assoc. f_equal. f_equal.
    rewrite D.distr_natural. reflexivity.
  Qed.

End LiftToKleisliDefinition.

Module LiftToKleisliTheory (C : Category) (M : Monad C) (F : Functor C C)
  (D : DistributiveLaw C M F).

  Include LiftToKleisliDefinition C M F D.
  Import C.

  (** The lifted functor F̃ makes the following square commute:

          F
      C -----> C
      |        |
    J |        | J
      v        v
    Kl(M) --> Kl(M)
          F̃

      where J = KlF is the free functor C → Kl(M).

      That is: J ∘ F = F̃ ∘ J
  *)

  (** On objects: J(F(X)) = F̃(J(X)) *)
  Proposition lifting_square_omap : forall X,
    M.KlF.omap (F.omap X) = omap (M.KlF.omap X).
  Proof.
    intros. unfold M.KlF.omap, omap.
    reflexivity.
  Qed.

  (** On morphisms: J(F(f)) = F̃(J(f)) for f : X → Y in C *)
  Proposition lifting_square_fmap : forall {X Y} (f : C.m X Y),
    M.KlF.fmap (F.fmap f) = fmap (M.KlF.fmap f).
  Proof.
    intros. unfold M.KlF.fmap, fmap.
    rewrite F.fmap_compose.
    rewrite <- compose_assoc.
    rewrite D.distr_unit.
    reflexivity.
  Qed.

End LiftToKleisliTheory.

(** ** Full lifted functor with theory *)

Module LiftToKleisli (C : Category) (M : Monad C) (F : Functor C C)
  (D : DistributiveLaw C M F) <: Functor M.Kl M.Kl.

  Include LiftToKleisliTheory C M F D.
  Include FunctorTheory M.Kl M.Kl.

End LiftToKleisli.

(** * Lifting a bifunctor to a Kleisli category *)

(** Given a monad M on S, a category L, and a bifunctor F : L × S → S
    with a distributive law λ : F(l, M(-)) → M(F(l, -)), we can lift F
    to a bifunctor F̃ : L × Kl(M) → Kl(M).

    On objects:  F̃(l, X) = F(l, X)
    On morphisms: given e : l₁ → l₂ in L and f : X → MY in Kl(M),
                  F̃(e, f) = λ_{l₂,Y} ∘ F(e, f) : F(l₁, X) → M(F(l₂, Y))
*)

(** ** Bifunctor distributive law interface *)

Module Type BiDistributiveLaw (L : Category) (S : Category) (M : Monad S)
  (F : Bifunctor L S S).

  (** The distributive law λ : F(l, MX) → MF(l, X) *)
  Parameter distr : forall (l : L.t) (X : S.t),
    S.m (F.omap l (M.omap X)) (M.omap (F.omap l X)).

  (** Naturality in l: for e : l₁ → l₂,
      distr l₂ X ∘ F(e, M.id) = M(F(e, id)) ∘ distr l₁ X *)
  Axiom distr_natural_l : forall {l1 l2 : L.t} (e : L.m l1 l2) (X : S.t),
    S.compose (distr l2 X) (F.fmap e (S.id (M.omap X))) =
    S.compose (M.fmap (F.fmap e (S.id X))) (distr l1 X).

  (** Naturality in X: for f : X → Y,
      distr l Y ∘ F(id, M f) = M(F(id, f)) ∘ distr l X *)
  Axiom distr_natural_r : forall (l : L.t) {X Y : S.t} (f : S.m X Y),
    S.compose (distr l Y) (F.fmap (L.id l) (M.fmap f)) =
    S.compose (M.fmap (F.fmap (L.id l) f)) (distr l X).

  (** Compatibility with unit: distr l X ∘ F(id, η_X) = η_{F(l,X)} *)
  Axiom distr_unit : forall (l : L.t) (X : S.t),
    S.compose (distr l X) (F.fmap (L.id l) (M.eta X)) = M.eta (F.omap l X).

  (** Compatibility with multiplication:
      distr l X ∘ F(id, μ_X) = μ_{F(l,X)} ∘ M(distr l X) ∘ distr l (MX) *)
  Axiom distr_mult : forall (l : L.t) (X : S.t),
    S.compose (distr l X) (F.fmap (L.id l) (M.mu X)) =
    S.compose (M.mu (F.omap l X))
      (S.compose (M.fmap (distr l X)) (distr l (M.omap X))).

End BiDistributiveLaw.

(** ** Derived lemmas for bifunctor distributive laws *)

Module BiDistributiveLawTheory (L : Category) (S : Category) (M : Monad S)
  (F : Bifunctor L S S) (D : BiDistributiveLaw L S M F).

  Import S.

  (** Combined naturality: for e : l₁ → l₂ and f : X → Y,
      distr l₂ Y ∘ F(e, M(f)) = M(F(e, f)) ∘ distr l₁ X *)
  Lemma distr_natural : forall {l1 l2 : L.t} {X Y : S.t}
    (e : L.m l1 l2) (f : S.m X Y),
    S.compose (D.distr l2 Y) (F.fmap e (M.fmap f)) =
    S.compose (M.fmap (F.fmap e f)) (D.distr l1 X).
  Proof.
    intros.
    (* Split F.fmap e (M.fmap f) using bifunctor composition *)
    rewrite <- (S.compose_id_right (M.fmap f)).
    rewrite <- (L.compose_id_left e) at 1.
    rewrite F.fmap_compose.
    (* Apply naturality axioms in sequence *)
    rewrite <- !compose_assoc.
    rewrite D.distr_natural_r.
    rewrite !compose_assoc.
    rewrite D.distr_natural_l.
    (* Reassemble *)
    rewrite <- compose_assoc.
    rewrite <- M.fmap_compose.
    rewrite <- F.fmap_compose.
    rewrite L.compose_id_left, S.compose_id_right.
    reflexivity.
  Qed.

End BiDistributiveLawTheory.

(** ** The lifted bifunctor definition *)

Module LiftBifunctorToKleisliDefinition (L : Category) (S : Category) (M : Monad S)
  (F : Bifunctor L S S) (D : BiDistributiveLaw L S M F)
  <: BifunctorDefinition L M.Kl M.Kl.

  Module DT := BiDistributiveLawTheory L S M F D.
  Import S.

  (** Objects: F̃(l, X) = F(l, X) *)
  Definition omap (l : L.t) (X : M.Kl.t) : M.Kl.t := F.omap l X.

  (** Morphisms: F̃(e, f) = λ ∘ F(e, f) for e : l₁ → l₂ and f : X → MY *)
  Definition fmap {A1 : L.t} {A2 : M.Kl.t} {B1 : L.t} {B2 : M.Kl.t}
    (e : L.m A1 B1) (f : M.Kl.m A2 B2) : M.Kl.m (omap A1 A2) (omap B1 B2) :=
    compose (D.distr B1 B2) (F.fmap e f).

  Proposition fmap_id : forall l X,
    fmap (L.id l) (M.Kl.id X) = M.Kl.id (omap l X).
  Proof.
    intros. unfold fmap, M.Kl.id, omap.
    rewrite D.distr_unit.
    reflexivity.
  Qed.

  Proposition fmap_compose :
    forall {A1 : L.t} {A2 : M.Kl.t} {B1 : L.t} {B2 : M.Kl.t} {C1 : L.t} {C2 : M.Kl.t}
      (g1 : L.m B1 C1) (g2 : M.Kl.m B2 C2) (f1 : L.m A1 B1) (f2 : M.Kl.m A2 B2),
    fmap (L.compose g1 f1) (M.Kl.compose g2 f2) =
      M.Kl.compose (fmap g1 g2) (fmap f1 f2).
  Proof.
    intros. unfold fmap, omap, M.Kl.compose, M.ext.
    rewrite F.fmap_compose. rewrite <- !compose_assoc.
    rewrite <- (L.compose_id_left g1).
    rewrite F.fmap_compose. rewrite <- !compose_assoc.
    (* Use distr_mult for the μ part *)
    rewrite D.distr_mult at 1. rewrite M.fmap_compose.
    f_equal. rewrite !compose_assoc. f_equal. f_equal.
    (* Use combined naturality *)
    rewrite DT.distr_natural. rewrite <- (S.compose_id_left g2) at 2.
    rewrite F.fmap_compose. rewrite F.fmap_id. rewrite compose_id_left.
    reflexivity.
  Qed.

End LiftBifunctorToKleisliDefinition.

(** ** Lifting square theorem for bifunctors *)

Module LiftBifunctorToKleisliTheory (L : Category) (S : Category) (M : Monad S)
  (F : Bifunctor L S S) (D : BiDistributiveLaw L S M F).

  Include LiftBifunctorToKleisliDefinition L S M F D.
  Import S.

  (** The lifted bifunctor F̃ makes the following square commute:

              F
      L × S -----> S
        |          |
    id×J |          | J
        v          v
    L × Kl(M) --> Kl(M)
              F̃

      where J = KlF is the free functor S → Kl(M).

      That is: J ∘ F = F̃ ∘ (id × J)
  *)

  (** On objects: J(F(l, X)) = F̃(l, J(X)) *)
  Proposition lifting_square_omap : forall l X,
    M.KlF.omap (F.omap l X) = omap l (M.KlF.omap X).
  Proof.
    intros. unfold M.KlF.omap, omap.
    reflexivity.
  Qed.

  (** On morphisms: J(F(e, f)) = F̃(e, J(f)) for e : l₁ → l₂ in L and f : X → Y in S *)
  Proposition lifting_square_fmap : forall {l1 l2 : L.t} {X Y : S.t}
    (e : L.m l1 l2) (f : S.m X Y),
    M.KlF.fmap (F.fmap e f) = fmap e (M.KlF.fmap f).
  Proof.
    intros. unfold M.KlF.fmap, fmap.
    (* J(F(e,f)) = η ∘ F(e,f) *)
    (* F̃(e, J(f)) = λ ∘ F(e, η ∘ f) *)
    rewrite <- (L.compose_id_right e) at 2.
    rewrite F.fmap_compose.
    symmetry.
    rewrite <- (L.compose_id_left e). rewrite <- (S.compose_id_right (M.eta Y)).
    rewrite F.fmap_compose. rewrite <- !compose_assoc.
    rewrite D.distr_unit. rewrite !compose_assoc. rewrite <- F.fmap_compose.
    rewrite compose_id_left. rewrite L.compose_id_left, L.compose_id_right.
    reflexivity.
  Qed.

End LiftBifunctorToKleisliTheory.

(** ** The lifted bifunctor with theory *)

Module LiftBifunctorToKleisli (L : Category) (S : Category) (M : Monad S)
  (F : Bifunctor L S S) (D : BiDistributiveLaw L S M F)
  <: Bifunctor L M.Kl M.Kl.

  Include LiftBifunctorToKleisliTheory L S M F D.
  Include BifunctorTheory L M.Kl M.Kl.

End LiftBifunctorToKleisli.