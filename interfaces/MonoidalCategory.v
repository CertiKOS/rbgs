Require Import interfaces.Category.
Require Import interfaces.Functor.


(** * Monoidal structures *)

(** Since a given category may involve several monoidal structure,
  we separate the corresponding interface into a submodule. *)

Module Type MonoidalStructure (C : Category).
  Import C.

  Include Bifunctor C C C.

  Parameter unit : C.t.
  Parameter assoc : forall A B C, C.iso (omap A (omap B C)) (omap (omap A B) C).
  Parameter lunit : forall A, C.iso (omap unit A) A.
  Parameter runit : forall A, C.iso (omap A unit) A.

  Axiom assoc_coh :
    forall A B C D : C.t,
      fmap (assoc A B C) (C.id D) @
        assoc A (omap B C) D @
        fmap (C.id A) (assoc B C D) =
      assoc (omap A B) C D @
        assoc A B (omap C D).

  Axiom unit_coh :
    forall A B : C.t,
      fmap (runit A) (C.id B) @ assoc A unit B =
      fmap (C.id A) (lunit B).

End MonoidalStructure.

(** Then a monoidal category is a category with a submodule for
  a tensor product. *)

Module Type MonoidalDefinition (C : Category).
  Declare Module Tens : MonoidalStructure C.
End MonoidalDefinition.

Module MonoidalTheory (C : Category) (M : MonoidalDefinition C).
  Import C M.

  Notation "1" := Tens.unit : obj_scope.
  Infix "*" := Tens.omap : obj_scope.
  Infix "*" := Tens.fmap : hom_scope.
  Notation α := Tens.assoc.
  Notation λ := Tens.lunit.
  Notation ρ := Tens.runit.

End MonoidalTheory.

Module Type Monoidal :=
  Category.Category
    <+ MonoidalDefinition
    <+ MonoidalTheory.


(** * Cartesian monoidal structures *)

(** ** Definition *)

Module Type CartesianStructureDefinition (C : Category).
  Import C.

  (** Terminal object *)

  Parameter unit : t.
  Parameter ter : forall X, C.m X unit.

  Axiom ter_uni : forall {X} (x y : C.m X unit), x = y.

  (** Binary products *)

  Parameter omap : t -> t -> t.
  Parameter p1 : forall {A B}, m (omap A B) A.
  Parameter p2 : forall {A B}, m (omap A B) B.
  Parameter pair : forall {X A B}, m X A -> m X B -> m X (omap A B).

  Axiom p1_pair : forall {X A B} (f : m X A) (g : m X B), p1 @ pair f g = f.
  Axiom p2_pair : forall {X A B} (f : m X A) (g : m X B), p2 @ pair f g = g.
  Axiom pair_pi : forall {X A B} x, @pair X A B (p1 @ x) (p2 @ x) = x.

End CartesianStructureDefinition.

(** ** Consequences *)

(** We show in particular that cartesian structures are a special case
  of monoidal structure. *)

Module CartesianStructureTheory (C : Category) (P : CartesianStructureDefinition C)
    <: MonoidalStructure C.

  Import C.
  Include P.

  Local Infix "&" := omap (at level 40, left associativity) : obj_scope.

  (** *** Useful lemmas *)

  Lemma p1_pair_rewrite {X A B Y} (f : m X A) (g : m X B) (x : m Y X) :
    p1 @ pair f g @ x = f @ x.
  Proof.
    rewrite <- compose_assoc, p1_pair; auto.
  Qed.

  Lemma p2_pair_rewrite {X A B Y} (f : m X A) (g : m X B) (x : m Y X) :
    p2 @ pair f g @ x = g @ x.
  Proof.
    rewrite <- compose_assoc, p2_pair; auto.
  Qed.

  Lemma pair_uni {X A B} (x : m X (omap A B)) (f : m X A) (g : m X B) :
    p1 @ x = f ->
    p2 @ x = g ->
    x = pair f g.
  Proof.
    intros. subst.
    rewrite pair_pi. auto.
  Qed.

  Lemma pair_compose {X A B Y} (f : m X A) (g : m X B) (x : m Y X) :
    pair f g @ x = pair (f @ x) (g @ x).
  Proof.
    apply pair_uni.
    - apply p1_pair_rewrite.
    - apply p2_pair_rewrite.
  Qed.

  (** *** Bifunctor structure *)

  Definition fmap {A1 A2 B1 B2} (f1 : m A1 B1) (f2 : m A2 B2) :=
    pair (f1 @ p1) (f2 @ p2).

  Proposition fmap_id (A B : t) :
    fmap (id A) (id B) = id (omap A B).
  Proof.
    unfold fmap. symmetry.
    apply pair_uni; rewrite compose_id_left, compose_id_right; auto.
  Qed.

  Proposition fmap_compose {A1 A2 B1 B2 C1 C2} :
    forall (g1 : m B1 C1) (g2 : m B2 C2) (f1: m A1 B1) (f2: m A2 B2),
      fmap (g1 @ f1) (g2 @ f2) = fmap g1 g2 @ fmap f1 f2.
  Proof.
    intros. unfold fmap. symmetry.
    apply pair_uni.
    - rewrite p1_pair_rewrite, compose_assoc, p1_pair, compose_assoc. auto.
    - rewrite p2_pair_rewrite, compose_assoc, p2_pair, compose_assoc. auto.
  Qed.

  Include BifunctorTheory C C C.
  Local Infix "&" := fmap : hom_scope.

  (** *** Monoidal structure *)

  Program Definition assoc (A B C : t) : C.iso (A & (B & C)) ((A & B) & C) :=
    {|
      fw := pair (pair p1 (p1 @ p2)) (p2 @ p2);
      bw := pair (p1 @ p1) (pair (p2 @ p1) p2);
    |}.
  Next Obligation.
    rewrite !pair_compose. symmetry. apply pair_uni.
    - rewrite compose_id_right, !compose_assoc, !p1_pair. auto.
    - rewrite compose_id_right, !compose_assoc, !p1_pair, !p2_pair, pair_pi. auto.
  Qed.
  Next Obligation.
    rewrite !pair_compose. symmetry. apply pair_uni.
    - rewrite compose_id_right, !compose_assoc, !p2_pair, !p1_pair, pair_pi. auto.
    - rewrite compose_id_right, !compose_assoc, !p2_pair. auto.
  Qed.

  Program Definition lunit (A : t) : iso (unit & A) A :=
    {|
      fw := p2;
      bw := pair (ter A) (id A);
    |}.
  Next Obligation.
    rewrite pair_compose. symmetry. apply pair_uni.
    - apply ter_uni.
    - rewrite compose_id_right, compose_id_left. auto.
  Qed.
  Next Obligation.
    apply p2_pair.
  Qed.

  Program Definition runit (A : t) : iso (A & unit) A :=
    {|
      fw := p1;
      bw := pair (id A) (ter A);
    |}.
  Next Obligation.
    rewrite pair_compose. symmetry. apply pair_uni.
    - rewrite compose_id_right, compose_id_left. auto.
    - apply ter_uni.
  Qed.
  Next Obligation.
    apply p1_pair.
  Qed.

  Proposition assoc_coh (A B C D : t) :
    (assoc A B C & id D) @ assoc A (B & C) D @ (id A & assoc B C D) =
    assoc (A & B) C D @ assoc A B (C & D).
  Proof.
    unfold assoc, fmap; cbn.
    repeat
      (apply pair_uni ||
       rewrite ?compose_assoc, ?compose_id_left, ?compose_id_right ||
       rewrite ?p1_pair, ?p2_pair, ?pair_compose);
      auto.
  Qed.

  Proposition unit_coh (A B : t) :
    (runit A & id B) @ assoc A unit B = id A & lunit B.
  Proof.
    unfold runit, lunit, fmap; cbn.
    repeat
      (apply pair_uni ||
       rewrite ?compose_assoc, ?compose_id_left, ?compose_id_right ||
       rewrite ?p1_pair, ?p2_pair, ?pair_compose);
      auto.
  Qed.

End CartesianStructureTheory.

(** ** Cartesian category interface *)

Module Type CartesianDef (C : Category).
  Declare Module Prod : MonoidalStructure C.
End CartesianDef.

Module CartesianTheory (C : Category) (M : CartesianDef C).
  Import C M.
  Notation T := Prod.unit.
  Infix "&" := Prod.omap (at level 40, left associativity) : obj_scope.
  Infix "&" := Prod.fmap : hom_scope.
End CartesianTheory.

Module Type Cartesian :=
  Category.Category <+ CartesianDef <+ CartesianTheory.
