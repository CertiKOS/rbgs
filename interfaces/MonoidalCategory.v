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

  (** Naturality properties *)

  Axiom assoc_nat :
    forall {A1 B1 C1 A2 B2 C2: C.t} (f: C.m A1 A2) (g: C.m B1 B2) (h: C.m C1 C2),
      fmap (fmap f g) h @ assoc A1 B1 C1 = assoc A2 B2 C2 @ fmap f (fmap g h).

  Axiom lunit_nat :
    forall {A1 A2 : C.t} (f : C.m A1 A2),
      f @ lunit A1 = lunit A2 @ fmap (C.id unit) f.

  Axiom runit_nat :
    forall {A1 A2 : C.t} (f : C.m A1 A2),
      f @ runit A1 = runit A2 @ fmap f (C.id unit).

  (** Pentagon identity *)

  Axiom assoc_coh :
    forall A B C D : C.t,
      fmap (assoc A B C) (C.id D) @
        assoc A (omap B C) D @
        fmap (C.id A) (assoc B C D) =
      assoc (omap A B) C D @
        assoc A B (omap C D).

  (** Triangle identity *)

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

Module Type Monoidal (C : Category) :=
  MonoidalDefinition C <+
  MonoidalTheory C.


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
  of monoidal structure. Note that we cannot include [BifunctorTheory]
  until the [omap] field from [CartesianStructureDefinition] and the
  [fmap] field from [CartesianStructureTheory] have been consolidated
  into a single module. As a result we need to defer this until we
  define the overall [CartesianStructure] interface. *)

Module CartesianStructureTheory (C : Category) (P : CartesianStructureDefinition C).

  Import C P.

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

  Global Hint Rewrite
    @p1_pair @p1_pair_rewrite
    @p2_pair @p2_pair_rewrite
    @pair_compose @compose_assoc : pair.

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

  (** Naturality *)

  Proposition assoc_nat {A1 B1 C1 A2 B2 C2} f g h :
    ((f & g) & h) @ assoc A1 B1 C1 = assoc A2 B2 C2 @ (f& (g & h)).
  Proof.
    unfold fmap. cbn.
    autorewrite with pair.
    reflexivity.
  Qed.

  Proposition lunit_nat {A1 A2 : C.t} (f : C.m A1 A2) :
    f @ lunit A1 = lunit A2 @ fmap (C.id unit) f.
  Proof.
    unfold fmap. cbn.
    autorewrite with pair.
    reflexivity.
  Qed.

  Proposition runit_nat {A1 A2 : C.t} (f : C.m A1 A2) :
    f @ runit A1 = runit A2 @ fmap f (C.id unit).
  Proof.
    unfold fmap. cbn.
    autorewrite with pair.
    reflexivity.
  Qed.

  (** Pentagon diagram *)

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

  (** Triangle diagram *)

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

(** Once we add in the definitions provided by [BifunctorTheory], we
  can check the result against [MonoidalStructure]. *)

Module Type CartesianStructure (C : Category) <: MonoidalStructure C :=
  CartesianStructureDefinition C <+
  CartesianStructureTheory C <+
  BifunctorTheory C C C.

(** ** Cartesian category interface *)

Module Type CartesianDefinition (C : Category).
  Declare Module Prod : MonoidalStructure C.
End CartesianDefinition.

Module CartesianTheory (C : Category) (M : CartesianDefinition C).
  Import C M.
  Notation T := Prod.unit.
  Infix "&" := Prod.omap (at level 40, left associativity) : obj_scope.
  Infix "&" := Prod.fmap : hom_scope.
End CartesianTheory.

Module Type Cartesian (C : Category) :=
  CartesianDefinition C <+
  CartesianTheory C.
