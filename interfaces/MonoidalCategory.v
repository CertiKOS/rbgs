Require Import interfaces.Category.
Require Import interfaces.Functor.


(** * Monoidal structures *)

(** Since a given category may involve several monoidal structures,
  we separate the corresponding interface into a submodule. *)

Module Type MonoidalStructureDefinition (C : Category).
  Import C.

  Include BifunctorDefinition C C C.

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

End MonoidalStructureDefinition.

Module MonoidalStructureTheory (C: Category) (M: MonoidalStructureDefinition C).
  Import C M.

  (** We provide versions of the naturality properties and coherence
    diagrams to use with the isomorphisms' backward directions. *)

  Theorem assoc_nat_bw {A1 B1 C1 A2 B2 C2} f g h :
    bw (assoc A2 B2 C2) @ fmap (fmap f g) h =
    fmap f (fmap g h) @ bw (assoc A1 B1 C1).
  Proof.
    apply eq_fw_bw_r_1. rewrite compose_assoc.
    apply eq_fw_bw_l_2. apply assoc_nat.
  Qed.

  Theorem lunit_nat_bw {A1 A2} f :
    bw (lunit A2) @ f = fmap (C.id unit) f @ bw (lunit A1).
  Proof.
    apply eq_fw_bw_r_1. rewrite compose_assoc.
    apply eq_fw_bw_l_2. apply lunit_nat.
  Qed.

  Theorem runit_nat_bw {A1 A2} f :
    bw (runit A2) @ f = fmap f (C.id unit) @ bw (runit A1).
  Proof.
    apply eq_fw_bw_r_1. rewrite compose_assoc.
    apply eq_fw_bw_l_2. apply runit_nat.
  Qed.

  Theorem assoc_coh_bw {A B C D} :
    fmap (C.id A) (bw (assoc B C D)) @
      bw (assoc A (omap B C) D) @
      fmap (bw (assoc A B C)) (C.id D) =
    bw (assoc A B (omap C D)) @
       bw (assoc (omap A B) C D).
  Proof.
    rewrite <- compose_id_left.
    rewrite <- fmap_id.
    rewrite <- (compose_id_left (id A)) at 2.
    rewrite <- (bw_fw (assoc B C D)).
    rewrite fmap_compose, !compose_assoc. f_equal.
    apply eq_fw_bw_l_2.
    rewrite <- !compose_assoc.
    apply (eq_fw_bw_r_1 (assoc (omap A B) C D)).
    apply (eq_fw_bw_r_1 (assoc A B (omap C D))).
    rewrite !compose_assoc.
    rewrite <- compose_id_left.
    rewrite <- fmap_id.
    rewrite <- (compose_id_left (id D)) at 2.
    rewrite <- (bw_fw (assoc A B C)).
    rewrite fmap_compose, !compose_assoc. f_equal.
    symmetry.
    apply assoc_coh.
  Qed.

  Theorem unit_coh_bw {A B} :
    bw (assoc A unit B) @ fmap (bw (runit A)) (C.id B) =
    fmap (C.id A) (bw (lunit B)).
  Proof.
    apply eq_fw_bw_l_2.
    rewrite <- compose_id_right at 1.
    rewrite <- fmap_id.
    rewrite <- (compose_id_left (id A)) at 1.
    rewrite <- (fw_bw (lunit B)) at 2.
    rewrite fmap_compose, <- !compose_assoc. f_equal.
    rewrite <- compose_id_left.
    rewrite <- fmap_id.
    rewrite <- (bw_fw (runit A)).
    rewrite <- (compose_id_left (id B)) at 2.
    rewrite fmap_compose, !compose_assoc. f_equal.
    symmetry. apply unit_coh.
  Qed.
End MonoidalStructureTheory.

Module Type MonoidalStructure (C : Category).
  Include MonoidalStructureDefinition C.
  Include BifunctorTheory C C C.
  Include MonoidalStructureTheory C.
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

Module Type MonoidalCategory :=
  Category.Category <+
  Monoidal.


(** * Monoidal closure *)

Module Type MonoidalClosureDefinition (C : Category) (M : MonoidalStructure C).
  Import C.
  Infix "*" := M.omap : obj_scope.
  Infix "*" := M.fmap : hom_scope.

  Include Bifunctor C.Op C C.

  Parameter curry : forall {A B C}, (M.omap A B ~~> C) -> (A ~~> omap B C).
  Parameter uncurry : forall {A B C}, (A ~~> omap B C) -> (M.omap A B ~~> C).

  Axiom uncurry_curry :
    forall {A B C} (f : A * B ~~> C), uncurry (curry f) = f.
  Axiom curry_uncurry :
    forall {A B C} (g : A ~~> omap B C), curry (uncurry g) = g.

  Axiom curry_natural_l :
    forall {A1 A2 B C} (x : A1 ~~> A2) (f : A2 * B ~~> C),
      curry (f @ (x * id B)) = curry f @ x.
  Axiom curry_natural_r :
    forall {A B C1 C2} (f : A * B ~~> C1) (y : C1 ~~> C2),
      curry (y @ f) = fmap (id B) y @ curry f.

End MonoidalClosureDefinition.

Module MonoidalClosureTheory (C : Category) (M : MonoidalStructure C)
  (W : MonoidalClosureDefinition C M).

  Import C W.

  Theorem curry_natural :
    forall {A1 A2 B C1 C2} (x : A1 ~~> A2) (f : A2 * B ~~> C1) (y : C1 ~~> C2),
      curry (y @ f @ (x * id B)) = fmap (id B) y @ curry f @ x.
  Admitted.

  (* Theorem uncurry_natural :
    .... *)

End MonoidalClosureTheory.


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
    @pair_pi
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
  BifunctorTheory C C C <+
  MonoidalStructureTheory C.

(** ** Cartesian category interface *)

Module Type CartesianDefinition (C : Category).
  Declare Module Prod : CartesianStructure C.
End CartesianDefinition.

Module CartesianTheory (C : Category) (M : CartesianDefinition C).
  Import C M.
  Notation T := Prod.unit.
  Infix "&&" := Prod.omap (at level 40, left associativity) : obj_scope.
  Infix "&&" := Prod.fmap : hom_scope.
End CartesianTheory.

Module Type Cartesian (C : Category) :=
  CartesianDefinition C <+
  CartesianTheory C.

Module Type CartesianCategory :=
  Category.Category <+
  Cartesian.


(** * Cocartesian monoidal structures *)

(** ** Definition *)

Module Type CocartesianStructureDefinition (C : Category).
  Import C.

  (* Initial object *)

  Parameter unit : t.
  Parameter ini : forall X, C.m unit X.

  Axiom ini_uni : forall {X} (x y : C.m unit X), x = y.

  (** Binary coproducts *)

  Parameter omap : t -> t -> t.
  Parameter i1 : forall {A B}, m A (omap A B).
  Parameter i2 : forall {A B}, m B (omap A B).
  Parameter copair : forall {X A B}, m A X -> m B X -> m (omap A B) X.

  Axiom copair_i1 : forall {X A B} (f : m A X) (g : m B X), copair f g @ i1 = f.
  Axiom copair_i2 : forall {X A B} (f : m A X) (g : m B X), copair f g @ i2 = g.
  Axiom iota_copair : forall {X A B} x, @copair X A B (x @ i1) (x @ i2) = x.

End CocartesianStructureDefinition.

(** ** Consequences *)

(** As with cartesian ones, cocartesian structures are a special case
  of monoidal structure. *)

Module CocartesianStructureTheory (C : Category) (P : CocartesianStructureDefinition C).
  Import C P.
  Local Infix "+" := omap (at level 50, left associativity) : obj_scope.

  (** *** Useful lemmas *)

  Lemma copair_i1_rewrite {X A B Y} (f : m A X) (g : m B X) (x : m Y A) :
    copair f g @ i1 @ x = f @ x.
  Proof.
    rewrite <- compose_assoc, copair_i1; auto.
  Qed.

  Lemma copair_i2_rewrite {X A B Y} (f : m A X) (g : m B X) (x : m Y B) :
    copair f g @ i2 @ x = g @ x.
  Proof.
    rewrite <- compose_assoc, copair_i2; auto.
  Qed.

  Lemma copair_uni {X A B} (x : m (omap A B) X) (f : m A X) (g : m B X) :
    x @ i1 = f ->
    x @ i2 = g ->
    x = copair f g.
  Proof.
    intros. subst.
    rewrite iota_copair. auto.
  Qed.

  Lemma copair_compose {X A B Y} (f : m A X) (g : m B X) (x : m X Y) :
    x @ copair f g = copair (x @ f) (x @ g).
  Proof.
    apply copair_uni.
    - rewrite compose_assoc, copair_i1. auto.
    - rewrite compose_assoc, copair_i2. auto.
  Qed.

  Global Hint Rewrite
    @copair_i1 @copair_i1_rewrite
    @copair_i2 @copair_i2_rewrite
    @iota_copair
    @copair_compose @compose_assoc : copair.

  (** *** Bifunctor structure *)

  Definition fmap {A1 A2 B1 B2} (f1 : m A1 B1) (f2 : m A2 B2) :=
    copair (i1 @ f1) (i2 @ f2).

  Proposition fmap_id (A B : t) :
    fmap (id A) (id B) = id (omap A B).
  Proof.
    unfold fmap. symmetry.
    apply copair_uni; rewrite compose_id_left, compose_id_right; auto.
  Qed.

  Proposition fmap_compose {A1 A2 B1 B2 C1 C2} :
    forall (g1 : m B1 C1) (g2 : m B2 C2) (f1: m A1 B1) (f2: m A2 B2),
      fmap (g1 @ f1) (g2 @ f2) = fmap g1 g2 @ fmap f1 f2.
  Proof.
    intros. unfold fmap. symmetry.
    apply copair_uni; autorewrite with copair; auto.
  Qed.

  Local Infix "+" := fmap : hom_scope.

  (** *** Monoidal structure *)

  Program Definition assoc (A B C : t) : C.iso (A + (B + C)) ((A + B) + C) :=
    {|
      fw := copair (i1 @ i1) (copair (i1 @ i2) i2);
      bw := copair (copair i1 (i2 @ i1)) (i2 @ i2);
    |}.
  Next Obligation.
    rewrite !copair_compose. symmetry.
    apply copair_uni; autorewrite with copair; auto using compose_id_left.
  Qed.
  Next Obligation.
    rewrite !copair_compose. symmetry.
    apply copair_uni; autorewrite with copair; auto using compose_id_left.
  Qed.

  Program Definition lunit (A : t) : iso (unit + A) A :=
    {|
      fw := copair (ini A) (id A);
      bw := i2;
    |}.
  Next Obligation.
    rewrite copair_compose. symmetry. apply copair_uni.
    - apply ini_uni.
    - rewrite compose_id_right, compose_id_left. auto.
  Qed.
  Next Obligation.
    apply copair_i2.
  Qed.

  Program Definition runit (A : t) : iso (A + unit) A :=
    {|
      fw := copair (id A) (ini A);
      bw := i1;
    |}.
  Next Obligation.
    rewrite copair_compose. symmetry. apply copair_uni.
    - rewrite compose_id_right, compose_id_left. auto.
    - apply ini_uni.
  Qed.
  Next Obligation.
    apply copair_i1.
  Qed.

  (** Naturality *)

  Proposition assoc_nat {A1 B1 C1 A2 B2 C2} f g h :
    ((f + g) + h) @ assoc A1 B1 C1 = assoc A2 B2 C2 @ (f + (g + h)).
  Proof.
    unfold fmap. cbn.
    autorewrite with copair.
    reflexivity.
  Qed.

  Proposition lunit_nat {A1 A2 : C.t} (f : C.m A1 A2) :
    f @ lunit A1 = lunit A2 @ fmap (C.id unit) f.
  Proof.
    unfold fmap. cbn.
    autorewrite with copair.
    rewrite compose_id_left, !compose_id_right.
    f_equal. apply ini_uni.
  Qed.

  Proposition runit_nat {A1 A2 : C.t} (f : C.m A1 A2) :
    f @ runit A1 = runit A2 @ fmap f (C.id unit).
  Proof.
    unfold fmap. cbn.
    autorewrite with copair.
    rewrite !compose_id_left, !compose_id_right.
    f_equal. apply ini_uni.
  Qed.

  (** Pentagon diagram *)

  Proposition assoc_coh (A B C D : t) :
    (assoc A B C + id D) @ assoc A (B + C) D @ (id A + assoc B C D) =
    assoc (A + B) C D @ assoc A B (C + D).
  Proof.
    unfold assoc, fmap; cbn.
    repeat
      (apply copair_uni ||
       rewrite ?compose_assoc, ?compose_id_left, ?compose_id_right ||
       autorewrite with copair); auto.
  Qed.

  (** Triangle diagram *)

  Proposition unit_coh (A B : t) :
    (runit A + id B) @ assoc A unit B = id A + lunit B.
  Proof.
    unfold runit, lunit, fmap; cbn.
    repeat
      (apply pair_uni ||
       rewrite ?compose_assoc, ?compose_id_left, ?compose_id_right ||
       autorewrite with copair); auto.
    repeat f_equal.
    apply ini_uni.
  Qed.

End CocartesianStructureTheory.

(** Once we add in the definitions provided by [BifunctorTheory], we
  can check the result against [MonoidalStructure]. *)

Module Type CocartesianStructure (C : Category) <: MonoidalStructure C :=
  CocartesianStructureDefinition C <+
  CocartesianStructureTheory C <+
  BifunctorTheory C C C <+
  MonoidalStructureTheory C.

(** ** Cocartesian category interface *)

Module Type CocartesianDefinition (C : Category).
  Declare Module Plus : CocartesianStructure C.
End CocartesianDefinition.

Module CocartesianTheory (C : Category) (M : CocartesianDefinition C).
  Import C M.
  Notation "0" := Plus.unit.
  Infix "+" := Plus.omap (at level 50, left associativity) : obj_scope.
  Infix "+" := Plus.fmap : hom_scope.
End CocartesianTheory.

Module Type Cocartesian (C : Category) :=
  CocartesianDefinition C <+
  CocartesianTheory C.

Module Type CocartesianCategory :=
  Category.Category <+
  Cocartesian.


(** * Monoidal functors *)

Module Type FunctorMonoidal (C D : Category) (CM : MonoidalStructure C)
  (DM : MonoidalStructure D) (F : Functor C D).

  Import (coercions, notations) D.

  Parameter omap_unit :
    D.iso DM.unit (F.omap CM.unit).

  Parameter omap_prod :
    forall X Y, D.iso (DM.omap (F.omap X) (F.omap Y)) (F.omap (CM.omap X Y)).

  Parameter omap_prod_nat :
    forall {X1 X2 Y1 Y2} (f : C.m X1 X2) (g : C.m Y1 Y2),
      omap_prod X2 Y2 @ DM.fmap (F.fmap f) (F.fmap g) =
      F.fmap (CM.fmap f g) @ omap_prod X1 Y1.

End FunctorMonoidal.

Module Type MonoidalFunctor (C D : MonoidalCategory) :=
  Functor.Functor C D <+
  FunctorMonoidal C D C.Tens D.Tens.
