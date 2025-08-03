Require Import interfaces.Category.
Require Import interfaces.Functor.


(** * Monoidal structures *)

(** Since a given category may involve several monoidal structures,
  we separate the corresponding interface into a submodule. *)

(** ** Definition *)

Module Type MonoidalStructureDefinition (C : Category).
  Import C.

  (** NB: we need the isomorphism preservation properties from
    [BifunctorTheory] in the [MonoidalStructureTheory] module,
    however including [BifunctorTheory] there creates an issue:
    in [FunctorCategory], functor composition involving three
    arbitrary categories is merely a bifunctor, but becomes a
    full-blown monoidal structure in the special case where the
    three categories are the same. As a result, by the time we add
    the monoidal structure, the base module we're extending is
    already a full-blown [Bifunctor] instance where [BifunctorTheory]
    has been included, and attempting to do it again in
    [MonoidalStructureTheory] creates a conflict. So here we simply
    use the full [Bifunctor] interface as a base and let the user
    decide when to incorporate it. We may want to use this approach
    in a more systematic way. *)

  Include Bifunctor C C C.

  (** *** Structural isomorphisms *)

  Parameter unit : C.t.
  Parameter assoc : forall A B C, C.iso (omap A (omap B C)) (omap (omap A B) C).
  Parameter lunit : forall A, C.iso (omap unit A) A.
  Parameter runit : forall A, C.iso (omap A unit) A.

  (** *** Naturality properties *)

  Axiom assoc_nat :
    forall {A1 B1 C1 A2 B2 C2: C.t} (f: C.m A1 A2) (g: C.m B1 B2) (h: C.m C1 C2),
      fmap (fmap f g) h @ assoc A1 B1 C1 = assoc A2 B2 C2 @ fmap f (fmap g h).

  Axiom lunit_nat :
    forall {A1 A2 : C.t} (f : C.m A1 A2),
      f @ lunit A1 = lunit A2 @ fmap (C.id unit) f.

  Axiom runit_nat :
    forall {A1 A2 : C.t} (f : C.m A1 A2),
      f @ runit A1 = runit A2 @ fmap f (C.id unit).

  (** *** Pentagon identity *)

  Axiom assoc_coh :
    forall A B C D : C.t,
      fmap (assoc A B C) (C.id D) @
        assoc A (omap B C) D @
        fmap (C.id A) (assoc B C D) =
      assoc (omap A B) C D @
        assoc A B (omap C D).

  (** *** Triangle identity *)

  Axiom unit_coh :
    forall A B : C.t,
      fmap (runit A) (C.id B) @ assoc A unit B =
      fmap (C.id A) (lunit B).

End MonoidalStructureDefinition.

(** ** Theory *)

Module MonoidalStructureTheory (C: Category) (M: MonoidalStructureDefinition C).
  Import C M.

  (** *** Naturality of backward maps *)

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

  (** *** Backward coherence diagrams *)

  Theorem assoc_coh_bw {A B C D} :
    fmap (C.id A) (bw (assoc B C D)) @
      bw (assoc A (omap B C) D) @
      fmap (bw (assoc A B C)) (C.id D) =
    bw (assoc A B (omap C D)) @
       bw (assoc (omap A B) C D).
  Proof.
    apply iso_eq_fw_bw; cbn; rewrite ?compose_assoc.
    apply assoc_coh.
  Qed.

  Theorem unit_coh_bw {A B} :
    bw (assoc A unit B) @ fmap (bw (runit A)) (C.id B) =
    fmap (C.id A) (bw (lunit B)).
  Proof.
    apply iso_eq_fw_bw; cbn; rewrite ?compose_assoc.
    apply unit_coh.
  Qed.
End MonoidalStructureTheory.

(** *** Overall interface *)

Module Type MonoidalStructure (C : Category).
  Include MonoidalStructureDefinition C.
  Include MonoidalStructureTheory C.
End MonoidalStructure.

(** ** Monodal categories *)

(** A monoidal category is a category with a submodule for
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

Module Type MonoidalClosureDefinition (C : CategoryWithOp) (M : MonoidalStructure C).
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

Module MonoidalClosureTheory (C : CategoryWithOp) (M : MonoidalStructure C)
  (W : MonoidalClosureDefinition C M).

  Import C W.

  Theorem curry_natural :
    forall {A1 A2 B C1 C2} (x : A1 ~~> A2) (f : A2 * B ~~> C1) (y : C1 ~~> C2),
      curry (y @ f @ (x * id B)) = fmap (id B) y @ curry f @ x.
  Admitted.

  (* Theorem uncurry_natural :
    .... *)

End MonoidalClosureTheory.


(** * Symmetric monoidal categories *)

(** ** Definition *)

Module Type SymmetricMonoidalStructureDefinition (C : Category).
  Include MonoidalStructureDefinition C.
  Import (notations, coercions) C.

  (** *** Swap map *)

  Parameter swap : forall A B, C.m (omap A B) (omap B A).

  (** *** Naturality *)

  Axiom swap_nat :
    forall {A1 A2 B1 B2} (f : C.m A1 A2) (g : C.m B1 B2),
      fmap g f @ swap A1 B1 = swap A2 B2 @ fmap f g.

  (** *** Coherence diagrams *)

  (** Hexagon identity *)

  Axiom swap_assoc :
    forall A B C,
      fmap (swap A C) (C.id B) @ assoc A C B @ fmap (C.id A) (swap B C) =
      assoc C A B @ swap (omap A B) C @ assoc A B C.

  (** Unit coherence *)

  Axiom runit_swap :
    forall A, runit A @ swap unit A = lunit A.

  (** *** Swap is its own inverse *)

  Axiom swap_swap :
    forall A B, swap B A @ swap A B = C.id (omap A B).

End SymmetricMonoidalStructureDefinition.

(** ** Theory *)

Module SymmetricMonoidalStructureTheory (C: Category) (M: SymmetricMonoidalStructureDefinition C).
  Import C M.
  Include MonoidalStructureTheory C M.

  (** *** Basic properties *)

  (** Since [swap_swap] already implies that [swap] is an isomorphism,
    we have the user define it as a simple morphism, but we provide
    the isomorphism version below in case it is needed. This kind of
    situation could be a reason to use a typeclass approach for
    isomorphisms instead of the current approach. *)

  Program Canonical Structure swap_iso A B : iso (omap A B) (omap B A) :=
    {|
      fw := swap A B;
      bw := swap B A;
    |}.
  Next Obligation.
    apply swap_swap.
  Qed.
  Next Obligation.
    apply swap_swap.
  Qed.

  Lemma lunit_swap A :
    lunit A @ swap A unit = runit A.
  Proof.
    rewrite <- runit_swap, compose_assoc.
    rewrite swap_swap, compose_id_right.
    reflexivity.
  Qed.

  (** *** Backward coherence diagrams *)

  (** Hexagon identity *)

  Proposition swap_assoc_bw A B C :
    fmap (id A) (swap C B) @ bw (assoc A C B) @ fmap (swap C A) (id B) =
    bw (assoc A B C) @ swap C (omap A B) @ bw (assoc C A B).
  Proof.
    apply iso_eq_fw_bw. cbn. rewrite ?compose_assoc.
    apply swap_assoc.
  Qed.

  (** Unit coherence *)

  Proposition lunit_swap_bw A :
    swap unit A @ bw (lunit A) = bw (runit A).
  Proof.
    apply iso_eq_fw_bw. cbn. rewrite ?compose_assoc.
    apply lunit_swap.
  Qed.

  Proposition runit_swap_bw A :
    swap A unit @ bw (runit A) = bw (lunit A).
  Proof.
    apply iso_eq_fw_bw. cbn. rewrite ?compose_assoc.
    apply runit_swap.
  Qed.

End SymmetricMonoidalStructureTheory.

Module Type SymmetricMonoidalStructure (C : Category) :=
  SymmetricMonoidalStructureDefinition C <+
  SymmetricMonoidalStructureTheory C.

Module Type SymmetricMonoidalDefinition (C : Category).
  Declare Module Tens : SymmetricMonoidalStructure C.
End SymmetricMonoidalDefinition.

Module SymmetricMonoidalTheory (C : Category) (M : SymmetricMonoidalDefinition C).
  Import C M.
  Include MonoidalTheory C M.

  Notation γ := Tens.swap.

End SymmetricMonoidalTheory.

Module Type SymmetricMonoidal (C : Category) :=
  SymmetricMonoidalDefinition C <+
  SymmetricMonoidalTheory C.

Module Type SymmetricMonoidalCategory :=
  Category.Category <+
  SymmetricMonoidal.


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
  Axiom pair_pi_compose : forall {X A B} x, @pair X A B (p1 @ x) (p2 @ x) = x.

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
    rewrite pair_pi_compose. auto.
  Qed.

  Lemma pair_pi A B :
    pair p1 p2 = id (omap A B).
  Proof.
    rewrite <- (compose_id_right p1), <- (compose_id_right p2).
    apply pair_pi_compose.
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
    - rewrite compose_id_right, !compose_assoc, !p1_pair, !p2_pair, pair_pi_compose. auto.
  Qed.
  Next Obligation.
    rewrite !pair_compose. symmetry. apply pair_uni.
    - rewrite compose_id_right, !compose_assoc, !p2_pair, !p1_pair, pair_pi_compose. auto.
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

  Definition swap (A B : t) : A & B ~~> B & A :=
    pair p2 p1.

  (** Naturality *)

  Proposition assoc_nat {A1 B1 C1 A2 B2 C2} f g h :
    ((f & g) & h) @ assoc A1 B1 C1 = assoc A2 B2 C2 @ (f & (g & h)).
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

  Proposition swap_nat {A1 A2 B1 B2} (f : C.m A1 A2) (g : C.m B1 B2) :
    (g & f) @ swap A1 B1 = swap A2 B2 @ (f & g).
  Proof.
    unfold fmap, swap. cbn.
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

  (** Hexagon diagram *)

  Proposition swap_assoc (A B C : t) :
    (swap A C & id B) @ assoc A C B @ (id A & swap B C) =
    assoc C A B @ swap (A & B) C @ assoc A B C.
  Proof.
    unfold swap, assoc, fmap; cbn.
    repeat
      (apply pair_uni ||
       rewrite ?compose_assoc, ?compose_id_left, ?compose_id_right ||
       rewrite ?p1_pair, ?p2_pair, ?pair_compose);
      auto.
  Qed.

  Proposition swap_swap (A B : t) :
    swap B A @ swap A B = id (omap A B).
  Proof.
    unfold swap, assoc, fmap; cbn.
    repeat
      (apply pair_uni ||
       rewrite ?compose_assoc, ?compose_id_left, ?compose_id_right ||
       rewrite ?p1_pair, ?p2_pair, ?pair_pi, ?pair_compose);
      auto.
  Qed.

  Proposition runit_swap (A : t) :
    runit A @ swap unit A = lunit A.
  Proof.
    unfold swap, assoc, fmap; cbn.
    repeat
      (apply pair_uni ||
       rewrite ?compose_assoc, ?compose_id_left, ?compose_id_right ||
       rewrite ?p1_pair, ?p2_pair, ?pair_compose);
      auto.
  Qed.

End CartesianStructureTheory.

(** Once we add in the definitions provided by [BifunctorTheory], we
  can check the result against [MonoidalStructure]. *)

Module Type CartesianStructure (C : Category) <: SymmetricMonoidalStructure C :=
  CartesianStructureDefinition C <+
  CartesianStructureTheory C <+
  BifunctorTheory C C C <+
  SymmetricMonoidalStructureTheory C.

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
  Axiom copair_iota_compose : forall {X A B} x, @copair X A B (x @ i1) (x @ i2) = x.

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
    rewrite copair_iota_compose. auto.
  Qed.

  Lemma copair_iota {A B} :
    copair i1 i2 = id (A + B).
  Proof.
    symmetry.
    apply copair_uni; apply compose_id_left.
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
    @copair_iota_compose
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

  Definition swap (A B : t) : m (A + B) (B + A) :=
    copair i2 i1.

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

  Proposition swap_nat {A1 A2 B1 B2} (f : C.m A1 A2) (g : C.m B1 B2) :
    (g + f) @ swap A1 B1 = swap A2 B2 @ (f + g).
  Proof.
    unfold fmap, swap. cbn.
    autorewrite with copair.
    reflexivity.
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

  (** Hexagon diagram *)

  Proposition swap_assoc (A B C : t) :
    (swap A C + id B) @ assoc A C B @ (id A + swap B C) =
    assoc C A B @ swap (A + B) C @ assoc A B C.
  Proof.
    unfold swap, assoc, fmap; cbn.
    repeat
      (apply pair_uni ||
       rewrite ?compose_assoc, ?compose_id_left, ?compose_id_right ||
       autorewrite with copair); auto.
  Qed.

  Proposition swap_swap (A B : t) :
    swap B A @ swap A B = id (omap A B).
  Proof.
    unfold swap, assoc, fmap; cbn.
    repeat
      (apply pair_uni ||
       rewrite ?compose_assoc, ?compose_id_left, ?compose_id_right ||
       autorewrite with copair); auto.
    apply copair_iota.
  Qed.

  Proposition runit_swap (A : t) :
    runit A @ swap unit A = lunit A.
  Proof.
    unfold swap, assoc, fmap; cbn.
    repeat
      (apply pair_uni ||
       rewrite ?compose_assoc, ?compose_id_left, ?compose_id_right ||
       autorewrite with copair); auto.
  Qed.

End CocartesianStructureTheory.

(** Once we add in the definitions provided by [BifunctorTheory], we
  can check the result against [MonoidalStructure]. *)

Module Type CocartesianStructure (C : Category) <: MonoidalStructure C :=
  CocartesianStructureDefinition C <+
  CocartesianStructureTheory C <+
  BifunctorTheory C C C <+
  SymmetricMonoidalStructureTheory C.

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
