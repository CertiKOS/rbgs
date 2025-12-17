Require Import interfaces.Category.
Require Import interfaces.Functor.
Require Import interfaces.MonoidalCategory.
Require Import interfaces.FunctorCategory.
Require Import FunctionalExtensionality.
Require Import ProofIrrelevance.


(** * Terminal Object *)

Module Type TerminalsDefinition (C : CategoryDefinition).

  Parameter unit: C.t.
  Parameter ter : forall X, C.m X unit.

  Axiom ter_uni : forall {X} (x y : C.m X unit), x = y.

End TerminalsDefinition.

Module Type Terminals (C : CategoryDefinition) :=
  TerminalsDefinition C.

Module TerminalFromCartesian (C : CartesianCategory) <: Terminals C.
  Import C.

  Definition unit := C.Prod.unit.
  Definition ter := C.Prod.ter.

  Proposition ter_uni : forall {X} (x y : C.m X unit), x = y.
  Proof.
    unfold unit. intros X. exact C.Prod.ter_uni.
  Qed.

End TerminalFromCartesian.

(** * Products *)

(** ** Category with all products *)

Module Type ProductsDefinition (C : CategoryDefinition).

  Parameter prod : forall {I}, (I -> C.t) -> C.t.
  Parameter pi : forall {I A}, forall i:I, C.m (prod A) (A i).
  Parameter tuple : forall {I X A}, (forall i:I, C.m X (A i)) -> C.m X (prod A).

  Axiom pi_tuple :
    forall {I X A} (f : forall i:I, C.m X (A i)),
      forall i, C.compose (pi i) (tuple f) = f i.

  Axiom tuple_pi :
    forall {I X A} (x : C.m X (@prod I A)),
      tuple (fun i => C.compose (pi i) x) = x.

End ProductsDefinition.

Module ProductsTheory (C : CategoryDefinition) (P : ProductsDefinition C).
  Import P.

  Lemma pi_tuple_rewrite {I X Y A} (f : forall i:I, C.m Y (A i)) (g : C.m X Y) :
    forall i, C.compose (pi i) (C.compose (tuple f) g) = C.compose (f i) g.
  Proof.
    intros i.
    rewrite <- C.compose_assoc, P.pi_tuple.
    reflexivity.
  Qed.

  Lemma tuple_uni {I X A} (f : forall i:I, C.m X (A i)) (x : C.m X (prod A)) :
    (forall i, C.compose (pi i) x = f i) -> x = tuple f.
  Proof.
    intros H.
    replace f with (fun i => C.compose (pi i) x).
    - rewrite tuple_pi. reflexivity.
    - apply functional_extensionality_dep; auto.
  Qed.
End ProductsTheory.

Module Type Products (C : CategoryDefinition) :=
  ProductsDefinition C <+
  ProductsTheory C.

(** ** Derived cartesian structure *)

(** If we have all products then in particular with have a cartesian
  structure. However in some cases the derived structure below is not
  the most natural or convenient definition. For example in [SET] we
  will want to use Rocq's built-in [unit] and [prod] types to define
  the cartesian structure rather than the equivalent but awkward
  [forall i:Empty_set, _] and [forall i:bool, if i then A else B].
  Hence we don't include the following in [ProductsTheory] but provide
  it separately to use as needed. *)

Module CartesianStructureFromProducts (C : Category) (P : Products C)
    <: CartesianStructure C.

  Definition unit :=
    P.prod (fun i : Empty_set => match i with end).

  Definition ter X : C.m X unit :=
    P.tuple (fun i : Empty_set => match i with end).

  Proposition ter_uni {X} (x y : C.m X unit) :
    x = y.
  Proof.
    cut (forall x, x = ter X); try firstorder congruence.
    clear. intro x.
    apply P.tuple_uni. intros [].
  Qed.

  Definition omap A B :=
    P.prod (fun i:bool => if i then A else B).

  Definition p1 {A B} : C.m (omap A B) A :=
    P.pi true.

  Definition p2 {A B} : C.m (omap A B) B :=
    P.pi false.

  Definition pair {X A B} (f : C.m X A) (g : C.m X B) : C.m X (omap A B) :=
    P.tuple
      (fun i:bool => if i return C.m X (if i then A else B) then f else g).

  Proposition p1_pair {X A B} (f : C.m X A) (g : C.m X B) :
    C.compose p1 (pair f g) = f.
  Proof.
    exact
      (P.pi_tuple (A := fun i:bool => if i then A else B)
         (fun i:bool => if i return C.m X (if i then A else B) then f else g)
         true).
  Qed.

  Proposition p2_pair {X A B} (f : C.m X A) (g : C.m X B) :
    C.compose p2 (pair f g) = g.
  Proof.
    exact
      (P.pi_tuple (A := fun i:bool => if i then A else B)
         (fun i:bool => if i return C.m X (if i then A else B) then f else g)
         false).
  Qed.

  Proposition pair_pi_compose {X A B} (x : C.m X (omap A B)) :
    pair (C.compose p1 x) (C.compose p2 x) = x.
  Proof.
    unfold pair, p1, p2.
    set (f := (fun i : bool => if i return (C.m X (if i then A else B))
                               then C.compose (P.pi true) x
                               else C.compose (P.pi false) x)).
    change (P.tuple f = x).
    replace f with (fun i => C.compose (P.pi i) x).
    - apply P.tuple_pi.
    - apply functional_extensionality_dep.
      intros [|]; reflexivity.
  Qed.

  Include CartesianStructureTheory C.
  Include BifunctorTheory C C C.
  Include SymmetricMonoidalStructureTheory C.
End CartesianStructureFromProducts.

Module CartesianFromProducts (C : Category) (P : Products C) <: Cartesian C.
  Module Prod := CartesianStructureFromProducts C P.
  Include CartesianTheory C.
End CartesianFromProducts.

(** ** Preservation *)

(** Note that this only works when both the source and target category
  have all products. It would be preferable to define product
  preservation when particular products may or may not exist in [C]
  and [D]; when all products do exist the definition would be
  equivalent to the following. However this would require basing the
  definition on a notion of an object and projection morphisms being
  a product, which would be best defined elsewhere. *)

Module Type PreservesProducts (C : CategoryDefinition) (D : Category)
  (PC : Products C) (PD : Products D) (F : FunctorDefinition C D).

  Import (notations, coercions) D.

  Parameter omap_prod :
    forall {I} (A : I -> C.t),
      D.iso (F.omap (PC.prod A)) (PD.prod (fun i => F.omap (A i))).

  Parameter fmap_pi :
    forall {I} (A : I -> C.t) (i : I),
      F.fmap (PC.pi i) = PD.pi i @ omap_prod A.

End PreservesProducts.


(** * Coproducts *)

(** ** Category with all coproducts *)

Module Type CoproductsDefinition (C : CategoryDefinition).

  Parameter coprod : forall {I}, (I -> C.t) -> C.t.
  Parameter iota : forall {I A}, forall i:I, C.m (A i) (coprod A).
  Parameter cotuple : forall {I X A}, (forall i:I, C.m (A i) X) -> C.m (coprod A) X.

  Axiom cotuple_iota :
    forall {I X A} (f : forall i:I, C.m (A i) X),
      forall i, C.compose (cotuple f) (iota i) = f i.

  Axiom iota_cotuple :
    forall {I X A} (x : C.m (@coprod I A) X),
      cotuple (fun i => C.compose x (iota i)) = x.

End CoproductsDefinition.

Module CoproductsTheory (C : CategoryDefinition) (P : CoproductsDefinition C).
  Import P.

  Lemma cotuple_iota_rewrite {I X Y A} (f: forall i:I, C.m (A i) Y) i (g: C.m X (A i)):
    C.compose (cotuple f) (C.compose (iota i) g) = C.compose (f i) g.
  Proof.
    rewrite <- C.compose_assoc, P.cotuple_iota.
    reflexivity.
  Qed.

  Lemma cotuple_uni {I X A} (f : forall i:I, C.m (A i) X) (x : C.m (coprod A) X) :
    (forall i, C.compose x (iota i) = f i) -> x = cotuple f.
  Proof.
    intros H.
    replace f with (fun i => C.compose x (iota i)).
    - rewrite iota_cotuple. reflexivity.
    - apply functional_extensionality_dep; auto.
  Qed.
End CoproductsTheory.

Module Type Coproducts (C : CategoryDefinition) :=
  CoproductsDefinition C <+
  CoproductsTheory C.


(** * Limits in general *)

(** Limits of shape [J] in a category [C] *)

Module LimitsPreliminaries (J C : CategoryDefinition).

  Module Diagram := FunctorCategory J C.

  (** A cone over a diagram *)

  Record cone {F : Diagram.t} :=
    {
      vertex :> C.t;
      edge (j : J.t) : C.m vertex (Diagram.oapply F j);
      face {i j} (f : J.m i j) :
        C.compose (Diagram.fapply F f) (edge i) = edge j;
    }.

  Arguments cone : clear implicits.

  Record cone_mor {F} {x y : cone F} :=
    {
      vertex_mor :> C.m x y;
      edge_mor j : C.compose (edge y j) vertex_mor = edge x j;
    }.

  Arguments cone_mor {_} _ _.

  Lemma cone_mor_eq {F x y} (m1 m2 : @cone_mor F x y) :
    vertex_mor m1 = vertex_mor m2 -> m1 = m2.
  Proof.
    destruct m1 as [m1 Hm1], m2 as [m2 Hm2]; cbn.
    intros H. subst. f_equal.
    apply proof_irrelevance.
  Qed.

  (** A limit is a terminal cone *)

  Class Limit {F} (l : cone F) :=
    {
      lim_mor (x : cone F) : cone_mor x l;
      lim_uni {x} (m : cone_mor x l) : m = lim_mor x;
    }.

End LimitsPreliminaries.

Module Type Limits (J C : CategoryDefinition).
  Include LimitsPreliminaries J C.

  Parameter lim : forall F, cone F.
  Axiom lim_spec : forall F, Limit (lim F).

  Global Existing Instance lim_spec.
End Limits.

Module Type Colimits (J : CategoryDefinition) (C : CategoryWithOp) :=
  Limits J C.Op.

(** ** Specific types of limits *)

Require Import MonoidalCategory.

(** The discrete category with two objects is used for the product and
  coproduct diagrams. *)

Module D2 <: Category.
  Unset Program Cases.

  Variant m_def : bool -> bool -> Type :=
    | id_def A : m_def A A.

  Definition t : Type := bool.
  Definition m : t -> t -> Type := m_def.

  Definition id : forall A, m A A := id_def.

  Program Definition compose {A B C} (g : m B C) : m A B -> m A C :=
    match g with
      | id_def A => fun f => f
    end.

  Lemma compose_id_left {A B} (f : m A B) :
    compose (id B) f = f.
  Proof.
    destruct f; cbn; auto.
  Qed.

  Lemma compose_id_right {A B} (f : m A B) :
    compose f (id A) = f.
  Proof.
    destruct f; cbn; auto.
  Qed.

  Lemma compose_assoc {A B C D} (f : m A B) (g : m B C) (h : m C D) :
    compose (compose h g) f = compose h (compose g f).
  Proof.
    destruct f, h; inversion g; subst; cbn; auto.
  Qed.

  Include CategoryTheory.
End D2.

Module CartesianStructureLimit (C : CartesianCategory).
  Unset Program Cases.
  Include LimitsPreliminaries D2 C.
  Import (notations) C.

  Program Definition prod_d (A B : C.t) : Diagram.t :=
    {|
      Diagram.oapply j := if j then A else B;
      Diagram.fapply i j f :=
        match f with D2.id_def j => C.id (if j then A else B) end;
    |}.
  Next Obligation.
    destruct f, g; cbn.
    rewrite C.compose_id_left; auto.
  Qed.

  Program Canonical Structure prod_c A B : cone (prod_d A B) :=
    {|
      vertex := A && B;
      edge j :=
        if j return A && B ~~> Diagram.oapply (prod_d A B) j
        then C.Prod.p1
        else C.Prod.p2;
    |}.
  Next Obligation.
    destruct f, A0; rewrite C.compose_id_left; auto.
  Qed.

  Global Program Instance prod_c_lim {A B} : Limit (prod_c A B) :=
    {
      lim_mor k := {| vertex_mor := C.Prod.pair (edge k true) (edge k false) |};
    }.
  Next Obligation.
    destruct j.
    - apply C.Prod.p1_pair.
    - apply C.Prod.p2_pair.
  Qed.
  Next Obligation.
    apply cone_mor_eq. cbn.
    apply C.Prod.pair_uni.
    - apply (edge_mor (y := prod_c A B) m true).
    - apply (edge_mor (y := prod_c A B) m false).
  Qed.
End CartesianStructureLimit.
