Require Export coqrel.LogicalRelations.
Require Import interfaces.ConcreteCategory.


(** * Partially ordered sets *)

(** ** Unbundled definitions *)

(** We use posets for multiple purposes which we want to keep
  separated as much as possible. For example, specification refinement
  orderings and the dcpos used to compute the semantics of iteration
  will sometime be separate orders although they are defined on the
  same carrier set. In order to still share definitions between these
  two applications, we first provide an unbundled version of
  order-delated definitions where the relation [R] involved is
  an unbundled parameter. *)

Class PartialOrder {P} (R : relation P) :=
  {
    po_preorder :> PreOrder R;
    po_antisym :> Antisymmetric P eq R;
  }.

(** *** Suprema *)

Class IsSup `{PartialOrder} {I} (x : I -> P) (u : P) :=
  {
    sup_ub i : R (x i) u;
    sup_lub y : (forall i, R (x i) y) -> R u y;
  }.

Section SUP_PROPERTIES.
  Context `{Ppo : PartialOrder}.

  Lemma sup_unique {I} (x : I -> P) (u v : P) :
    IsSup x u ->
    IsSup x v ->
    u = v.
  Proof.
    intros Hu Hv.
    apply antisymmetry.
    - apply sup_lub. intro. apply sup_ub.
    - apply sup_lub. intro. apply sup_ub.
  Qed.

  Lemma sup_at {I y u} `{Hu : !IsSup y u} (i : I) (x : P) :
    R x (y i) -> R x u.
  Proof.
    intros; etransitivity; eauto; apply sup_ub.
  Qed.

  Lemma sup_iff {I} (x : I -> P) {u : P} `{Hz : !IsSup x u} (y : P) :
    R u y <-> forall i, R (x i) y.
  Proof.
    split.
    - intros H i. etransitivity; eauto using sup_ub.
    - apply sup_lub.
  Qed.
End SUP_PROPERTIES.

(** *** Infrema *)

Class IsInf `{PartialOrder} {I} (y : I -> P) (u : P) :=
  {
    inf_lb i : R u (y i);
    inf_glb x : (forall i, R x (y i)) -> R x u;
  }.

Section INF_PROPERTIES.
  Context `{Rpo : PartialOrder}.

  Lemma inf_unique {I} (x : I -> P) (u v : P) :
    IsInf x u ->
    IsInf x v ->
    u = v.
  Proof.
    intros Hu Hv.
    apply antisymmetry.
    - apply inf_glb. intro. apply inf_lb.
    - apply inf_glb. intro. apply inf_lb.
  Qed.

  Lemma inf_at {I x u} `{Hu : !IsInf x u} (i : I) (y : P) :
    R (x i) y -> R u y.
  Proof.
    intros; etransitivity; eauto. apply inf_lb.
  Qed.

  Lemma inf_iff {I} (y : I -> P) {u : P} `{Hu : !IsInf y u} (x : P) :
    R x u <-> forall i, R x (y i).
  Proof.
    split.
    - intros H i. etransitivity; eauto using inf_lb.
    - apply inf_glb.
  Qed.
End INF_PROPERTIES.

(** ** As extra structure for sets *)

(** The main role of posets in our development is as the core
  structure of refinement spaces. The name used in the semi-bundled
  version below for the ordering relation reflects this use. *)

Class Poset (P : Type) :=
  {
    ref : relation P;
    ref_po :> PartialOrder ref;
  }.

Module Poset <: ConcreteCategory.

  Class Structure (P : Type) : Type :=
    structure_poset : Poset P.

  Global Hint Immediate structure_poset : typeclass_instances.
  Global Hint Extern 1 (Structure _) => red : typeclass_instances.

  Class Morphism {A B} `{Apos: Poset A} `{Bpos: Poset B} (f : A -> B) :=
    morphism_monotonic :> Monotonic f (ref ++> ref).

  Global Instance id_mor `{Poset} :
    Morphism (fun x => x).
  Proof.
    firstorder.
  Qed.

  Global Instance compose_mor :
    forall {A B C} `{Poset A} `{Poset B} `{Poset C} (g: B -> C) (f: A -> B),
      Morphism g ->
      Morphism f ->
      Morphism (fun x => g (f x)).
  Proof.
    firstorder.
  Qed.

  Include ConcreteCategoryTheory.

End Poset.

Notation poset := Poset.structured_set.

Declare Scope poset_scope.
Delimit Scope poset_scope with poset.
Bind Scope poset_scope with poset.

Declare Scope poselt_scope.
Delimit Scope poselt_scope with poselt.
Bind Scope poselt_scope with Poset.carrier.

Infix "<=" := ref.
