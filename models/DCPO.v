Require Import interfaces.Category.
Require Import interfaces.ConcreteCategory.
Require Import coqrel.LogicalRelations.

(** * Definitions for DCPOs *)

(** ** Partial orders *)

Class PartialOrder (P : Type) :=
  {
    le : P -> P -> Prop;
    le_preo :> PreOrder le;
    le_po :> Antisymmetric P eq le;
  }.

Infix "[= " := le (at level 70).

Module Poset <: ConcreteCategory.

  Definition Structure (P : Type) :=
    PartialOrder P.

  Definition Morphism {P Q} `{Ple: PartialOrder P} `{Qle: PartialOrder Q} (f : P -> Q) :=
    Monotonic f (le ++> le).

  Instance id_mor `{PartialOrder} :
    Monotonic (fun x => x) (le ++> le).
  Proof.
    rauto.
  Qed.

  Instance compose_mor {A B C} `{PartialOrder A} `{PartialOrder B} `{PartialOrder C} :
    forall (g: B -> C) (f: A -> B),
      Monotonic g (le ++> le) ->
      Monotonic f (le ++> le) ->
      Monotonic (fun x => g (f x)) (le ++> le).
  Proof.
    intros.
    rauto.
  Qed.

  Include ConcreteCategoryTheory.
End Poset.

(** ** Directed-complete partial orders *)

Class Directed `{PartialOrder} (D : P -> Prop) :=
  directed : 
    (exists x, D x) /\
    (forall x y, D x -> D y -> exists z, D z /\ x [= z /\ y [= z).

Class IsSup `{PartialOrder} (D : P -> Prop) (u : P) :=
  {
    sup_ub x : D x -> x [= u;
    sup_lub y : (forall x, D x -> x [= y) -> u [= y;
  }.

Lemma sup_unique `{PartialOrder} (D : P -> Prop) (u v : P) :
  IsSup D u ->
  IsSup D v ->
  u = v.
Proof.
  intros Hu Hv.
  apply antisymmetry.
  - apply sup_lub. intros x Hx.
    apply sup_ub; auto.
  - apply sup_lub. intros x Hx.
    apply sup_ub; auto.
Qed.

Class DirectedComplete (P : Type) :=
  {
    dc_po :> PartialOrder P;
    dsup : forall D `{HD: !Directed D}, P;
    dsup_is_sup D `{!Directed D} :> IsSup D (dsup D);
  }.

Variant im {A B} (f : A -> B) (X : A -> Prop) : B -> Prop :=
  im_intro a : X a -> im f X (f a).

Require Import PropExtensionality.
Require Import FunctionalExtensionality.

Lemma im_id {A} (X : A -> Prop) :
  im (fun a => a) X = X.
Proof.
  apply functional_extensionality. intros x.
  apply propositional_extensionality. split.
  - intros [a Ha]; auto.
  - intros Hx. apply (im_intro (fun a => a)); auto.
Qed.

Lemma im_compose {A B C} (g : B -> C) (f : A -> B) (X : A -> Prop) :
  im (fun a => g (f a)) X = im g (im f X).
Proof.
  apply functional_extensionality. intros c.
  apply propositional_extensionality. split.
  - intros [a Ha]. auto using im_intro.
  - intros [_ [a Ha]]. apply (im_intro (fun a => (g (f a)))); auto.
Qed.

Class ScottContinuous {P Q} `{HP: DirectedComplete P} `{HQ: PartialOrder Q} (f : P -> Q) :=
  {
    sc_dsup_sup :>
      forall D `{!Directed D}, IsSup (im f D) (f (dsup D));
  }.

Lemma le_directed `{PartialOrder} p q :
  p [= q -> Directed (fun x => x = p \/ x = q).
Proof.
  intros Hpq. split.
  - exists p; auto.
  - intros x y Hx Hy.
    destruct Hx, Hy; subst; eauto using (reflexivity (R:=le)).
Qed.

Instance sc_le `{ScottContinuous} :
  Monotonic f (le ++> le).
Proof.
  intros x y Hxy.
  set (D := fun a => a = x \/ a = y).
  assert (HD : Directed D).
  {
    apply le_directed; auto.
  }
  assert (Hy : dsup D = y).
  {
    apply antisymmetry.
    - apply sup_lub.
      intros z [Hz|Hz]; subst; auto.
      reflexivity.
    - apply sup_ub.
      right.
      reflexivity.
  }
  rewrite <- Hy.
  apply sup_ub.
  constructor. red. auto.
Qed.

Instance im_directed {P Q} `{!PartialOrder P} `{!PartialOrder Q} (f : P -> Q) (D : P -> Prop) :
  Monotonic f (le ++> le) ->
  Directed D ->
  Directed (im f D).
Proof.
  intros Hf [Hex HD]. split.
  - destruct Hex as [x H]. exists (f x). constructor. exact H.
  - intros _ _ [x Hx] [y Hy].
    edestruct (HD x y) as (z & Hz & Hxz & Hyz); auto.
    eauto 10 using im_intro.
Qed.

Lemma sc_dsup {P Q} `{!DirectedComplete P} `{!DirectedComplete Q} (f:P->Q) `{!ScottContinuous f}:
  forall D `{!Directed D}, f (dsup D) = dsup (im f D).
Proof.
  intros D HD.
  apply (sup_unique (im f D)).
  - apply sc_dsup_sup.
  - apply dsup_is_sup.
Qed.

Module DCPO <: ConcreteCategory.

  Definition Structure :=
    DirectedComplete.

  Definition Morphism {P Q} `{!DirectedComplete P} `{!DirectedComplete Q} (f: P->Q) :=
    ScottContinuous f.

  Instance id_mor `{DirectedComplete} :
    ScottContinuous (fun p => p).
  Proof.
    constructor.
    intros D HD.
    rewrite im_id.
    typeclasses eauto.
  Qed.

  Instance compose_mor {A B C} `{DirectedComplete A} `{DirectedComplete B} `{DirectedComplete C} :
    forall (g: B -> C) (f: A -> B),
      ScottContinuous g ->
      ScottContinuous f ->
      ScottContinuous (fun x => g (f x)).
  Proof.
    intros g f Hg Hf.
    constructor.
    intros D HD.
    rewrite (sc_dsup f).
    rewrite (sc_dsup g).
    rewrite im_compose.
    typeclasses eauto.
  Qed.

  Include ConcreteCategoryTheory.
End DCPO.
