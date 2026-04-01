Require Import FunctionalExtensionality.
Require Import PropExtensionality.
Require Import ProofIrrelevance.
Require Import Program.
Require Import coqrel.LogicalRelations.
Require Import interfaces.Category.
Require Import interfaces.ConcreteCategory.
Require Import structures.Posets.

(** * Directed-complete partial orders *)

(** The semantics of loops, iteration or recursion are often computed
  as limits of sequences of increasingly terminating computations.
  ...

 *)

(** ** Directed sets *)

(** *** Definition *)

(** Since we are primarily interested in bounded dcpos,
  we use a non-standard definition of directed set which permits
  empty sets. This allows us to treat the lower bound uniformly
  as a directed supremum. *)

Class Directed `{PartialOrder} {I} (x : I -> P) :=
  directed : forall i j, exists k, R (x i) (x k) /\ R (x j) (x k).

Global Instance Empty_set_directed `{PartialOrder} (x : Empty_set -> P) :
  Directed x.
Proof.
  intros [ ].
Qed.  

Global Instance unit_set_directed `{PartialOrder} (x : unit -> P) :
  Directed x.
Proof.
  intros [ ] [ ]. exists tt.
  split; reflexivity.
Qed.

Lemma pair_directed `{PartialOrder} (x y : P) :
  R x y ->
  Directed (bool_rect _ y x).
Proof.
  intros Hxy i j. exists true. cbn.
  destruct i, j; cbn; split; auto; reflexivity.
Qed.

Global Hint Extern 1 (Directed _) =>
  apply pair_directed; assumption : typeclass_instances.

(** ** DCPOs *)

(** A directed-complete partial order is a poset where every directed
  subset has a supremum. Since we define directed sets as possibly
  empty, the resulting structure is a bounded dcpo. *)

Class DCPO (P : Type) :=
  {
    lce : relation P;
    lce_po :> PartialOrder lce;
    dsup : forall {I} (x : I -> P) `{Hx: !Directed x}, P;
    dsup_is_sup {I} (x : I -> P) `{!Directed x} :> IsSup x (dsup x);
  }.

(** *** Properties of [dsup] *)

(** For convenience, we provide specialized versions of
  the supremum properties. *)

Lemma dsup_ub `{DCPO} {I} (x : I -> P) `{Dx : !Directed x} (i : I) :
  lce (x i) (dsup x).
Proof.
  apply sup_ub.
Qed.

Lemma dsup_lub `{DCPO} {I} (x : I -> P) `{Dx : !Directed x} (y : P) :
  (forall i, lce (x i) y) -> lce (dsup x) y.
Proof.
  apply sup_lub.
Qed.

(** *** Least element *)

Definition bot `{DCPO} :=
  dsup (Empty_set_rect _).

Lemma bot_lb `{DCPO} x :
  lce bot x.
Proof.
  apply sup_lub. tauto.
Qed.

(** *** Binary case for [dsup] *)

(** In some proofs below we will need to express ordering
  in terms of directed suprema of pairs. Below we provide
  the relevant properties. *)

Definition bset {A} (x y : A) : bool -> A :=
  bool_rect _ y x.

Lemma bset_natural {A B} (f : A -> B) (x y : A) :
  bset (f x) (f y) = fun i => f (bset x y i).
Proof.
  apply functional_extensionality.
  intros [|]; reflexivity.
Qed.

(** Pairs like the ones defined above are directed when
  the two elements are related. *)

Lemma bset_directed_r `{DCPO} (x y : P) :
  lce x y -> Directed (bset x y).
Proof.
  intros Hxy i j. exists true. cbn.
  destruct i, j; cbn; split; auto; reflexivity.
Qed.

Global Hint Extern 1 (Directed _) =>
  apply bset_directed_r; assumption : typeclass_instances.

Lemma bset_directed_l `{DCPO} (x y : P) :
  lce y x -> Directed (bset x y).
Proof.
  intros Hxy i j. exists false. cbn.
  destruct i, j; cbn; split; auto; reflexivity.
Qed.

Global Hint Extern 1 (Directed _) =>
  apply bset_directed_l; assumption : typeclass_instances.

(** Moreover, the supremum is the largest of the two elements. *)

Lemma lce_dsup_r `{DCPO} (x y : P) `{Dxy: !Directed (bset x y)} :
  lce x y -> dsup (bset x y) = y.
Proof.
  intros Hxy.
  apply antisymmetry.
  - apply dsup_lub. intros [|]; cbn; auto. reflexivity.
  - apply (dsup_ub (bset x y) true).
Qed.

Lemma lce_dsup_l `{DCPO} (x y : P) `{Dxy: !Directed (bset x y)} :
  lce y x -> dsup (bset x y) = x.
Proof.
  intros Hxy.
  apply antisymmetry.
  - apply dsup_lub. intros [|]; cbn; auto. reflexivity.
  - apply (dsup_ub (bset x y) false).
Qed.

(** ** Derived DCPOs *)

(** *** Binary products *)

(** *** Dependent products *)

Section FORALL_DCPO.
  Context {I} {P : I -> Type} `{Pdcpo : forall i:I, DCPO (P i)}.
  Obligation Tactic := cbn.

  Local Instance forall_dcpo_po :
    PartialOrder (P := forall i, P i) (forallr - @ i, lce).
  Proof.
    repeat split.
    - intros x i.
      reflexivity.
    - intros x y z Hxy Hyz i.
      etransitivity; eauto.
    - intros x y Hxy Hyx.
      apply functional_extensionality_dep. intros i.
      apply antisymmetry; auto.
  Qed.

  Global Instance forall_directed {J} (x : J -> forall i:I, P i) (i : I) :
    Directed x ->
    Directed (fun j => x j i).
  Proof.
    firstorder.
  Qed.

  Global Instance forall_issup {J} (x: J -> forall i, P i) (y: forall i, P i) :
    (forall i, IsSup (fun j => x j i) (y i)) ->
    IsSup x y.
  Proof.
    intros Hy.
    split.
    - firstorder.
    - intros z Hxz i.
      apply sup_lub.
      firstorder.
  Qed.

  Global Program Instance forall_dcpo : DCPO (forall i, P i) :=
    {
      lce := forallr - @ i, lce;
      dsup J x Hx i := dsup (fun j => x j i);
    }.
End FORALL_DCPO.

(** ** Scott-continuous functions *)

Module DCPO <: ConcreteCategory.

  Class Structure (P : Type) : Type :=
    structure_dcpo : DCPO P.

  Global Hint Immediate structure_dcpo : typeclass_instances.
  Global Hint Extern 1 (Structure _) => red : typeclass_instances.

  (** *** Definition *)

  (** A Scott-continuous function preserves all directed suprema.
    Note that the image oof the directed set is itself directed
    only by virtue of the monotonicity implied by Scott-continuity.
    So we cannot formulate Scott-continuity directly in terms of
    the target's [dsup] operation. *)

  Class Morphism {A B} `{Adcpo: DCPO A} `{Bdcpo: DCPO B} (f : A -> B) :=
    scott_continuous :>
      forall {I} (x : I -> A) `{Hx : !Directed x},
        IsSup (fun i => f (x i)) (f (dsup x)).

  (** Nevertheless, if we know the target set to be directed,
    we can write the equation in the expected way. *)

  Lemma dsup_mor `{Morphism} {I} (x : I -> A)
    `{Dx: !Directed x} `{Dy: !Directed (fun i => f (x i))} :
      f (dsup x) = dsup (fun i => f (x i)).
  Proof.
    apply (sup_unique (fun i => f (x i))); typeclasses eauto.
  Qed.

  (** *** Monotonicity *)

  (** Scott-continuity implies monotonicity. This is because [x <= y]
    if and only if [y] is the supremum of the pair [{x, y}]. *)

  Global Instance morphism_lce :
    forall `(Morphism), Monotonic f (lce ++> lce).
  Proof.
    intros A B Adcpo Bdcpo f Hf x y Hxy.
    rewrite <- (lce_dsup_r x y) by auto.
    apply sup_at with false. reflexivity.
  Qed.

  (** In turn, this means that the image of a directed set is
    itself directed, making it easier to use [dsup_mor]. *)

  Lemma directed_mor `{Morphism} {I} (x : I -> A) :
    Directed x ->
    Directed (fun i => f (x i)).
  Proof.
    intros Dx i j.
    destruct (directed i j) as (k & Hi & Hj).
    exists k. split; rauto.
  Qed.

  Global Hint Extern 1 (Directed (fun i => _)) =>
    apply directed_mor : typeclass_instances.

  (** *** Composition *)

  Global Instance id_mor `{DCPO} :
    Morphism (fun x => x).
  Proof.
    intros I x Hx.
    typeclasses eauto.
  Qed.

  Global Instance compose_mor :
    forall {A B C} `{DCPO A} `{DCPO B} `{DCPO C} (g: B -> C) (f: A -> B),
      Morphism g ->
      Morphism f ->
      Morphism (fun x => g (f x)).
  Proof.
    intros A B C HA HB HC g f Hg Hf I x Hx.
    rewrite (dsup_mor x).
    apply scott_continuous.
  Qed.

  Include ConcreteCategoryTheory.

End DCPO.

Notation dcpo := DCPO.structured_set.
