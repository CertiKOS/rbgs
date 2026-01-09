Require Import interfaces.Category.
Require Import interfaces.Functor.
Require Import interfaces.Monads.
Require Import interfaces.MonoidalCategory.
Require Import interfaces.Limits.

Require Import models.Sets.

Require Import FunctionalExtensionality.

Import SET.

(** * The Action monad *)

(** The [Action X] type represents a computation that either
    produces a value of type [X] (via [act]), or performs
    a silent/internal transition (via [tau]). *)

Inductive Action (X : Type) : Type := tau | act (x : X).
Arguments tau {_}.
Arguments act {_} _.


(** ** Action as a monad on SET *)

(** We use the [MonadDefinition] interface from [interfaces.Monads],
    which provides the Kleisli category for free via [MonadTheory]. *)

Module ActionMonad <: MonadDefinition SET.

  Definition omap := Action.

  Definition fmap {A B} (f : A -> B) (a : Action A) : Action B :=
    match a with
    | tau => tau
    | act x => act (f x)
    end.

  Definition eta X : SET.m X (omap X) := act.

  Definition mu X (a : Action (Action X)) : Action X :=
    match a with
    | tau => tau
    | act tau => tau
    | act (act x) => act x
    end.

  Proposition fmap_id A :
    fmap (SET.id A) = SET.id (omap A).
  Proof.
    extensionality a; destruct a; reflexivity.
  Qed.

  Proposition fmap_compose {A B C} (g : SET.m B C) (f : SET.m A B) :
    fmap (SET.compose g f) = SET.compose (fmap g) (fmap f).
  Proof.
    extensionality a; destruct a; reflexivity.
  Qed.

  Proposition eta_natural {X Y} (f : SET.m X Y) :
    SET.compose (eta Y) f = SET.compose (fmap f) (eta X).
  Proof.
    reflexivity.
  Qed.

  Proposition mu_natural {X Y} (f : SET.m X Y) :
    SET.compose (mu Y) (fmap (fmap f)) = SET.compose (fmap f) (mu X).
  Proof.
    extensionality a; unfold SET.compose, fmap, mu.
    repeat destruct a as [| a]; reflexivity.
  Qed.

  Proposition mu_eta_l X :
    SET.compose (mu X) (eta (omap X)) = SET.id (omap X).
  Proof.
    extensionality a; destruct a; reflexivity.
  Qed.

  Proposition mu_eta_r X :
    SET.compose (mu X) (fmap (eta X)) = SET.id (omap X).
  Proof.
    extensionality a; unfold SET.compose, SET.id, fmap, mu.
    repeat destruct a as [| a]; reflexivity.
  Qed.

  Proposition mu_mu X :
    SET.compose (mu X) (mu (omap X)) = SET.compose (mu X) (fmap (mu X)).
  Proof.
    extensionality a; unfold SET.compose, fmap, mu.
    repeat destruct a as [| a]; reflexivity.
  Qed.

End ActionMonad.

Module ActionMonadTheory := MonadTheory SET ActionMonad.


(** ** Kleisli category of the Action monad *)

(** The Kleisli category is provided for free by [MonadTheory].
    We define [ActionBase] as an alias for convenience. *)

Module ActionBase <: Category.
  Include ActionMonadTheory.Kl.

  (** Useful tactic for unfolding Kleisli composition *)
  Ltac unfold_kleisli :=
    repeat match goal with
    | |- context [compose] => unfold compose
    | |- context [id] => unfold id
    | |- context [ActionMonadTheory.ext] => unfold ActionMonadTheory.ext
    | |- context [ActionMonad.mu] => unfold ActionMonad.mu
    | |- context [ActionMonad.fmap] => unfold ActionMonad.fmap
    | |- context [SET.compose] => unfold SET.compose
    | |- context [SET.id] => unfold SET.id
    end;
    simpl in *.
End ActionBase.


(** ** Cartesian structure on the Kleisli category *)

Module ActionCartesian <: CartesianStructure ActionBase.
  Import ActionBase.

  (** Terminal object *)
  Definition unit : t := False.

  (** Terminal arrow *)
  Definition ter (X : t) : m X unit := fun _ => tau.

  (** Uniqueness of terminal arrows *)
  Theorem ter_uni {X} :
    forall (x y : m X unit), x = y.
  Proof.
    intros. extensionality a.
    destruct (x a) as [| x']; destruct (y a) as [| y'];
    try reflexivity; contradiction.
  Qed.

  (** Product of objects *)
  Inductive act_prod (A B : t) : t :=
    sync (x : A) (y : B) | async (x : A + B).
  Arguments sync {_ _} _ _.
  Arguments async {_ _} _.

  Definition omap (A B : t) : t := act_prod A B.

  (** First projection *)
  Definition p1 {A B} : m (omap A B) A :=
    fun a =>
      match a with
      |   sync x y => act x
      |   async (inl x) => act x
      |   async (inr y) => tau
      end.

  (** Second projection *)
  Definition p2 {A B} : m (omap A B) B :=
    fun a =>
      match a with
      |   sync x y => act y
      |   async (inl x) => tau
      |   async (inr y) => act y
      end.

  (** Pairing of morphisms *)
  Definition pair {X A B} (f : m X A) (g : m X B) : m X (omap A B) :=
    fun a =>
      match (f a, g a) with
        |   (act x, act y) => act (sync x y)
        |   (act x, tau) => act (async (inl x))
        |   (tau, act y) => act (async (inr y))
        |   (tau, tau) => tau
      end.

  (** Pairing law: first projection *)
  Theorem p1_pair {X A B} (f : m X A) (g : m X B) :
    p1 @ pair f g = f.
  Proof.
    unfold_kleisli. unfold p1, pair. extensionality x. cbn.
    destruct (f x) as [| y]; destruct (g x) as [| y']; reflexivity.
  Qed.

  (** Pairing law: second projection *)
  Theorem p2_pair {X A B} (f : m X A) (g : m X B) :
    p2 @ pair f g = g.
  Proof.
    unfold_kleisli. unfold p1, pair. extensionality x. cbn.
    destruct (f x) as [| y]; destruct (g x) as [| y']; reflexivity.
  Qed.

  (** Pairing law: uniqueness *)
  Theorem pair_pi_compose {X A B} (x : m X (omap A B)) :
    pair (p1 @ x) (p2 @ x) = x.
  Proof.
    unfold_kleisli. unfold p1, p2, pair. rename x into f.
    extensionality x.
    destruct (f x) as [| y]; try reflexivity.
    destruct y as [l r | [l | r]]; reflexivity.
  Qed.

  Include CartesianStructureTheory ActionBase.
  Include BifunctorTheory ActionBase ActionBase ActionBase.
  Include SymmetricMonoidalStructureTheory ActionBase.
End ActionCartesian.


(** ** Cocartesian structure on the Kleisli category *)

Module ActionCocartesian <: CocartesianStructure ActionBase.
  Import ActionBase.

  (** Initial object (signature calls it "unit") *)
  Definition unit : t := False.

  (** Initial arrow (from initial to any object) *)
  Definition ini (X : t) : m unit X :=
    fun f => match f with end.

  (** Uniqueness of initial arrows *)
  Theorem ini_uni {X} :
    forall (x y : m unit X), x = y.
  Proof.
    intros. extensionality f. destruct f.
  Qed.

  (** Coproduct of objects *)
  Definition omap (A B : t) : t := sum A B.

  (** First injection *)
  Definition i1 {A B} : m A (omap A B) :=
    fun a => act (inl a).

  (** Second injection *)
  Definition i2 {A B} : m B (omap A B) :=
    fun b => act (inr b).

  (** Copairing (signature calls it "copair") *)
  Definition copair {X A B} (f : m A X) (g : m B X) : m (omap A B) X :=
    fun x =>
      match x with
      |   inl a => f a
      |   inr b => g b
      end.

  (** Copair law: first injection *)
  Theorem copair_i1 {X A B} (f : m A X) (g : m B X) :
    copair f g @ i1 = f.
  Proof.
    unfold_kleisli. unfold i1, copair. extensionality x.
    cbn. destruct (f x); reflexivity.
  Qed.

  (** Copair law: second injection *)
  Theorem copair_i2 {X A B} (f : m A X) (g : m B X) :
    copair f g @ i2 = g.
  Proof.
    unfold_kleisli. unfold i2, copair. extensionality x.
    cbn. destruct (g x); reflexivity.
  Qed.

  (** Copair law: uniqueness *)
  Theorem copair_iota_compose {X A B} (x : m (omap A B) X) :
    copair (x @ i1) (x @ i2) = x.
  Proof.
    unfold_kleisli. unfold copair, i1, i2. rename x into h.
    extensionality x. cbn.
    destruct x as [a | b];
    [destruct (h (inl a)) | destruct (h (inr b))]; reflexivity.
  Qed.

  Include CocartesianStructureTheory ActionBase.
  Include BifunctorTheory ActionBase ActionBase ActionBase.
  Include SymmetricMonoidalStructureTheory ActionBase.
End ActionCocartesian.
