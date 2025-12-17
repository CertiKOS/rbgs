Require Import interfaces.Monads.
Require Import interfaces.MonoidalCategory.
Require Import interfaces.Limits.

(* This defines the Lift Monad X |-> 1 + X on any cocartesian category
   with terminals *)

Module LiftMonad (C : CocartesianCategory) (T : Terminals C) <: Monad C.
  Import C.
  Open Scope obj_scope.

  Definition omap := fun X => T.unit + X.

  Definition fmap {A B} (f : m A B) : m (omap A) (omap B) := (id T.unit) + f.

  Proposition fmap_id :
    forall A, fmap (C.id A) = C.id (omap A).
  Proof.
    unfold fmap. intros A. rewrite Plus.fmap_id. reflexivity.
  Qed.

  Proposition fmap_compose :
    forall {A B C} (g : C.m B C) (f : C.m A B),
      fmap (C.compose g f) = C.compose (fmap g) (fmap f).
  Proof.
    intros A B C. intros g f. unfold fmap.
    pose (Plus.fmap_compose (id T.unit) g (id T.unit) f).
    rewrite compose_id_left in e. exact e.
  Qed.

  Definition eta : forall X, C.m X (omap X) :=
    fun x => Plus.i2.
  Definition mu : forall X, C.m (omap (omap X)) (omap X) :=
    fun X => Plus.fmap (T.ter _) (id _) @ (Plus.assoc _ _ _).

  Proposition eta_natural :
    forall {X Y} (f : C.m X Y),
      C.compose (eta Y) f = C.compose (fmap f) (eta X).
  Proof.
    intros. unfold eta, fmap. unfold Plus.fmap.
    symmetry. exact (Plus.copair_i2 (Plus.i1 @ id T.unit) (Plus.i2 @ f)).
  Qed.

  Proposition mu_natural :
    forall {X Y} (f : C.m X Y),
      C.compose (mu Y) (fmap (fmap f)) = C.compose (fmap f) (mu X).
  Proof.
    intros. unfold mu, fmap. rewrite compose_assoc.
    pose (Plus.assoc_nat (id T.unit) (id T.unit) f).
    symmetry in e. rewrite e at 1.
    rewrite <- compose_assoc. rewrite <- compose_assoc. f_equal. clear e.
    pose (Plus.fmap_compose (T.ter (T.unit + T.unit)) (id Y) (id T.unit + id T.unit) f).
    symmetry in e. rewrite e at 1. clear e.
    rewrite compose_id_left. rewrite Plus.fmap_id. rewrite compose_id_right.
    replace f with (f @ id X) at 1 by (apply compose_id_right).
    replace (T.ter (T.unit + T.unit)) with
      (id T.unit @ T.ter (T.unit + T.unit)) at 1 by (apply compose_id_left).
    rewrite Plus.fmap_compose. reflexivity.
  Qed.

  Proposition mu_eta_l :
    forall X,
      C.compose (mu X) (eta (omap X)) = C.id (omap X).
  Proof.
    intros. unfold mu, eta, omap; simpl.
    unfold Plus.fmap, Plus.assoc; simpl.
    autorewrite with copair.
    symmetry. apply Plus.copair_uni.
    - rewrite compose_id_left. symmetry.
      rewrite (T.ter_uni (T.ter _ @ Plus.i2) (id T.unit)).
      rewrite compose_id_right. reflexivity.
    - rewrite compose_id_left. rewrite compose_id_right. reflexivity.
  Qed.

  Proposition mu_eta_r :
    forall X,
      C.compose (mu X) (fmap (eta X)) = C.id (omap X).
  Proof.
    intros. unfold mu, eta, fmap, omap; simpl.
    unfold Plus.fmap, Plus.assoc; simpl.
    autorewrite with copair.
    symmetry. apply Plus.copair_uni.
    - rewrite compose_id_left. rewrite compose_id_right. symmetry.
      rewrite (T.ter_uni (T.ter _ @ Plus.i1) (id T.unit)).
      rewrite compose_id_right. reflexivity.
    - rewrite compose_id_left.
      rewrite compose_id_right.
      reflexivity.
  Qed.

  Proposition mu_mu :
    forall X,
      C.compose (mu X) (mu (omap X)) = C.compose (mu X) (fmap (mu X)).
  Proof.
    intros. unfold mu, fmap, omap; simpl.
    unfold Plus.fmap, Plus.assoc; simpl.
    autorewrite with copair.
    apply Plus.copair_uni; autorewrite with copair.
    - repeat f_equal.
      apply T.ter_uni.
    - apply Plus.copair_uni; autorewrite with copair.
      + f_equal. apply T.ter_uni.
      + repeat rewrite compose_id_right.
        apply Plus.copair_uni; autorewrite with copair.
        f_equal. apply T.ter_uni. reflexivity.
  Qed.

  Include (MonadTheory C).
End LiftMonad.
