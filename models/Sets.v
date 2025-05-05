Require Import interfaces.Category.
Require Import interfaces.FunctorCategory.
Require Import interfaces.MonoidalCategory.
Require Import FunctionalExtensionality.


(** * Category of sets and functions *)

Module SET <: CategoryWithEndofunctors.

  Definition t := Type.
  Definition m X Y := X -> Y.

  Definition id X := fun x:X => x.
  Definition compose {X Y Z} (g : Y -> Z) (f : X -> Y) := fun x => g (f x).

  Proposition compose_id_left {A B} (f : m A B) :
    compose (id B) f = f.
  Proof.
    reflexivity.
  Qed.

  Proposition compose_id_right {A B} (f : m A B) :
    compose f (id A) = f.
  Proof.
    reflexivity.
  Qed.

  Proposition compose_assoc {A B C D} (f : m A B) (g : m B C) (h : m C D) :
    compose (compose h g) f = compose h (compose g f).
  Proof.
    reflexivity.
  Qed.

  Include CategoryTheory.
  Include AddEndofunctors.

  (** Naturality properties in [SET] are more convenient to use in the
    following form. *)

  Import (coercions) End.

  Lemma natural {F G} (η : End.nt F G) {X Y} (f : X -> Y) (u : F X) :
    η Y (End.fapply F f u) = End.fapply G f (η X u).
  Proof.
    change ((η Y @ End.fapply F f) u = (End.fapply G f @ η X) u).
    rewrite End.natural. reflexivity.
  Qed.

End SET.

(** ** The terms for an effect signature [E] define a monad *)

Module SMnd := Monads SET.

Inductive term (E : Type -> Type) X :=
  | var (x : X) : term E X
  | cons {I : Type} (m : E I) (t : I -> term E X) : term E X.

Arguments var {_ _}.
Arguments cons {_ _} {I}.

Fixpoint tmap E {X Y} (f : X -> Y) (t : term E X) :=
  match t with
    | var x => var (f x)
    | cons m t => cons m (fun i => tmap E f (t i))
  end.

Proposition tmap_id {E X} (t : term E X) :
  tmap E (SET.id X) t = t.
Proof.
  induction t; cbn; auto. f_equal.
  apply functional_extensionality. intro i.
  apply H.
Qed.

Proposition tmap_compose {E X Y Z} (g : Y -> Z) (f : X -> Y) (t : term E X) :
  tmap E (SET.compose g f) t = tmap E g (tmap E f t).
Proof.
  induction t; cbn; auto. f_equal.
  apply functional_extensionality. intro i.
  apply H.
Qed.

Program Definition free_f E : SET.End.t :=
  {|
    SET.End.oapply := term E;
    SET.End.fapply := @tmap E;
  |}.
Next Obligation.
  apply functional_extensionality. intro t.
  apply tmap_id.
Qed.
Next Obligation.
  apply functional_extensionality. intro t.
  apply tmap_compose.
Qed.

Fixpoint subst E {X Y} (σ : X -> term E Y) (t : term E X) : term E Y :=
  match t with
    | var x => σ x
    | cons m t => cons m (fun i => subst E σ (t i))
  end.

Program Definition free_m E : SMnd.t :=
  {|
    SMnd.carrier := free_f E;
    SMnd.eta := {| SET.End.comp X := var |};
    SMnd.mu := {| SET.End.comp X := subst E (SET.id (term E X)) |};
  |}.
Next Obligation.
  apply functional_extensionality. intro t.
  induction t; cbn; auto. f_equal.
  apply functional_extensionality. intro i.
  unfold SET.compose in H. rewrite H.
  reflexivity.
Qed.
Next Obligation.
  apply SET.End.meq. intro X. cbn.
  reflexivity.
Qed.
Next Obligation.
  apply SET.End.meq. intro X. cbn.
  unfold SET.compose, SET.id.
  apply functional_extensionality. intro t.
  induction t; cbn; auto. f_equal.
  apply functional_extensionality. intro i.
  rewrite H. reflexivity.
Qed.
Next Obligation.
  apply SET.End.meq. intro X. cbn.
  rewrite SET.compose_id_left, SET.compose_id_right.
  unfold SET.compose, SET.id.
  apply functional_extensionality. intro t.
  induction t; cbn.
  - rewrite tmap_id. auto.
  - f_equal.
    apply functional_extensionality. intro i.
    rewrite H. reflexivity.
Qed.

Inductive testsig : Type -> Type :=
  | getbit : testsig bool.

Import SMnd.
Import SET.EndNotations.

Definition test : SET.End.oapply (SMnd.carrier (free_m testsig)) nat.
  cbn.
Abort.
