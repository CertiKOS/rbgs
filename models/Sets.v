Require Import interfaces.Category.
Require Import interfaces.Functor.
Require Import interfaces.FunctorCategory.
Require Import interfaces.MonoidalCategory.
Require Import FunctionalExtensionality.


(** * Category of sets and functions *)

Module SetBase <: CategoryWithEndofunctors.

  (** ** Core definitions *)

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

  (** ** Endofunctors *)

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

End SetBase.

Module Type SetBaseSpec.
  Include SetBase.
End SetBaseSpec.

(** ** Monoidal Structures *)

Module SetMonoidalStructures (B : SetBaseSpec).
  Import B.

  Module Prod <: CartesianStructure B.

    Definition unit := Datatypes.unit.
    Definition ter X : X ~~> unit := fun _ => tt.

    Theorem ter_uni {X} :
      forall (x y : X ~~> unit), x = y.
    Proof.
      intros.
      apply functional_extensionality.
      intros i. destruct (x i), (y i); auto.
    Qed.

    Definition omap : t -> t -> t := prod.
    Definition p1 {A B} : omap A B ~~> A := @fst A B.
    Definition p2 {A B} : omap A B ~~> B := @snd A B.
    Definition pair {X A B} (f : X ~~> A) (g : X ~~> B) : X ~~> omap A B :=
      fun x => (f x, g x).

    Theorem p1_pair {X A B} (f : m X A) (g : m X B) :
      p1 @ pair f g = f.
    Proof.
      reflexivity.
    Qed.

    Theorem p2_pair {X A B} (f : m X A) (g : m X B) :
      p2 @ pair f g = g.
    Proof.
      firstorder.
    Qed.

    Theorem pair_pi {X A B} x :
      @pair X A B (p1 @ x) (p2 @ x) = x.
    Proof.
      apply functional_extensionality.
      intros i. unfold pair, compose.
      destruct x; auto.
    Qed.

    Include CartesianStructureTheory B.
    Include BifunctorTheory B B B.
    Include MonoidalStructureTheory B.
  End Prod.

  Module Exp : MonoidalClosureDefinition B Prod.

    Definition omap (A B : t) : t :=
      A -> B.

    Definition fmap {A1 A2 B1 B2} (f : B1 ~~> A1) (g : A2 ~~> B2) : omap A1 A2 ~~> omap B1 B2 :=
      fun h => g @ h @ f.

    Theorem fmap_id A1 A2 :
      fmap (id A1) (id A2) = id (omap A1 A2).
    Proof.
      reflexivity.
    Qed.

    Theorem fmap_compose {A1 A2 B1 B2 C1 C2} :
      forall (g1 : C1 ~~> B1) (g2 : B2 ~~> C2) (f1 : B1 ~~> A1) (f2 : A2 ~~> B2),
        fmap (f1 @ g1) (g2 @ f2) = fmap g1 g2 @ fmap f1 f2.
    Proof.
      reflexivity.
    Qed.

    Include BifunctorTheory B.Op B B.

    Definition curry : forall {A B C}, (Prod.omap A B ~~> C) -> (A ~~> omap B C) :=
      @Datatypes.curry.

    Definition uncurry : forall {A B C}, (A ~~> omap B C) -> (Prod.omap A B ~~> C) :=
      @Datatypes.uncurry.

    Theorem uncurry_curry {A B C} (f : Prod.omap A B ~~> C) :
      uncurry (curry f) = f.
    Proof.
      apply functional_extensionality.
      intros [a b].
      reflexivity.
    Qed.

    Theorem curry_uncurry {A B C} (g : A ~~> omap B C) :
      curry (uncurry g) = g.
    Proof.
      reflexivity.
    Qed.

    Theorem curry_natural_l {A1 A2 B C} (x : A1 ~~> A2) (f : Prod.omap A2 B ~~> C) :
      curry (f @ (Prod.fmap x (id B))) = curry f @ x.
    Proof.
      reflexivity.
    Qed.

    Theorem curry_natural_r {A B C1 C2} (f : Prod.omap A B ~~> C1) (y : C1 ~~> C2) :
      curry (y @ f) = fmap (id B) y @ curry f.
    Proof.
      reflexivity.
    Qed.

    Include MonoidalClosureTheory B Prod.
  End Exp.
End SetMonoidalStructures.

(** ** Overall definition *)

Module Type SetSpec :=
  CartesianCategory <+
  AddEndofunctors.

Module SET <: SetSpec :=
  SetBase <+
  SetMonoidalStructures.


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
