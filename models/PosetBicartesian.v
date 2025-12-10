Require Import interfaces.Category.
Require Import interfaces.ConcreteCategory.
Require Import interfaces.Functor.
Require Import interfaces.MonoidalCategory.
Require Import models.DCPO.
Require Import coqrel.LogicalRelations.

(** * The category of Posets is Bicartesian *)

(** We show that [Poset] from DCPO.v has both products (meets) and
    coproducts (joins), making it a bicartesian category. *)

(** ** Cartesian Structure *)

Module PosetCartesianStructure <: CartesianStructureDefinition Poset.
  Import Poset.

  (** *** Terminal object: unit poset *)

  Definition unit_le (x y : unit) : Prop := True.

  Program Definition unit_PartialOrder : DCPO.PartialOrder unit :=
    {| DCPO.le := unit_le; |}.
  Next Obligation.
    unfold Antisymmetric. intros. destruct x, y; reflexivity.
  Defined.

  Definition unit : t := @Poset.mkt unit unit_PartialOrder.

  Definition ter (X : t) : m X unit.
  Proof.
    refine (@Poset.mkm X unit (fun _ => tt) _).
    intros x y _. exact I.
  Defined.

  Proposition ter_uni : forall {X} (x y : m X unit), x = y.
  Proof.
    intros. apply Poset.meq. intros z.
    destruct (Poset.apply X unit x z), (Poset.apply X unit y z).
    reflexivity.
  Qed.

  (** *** Binary products: pointwise order *)

  Section Product.
    Variables A B : t.

    Definition ProdPO := (Poset.carrier A * Poset.carrier B)%type.

    Program Definition ProdPO_PartialOrder : DCPO.PartialOrder ProdPO :=
      {| DCPO.le := fun p1 p2 =>
                      @le _ (Poset.structure A) (fst p1) (fst p2) /\
                      @le _ (Poset.structure B) (snd p1) (snd p2) |}.
    Next Obligation.
      constructor.
      - intros [a b]. split; reflexivity.
      - intros [a1 b1] [a2 b2] [a3 b3] [H1a H1b] [H2a H2b].
        split; etransitivity; eauto.
    Qed.
    Next Obligation.
      intros [a1 b1] [a2 b2] [H1a H1b] [H2a H2b]. simpl in *.
      f_equal.
      - exact (@le_po (Poset.carrier A) (Poset.structure A) a1 a2 H1a H2a).
      - exact (@le_po (Poset.carrier B) (Poset.structure B) b1 b2 H1b H2b).
    Qed.

    Definition prod : t := @Poset.mkt ProdPO ProdPO_PartialOrder.

    Definition proj1 : m prod A.
    Proof.
      refine (@Poset.mkm prod A fst _).
      intros [a1 b1] [a2 b2] [Ha Hb]. exact Ha.
    Defined.

    Definition proj2 : m prod B.
    Proof.
      refine (@Poset.mkm prod B snd _).
      intros [a1 b1] [a2 b2] [Ha Hb]. exact Hb.
    Defined.

    Definition mk_pair {X : t} (f : m X A) (g : m X B) : m X prod.
    Proof.
      refine (@Poset.mkm X prod (fun x => (Poset.apply X A f x, Poset.apply X B g x)) _).
      intros x y Hxy. split.
      - apply (Poset.morphism X A f). exact Hxy.
      - apply (Poset.morphism X B g). exact Hxy.
    Defined.

  End Product.

  Definition omap (A B : t) : t := prod A B.
  Definition p1 {A B} : m (omap A B) A := proj1 A B.
  Definition p2 {A B} : m (omap A B) B := proj2 A B.
  Definition pair {X A B} (f : m X A) (g : m X B) : m X (omap A B) := mk_pair A B f g.

  Proposition p1_pair : forall {X A B} (f : m X A) (g : m X B), compose p1 (pair f g) = f.
  Proof. intros. apply Poset.meq. intros x. reflexivity. Qed.

  Proposition p2_pair : forall {X A B} (f : m X A) (g : m X B), compose p2 (pair f g) = g.
  Proof. intros. apply Poset.meq. intros x. reflexivity. Qed.

  Proposition pair_pi_compose : forall {X A B} x, @pair X A B (compose p1 x) (compose p2 x) = x.
  Proof.
    intros. apply Poset.meq. intros z. simpl.
    destruct (Poset.apply X (omap A B) x z) as [a b].
    reflexivity.
  Qed.

End PosetCartesianStructure.

Module PosetCartesian <: CartesianStructure Poset.
  Include PosetCartesianStructure.
  Include CartesianStructureTheory Poset PosetCartesianStructure.
  Include BifunctorTheory Poset Poset Poset.
  Include SymmetricMonoidalStructureTheory Poset.
End PosetCartesian.

(** ** Cocartesian Structure *)

Module PosetCocartesianStructure <: CocartesianStructureDefinition Poset.
  Import Poset.

  (** *** Initial object: empty poset *)

  Program Definition Empty_PartialOrder : DCPO.PartialOrder Empty_set :=
    {| DCPO.le := fun x y => match x with end |}.
  Next Obligation.
    constructor; intros [].
  Defined.
  Next Obligation.
    intros [].
  Defined.

  Definition unit : t := @Poset.mkt Empty_set Empty_PartialOrder.

  Definition ini (X : t) : m unit X.
  Proof.
    refine (@Poset.mkm unit X (fun e => match e with end) _).
    intros [].
  Defined.

  Proposition ini_uni : forall {X} (x y : m unit X), x = y.
  Proof.
    intros. apply Poset.meq. intros [].
  Qed.

  (** *** Binary coproducts: disjoint union *)

  Section Coproduct.
    Variables A B : t.

    Definition CoprodPO := (Poset.carrier A + Poset.carrier B)%type.

    Definition CoprodPO_le (p q : CoprodPO) : Prop :=
      match p, q with
      | inl a1, inl a2 => @le _ (Poset.structure A) a1 a2
      | inr b1, inr b2 => @le _ (Poset.structure B) b1 b2
      | _, _ => False
      end.

    Definition CoprodPO_PartialOrder : DCPO.PartialOrder CoprodPO.
    Proof.
      refine {| DCPO.le := CoprodPO_le |}.
      - constructor.
        + intros [a | b]; simpl. reflexivity. reflexivity.
        + intros [a1 | b1] [a2 | b2] [a3 | b3]; try contradiction; simpl;
            intros H1 H2; etransitivity; eauto.
      - intros [a1 | b1] [a2 | b2]; try contradiction; simpl; intros H1 H2;
          f_equal.
        + exact (@le_po (Poset.carrier A) (Poset.structure A) a1 a2 H1 H2).
        + exact (@le_po (Poset.carrier B) (Poset.structure B) b1 b2 H1 H2).
    Defined.

    Definition coprod : t := @Poset.mkt CoprodPO CoprodPO_PartialOrder.

    Definition inj1 : m A coprod.
    Proof.
      refine (@Poset.mkm A coprod inl _).
      intros a1 a2 Ha. exact Ha.
    Defined.

    Definition inj2 : m B coprod.
    Proof.
      refine (@Poset.mkm B coprod inr _).
      intros b1 b2 Hb. exact Hb.
    Defined.

    Definition mk_copair {X : t} (f : m A X) (g : m B X) : m coprod X.
    Proof.
      refine (@Poset.mkm coprod X
                (fun ab => match ab with
                           | inl a => Poset.apply A X f a
                           | inr b => Poset.apply B X g b
                           end) _).
      intros [a1 | b1] [a2 | b2]; try contradiction; simpl; intros H.
      - apply (Poset.morphism A X f). exact H.
      - apply (Poset.morphism B X g). exact H.
    Defined.

  End Coproduct.

  Definition omap (A B : t) : t := coprod A B.
  Definition i1 {A B} : m A (omap A B) := inj1 A B.
  Definition i2 {A B} : m B (omap A B) := inj2 A B.
  Definition copair {X A B} (f : m A X) (g : m B X) : m (omap A B) X := mk_copair A B f g.

  Proposition copair_i1 : forall {X A B} (f : m A X) (g : m B X), compose (copair f g) i1 = f.
  Proof. intros. apply Poset.meq. intros a. reflexivity. Qed.

  Proposition copair_i2 : forall {X A B} (f : m A X) (g : m B X), compose (copair f g) i2 = g.
  Proof. intros. apply Poset.meq. intros b. reflexivity. Qed.

  Proposition copair_iota_compose : forall {X A B} x, @copair X A B (compose x i1) (compose x i2) = x.
  Proof.
    intros. apply Poset.meq. intros [a | b]; reflexivity.
  Qed.

End PosetCocartesianStructure.

Module PosetCocartesian <: CocartesianStructure Poset.
  Include PosetCocartesianStructure.
  Include CocartesianStructureTheory Poset PosetCocartesianStructure.
  Include BifunctorTheory Poset Poset Poset.
  Include SymmetricMonoidalStructureTheory Poset.
End PosetCocartesian.

(** ** Bicartesian Category *)

Module PosetBicartesian <: BicartesianCategory.
  Module C <: CartesianCategory.
    Include Poset.
    Module Prod := PosetCartesian.
    Include CartesianTheory Poset.
  End C.

  Module CC <: Cocartesian C.
    Module Plus := PosetCocartesian.
    Include CocartesianTheory C.
  End CC.

  Include C.
  Include CC.
End PosetBicartesian.