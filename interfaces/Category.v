Require Import Coq.Program.Tactics.


(** * Introduction *)

(** The models we formalize all provide the structure of a category:

  - A set of objects, representing interfaces,
  - Morphisms between objects, representing components,
  - Identities for trivial components,
  - Composition of morphisms along a common interface.

  By using Coq's module system, we can ensure a uniform interface
  across different models and maximize code reuse, without paying for
  the additional complexity what would come with a first-class
  treatment of the underlying categorical concepts. *)


(** * Category interface *)

(** The module type [Category] defined below provides a common
  interface that we expect to rely on no matter which model is used.
  This interface is divided into two parts:

  - the module type [CategoryDefinition] enumerates the data which
    must be defined when we declare a new instance;
  - the module functor [CategoryTheory] then provides common
    definitions and proofs and can be included to finish implementing
    the complete user-facing [Category] interface.

  We will use this pattern very often as we define other interfaces. *)

(** ** Definition *)

(** The following interface gives the basic definition of a category. *)

Module Type CategoryDefinition.

  (** Objects and morphisms *)

  Parameter t : Type.
  Parameter m : t -> t -> Type.

  (** Identity and composition *)

  Parameter id : forall A, m A A.
  Parameter compose : forall {A B C}, m B C -> m A B -> m A C.

  (** Properties *)

  Axiom compose_id_left :
    forall {A B} (f : m A B), compose (id B) f = f.

  Axiom compose_id_right :
    forall {A B} (f : m A B), compose f (id A) = f.

  Axiom compose_assoc :
    forall {A B C D} (f : m A B) (g : m B C) (h : m C D),
      compose (compose h g) f = compose h (compose g f).

End CategoryDefinition.

(** ** Theory *)

(** Once the fields enumerated in [CategoryDefinition] have been
  defined, the user should include the following module, which works
  out some basic category theory. *)

Module CategoryTheory (C : CategoryDefinition).

  (** *** Notations *)

  Declare Scope obj_scope.
  Delimit Scope obj_scope with obj.
  Bind Scope obj_scope with C.t.
  Open Scope obj_scope.

  Declare Scope hom_scope.
  Delimit Scope hom_scope with hom.
  Bind Scope hom_scope with C.m.
  Open Scope hom_scope.

  Infix "@" := C.compose (at level 45, right associativity) : hom_scope.
  Infix "~~>" := C.m (at level 90, right associativity) : type_scope.

  (** *** Isomorphisms *)

  Structure iso {A B : C.t} :=
    {
      fw :> C.m A B;
      bw : C.m B A;
      bw_fw : bw @ fw = C.id A;
      fw_bw : fw @ bw = C.id B;
    }.

  Arguments iso : clear implicits.

  (** The following versions help rewriting modulo associativity. *)

  Lemma bw_fw_rewrite {A B X} (f : iso A B) (x : C.m X A) :
    bw f @ fw f @ x = x.
  Proof.
    rewrite <- C.compose_assoc, bw_fw.
    apply C.compose_id_left.
  Qed.

  Lemma fw_bw_rewrite {A B X} (f : iso A B) (x : C.m X B) :
    fw f @ bw f @ x = x.
  Proof.
    rewrite <- C.compose_assoc, fw_bw.
    apply C.compose_id_left.
  Qed.

  (** We can define some basic instances. *)

  Program Canonical Structure id_iso {A} :=
    {|
      fw := C.id A;
      bw := C.id A;
    |}.
  Solve All Obligations with
    auto using C.compose_id_left.

  Canonical Structure bw_iso {A B} (f : iso A B) :=
    {|
      fw := bw f;
      bw := fw f;
      bw_fw := fw_bw f;
      fw_bw := bw_fw f;
    |}.

  Program Canonical Structure compose_iso {A B C} (g : iso B C) (f : iso A B) :=
    {|
      fw := fw g @ fw f;
      bw := bw f @ bw g;
    |}.
  Solve All Obligations with
    intros;
    rewrite ?C.compose_assoc, ?bw_fw_rewrite, ?fw_bw_rewrite, ?fw_bw, ?bw_fw;
    auto.

End CategoryTheory.

(** ** Overall interface *)

(** A module defining a specific category is expected to provide the
  basic definitions and include the theory. *)

Module Type Category.
  Include CategoryDefinition.
  Include CategoryTheory.
End Category.


(** * Basic instances *)

(** ** Trivial categories *)

(** The category [0] has no objects. *)

Module Zero <: Category.

  Definition t : Type := Empty_set.
  Definition m (A B : t) : Type := match A with end.

  Definition id (A : t) : m A A := match A with end.
  Definition compose {A B C} (x : m B C) (y : m A B) : m A C := match A with end.

  Lemma compose_id_left {A B} (f : m A B) :
    compose (id B) f = f.
  Proof.
    destruct A.
  Qed.

  Lemma compose_id_right {A B} (f : m A B) :
    compose f (id A) = f.
  Proof.
    destruct A.
  Qed.

  Lemma compose_assoc {A B C D} (f : m A B) (g : m B C) (h : m C D) :
    compose (compose h g) f = compose h (compose g f).
  Proof.
    destruct A.
  Qed.

  Include CategoryTheory.

End Zero.

(** The category [1] has a single object and morphism. *)

Module One <: Category.

  Definition t : Type := unit.
  Definition m (A B : t) : Type := unit.

  Definition id (A : t) : m A A := tt.
  Definition compose {A B C} (x : m B C) (y : m A B) : m A C := tt.

  Lemma compose_id_left {A B} (f : m A B) :
    compose (id B) f = f.
  Proof.
    destruct f.
    reflexivity.
  Qed.

  Lemma compose_id_right {A B} (f : m A B) :
    compose f (id A) = f.
  Proof.
    destruct f.
    reflexivity.
  Qed.

  Lemma compose_assoc {A B C D} (f : m A B) (g : m B C) (h : m C D) :
    compose (compose h g) f = compose h (compose g f).
  Proof.
    reflexivity.
  Qed.

  Include CategoryTheory.

End One.

(** The interval category [2] contains two objects and a single
  nontrivial morphism between them. *)

Module Two <: Category.
  Unset Program Cases.

  Variant m_def : bool -> bool -> Type :=
    | id_def A : m_def A A
    | int : m_def false true.

  Definition t : Type := bool.
  Definition m : t -> t -> Type := m_def.

  Definition id : forall A, m A A := id_def.

  Program Definition compose {A B C} (g : m B C) : m A B -> m A C :=
    match g with
      | id_def A => fun f => f
      | int =>
        match A with
          | true => _ (* this cannot happen since [m true false] is empty *)
          | false => fun f => int
        end
    end.
  Next Obligation.
    inversion X.
  Qed.

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

End Two.

(** ** Category of types and functions *)

Module SET.

  (** Objects and morphisms *)

  Definition t := Type.
  Definition m (A B : t) := A -> B.

  (** Composition *)

  Definition id A : m A A :=
    fun x => x.

  Definition compose {A B C} (g : m B C) (f : m A B) : m A C :=
    fun x => g (f x).

  (** Proofs *)

  Lemma compose_id_left {A B} (f : m A B) :
    compose (id B) f = f.
  Proof.
    reflexivity.
  Qed.

  Lemma compose_id_right {A B} (f : m A B) :
    compose f (id A) = f.
  Proof.
    reflexivity.
  Qed.

  Lemma compose_assoc {A B C D} (f : m A B) (g : m B C) (h : m C D) :
    compose (compose h g) f = compose h (compose g f).
  Proof.
    reflexivity.
  Qed.

End SET.

(** ** Product category *)

(** This is used in particular to give bifunctors a functor interface. *)

Module Prod (C D : CategoryDefinition) <: Category.

  (** Objects and morphisms *)

  Definition t : Type := C.t * D.t.
  Definition m (A B : t) : Type := C.m (fst A) (fst B) * D.m (snd A) (snd B).

  (** Composition *)

  Definition id A : m A A :=
    (C.id (fst A), D.id (snd A)).

  Definition compose {A B C} (g : m B C) (f : m A B) : m A C :=
    (C.compose (fst g) (fst f), D.compose (snd g) (snd f)).

  (** Proofs *)

  Lemma compose_id_left {A B} (f : m A B) :
    compose (id B) f = f.
  Proof.
    destruct f; unfold id, compose; cbn; f_equal.
    - apply C.compose_id_left.
    - apply D.compose_id_left.
  Qed. 

  Lemma compose_id_right {A B} (f : m A B) :
    compose f (id A) = f.
  Proof.
    destruct f; unfold id, compose; cbn; f_equal.
    - apply C.compose_id_right.
    - apply D.compose_id_right.
  Qed.

  Lemma compose_assoc {A B C D} (f : m A B) (g : m B C) (h : m C D) :
    compose (compose h g) f = compose h (compose g f).
  Proof.
    destruct f, g, h; unfold id, compose; cbn; f_equal.
    - apply C.compose_assoc.
    - apply D.compose_assoc.
  Qed.

  Include CategoryTheory.

End Prod.

(** ** Opposite category *)

Module Op (C : Category) <: Category.

  (** Objects and morphisms *)

  Definition t := C.t.
  Definition m (A B : t) : Type := C.m B A.

  (** Composition *)

  Definition id A : m A A := C.id A.
  Definition compose {A B C} (g : m B C) (f : m A B) : m A C := C.compose f g.

  (** Proofs *)

  Lemma compose_id_left {A B} (f : m A B) :
    compose (id B) f = f.
  Proof.
    apply C.compose_id_right.
  Qed.

  Lemma compose_id_right {A B} (f : m A B) :
    compose f (id A) = f.
  Proof.
    apply C.compose_id_left.
  Qed.

  Lemma compose_assoc {A B C D} (f : m A B) (g : m B C) (h : m C D) :
    compose (compose h g) f = compose h (compose g f).
  Proof.
    symmetry.
    apply C.compose_assoc.
  Qed.

  Include CategoryTheory.

End Op.
