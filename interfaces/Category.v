Require Import Coq.Program.Tactics.


(** * Introduction *)

(** The models we formalize all provide the structure of a category:

  - A set of objects, representing interfaces,
  - Morphisms between objects, representing components,
  - Identities for trivial components,
  - Composition of morphisms along a common interface.

  By using Coq's module system, we can ensure a uniform interface
  across different model and maximize code reuse, without paying for
  the additional complexity what would come with a first-class
  treatment of the underlying categorical concepts. *)


(** * Categories *)

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

  (** ** Notations *)

  Delimit Scope obj_scope with obj.
  Bind Scope obj_scope with C.t.
  Open Scope obj_scope.

  Delimit Scope hom_scope with hom.
  Bind Scope hom_scope with C.m.
  Open Scope hom_scope.

  Infix "@" := C.compose (at level 45, right associativity) : hom_scope.

  (** ** Isomorphisms *)

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







(** ** Basic instances *)

(** *** Product category *)

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





