Require Import interfaces.Category.
Require Import interfaces.Functor.

Require Import interfaces.Pullbacks.

Require Import ProofIrrelevance.

Module SpansDefinition (C : CategoryDefinition).
  (**
  A span is just a diagram of the form:

  <<[src] <--[src_leg]-- [vtx] --[src_tgt]--> [tgt]>>

  These are the objects of the category of span arrows.
*)
  Record span (src tgt : C.t) :=
    mk_span {
      vtx : C.t;
      src_leg : C.m vtx src;
      tgt_leg : C.m vtx tgt;
    }.
  Arguments vtx {_ _}.
  Arguments src_leg {_ _}.
  Arguments tgt_leg {_ _}.

  Definition src {src tgt : C.t} (A : span src tgt) := src.
  Definition tgt {src tgt : C.t} (A : span src tgt) := tgt.

(**
  The morphisms consist of the morphisms in C completing the squares between two
  spans:
<<
    A  <------ S ------> B
    |          |         |
 [src_mor] [vtx_mor] [tgt_mor]
    |          |         |
    V          V         V
    A' <------ T ------> B'
>>
  And compose by stacking diagrams vertically.
*)
  Record span_mor {srcA tgtA srcB tgtB : C.t}
    {A : span srcA tgtA} {B : span srcB tgtB} :=
    mk_span_mor {
      vtx_mor : C.m (vtx A) (vtx B);
      src_mor : C.m (src A) (src B);
      tgt_mor : C.m (tgt A) (tgt B);

      mor_src_leg_eq :
        C.compose (src_leg B) vtx_mor = C.compose src_mor (src_leg A);
      mor_tgt_leg_eq :
        C.compose (tgt_leg B) vtx_mor = C.compose tgt_mor (tgt_leg A);
    }.
  Arguments span_mor {_ _ _ _} (A B).

  Proposition  meq {srcA tgtA srcB tgtB : C.t}
    {A : span srcA tgtA} {B : span srcB tgtB} (f g : span_mor A B) :
    vtx_mor f = vtx_mor g -> src_mor f = src_mor g -> tgt_mor f = tgt_mor g ->
      f = g.
  Proof.
    intros. destruct f, g; cbn in *; subst. f_equal; apply proof_irrelevance.
  Qed.
End SpansDefinition.

Module Type Spans (C : CategoryDefinition).
  Include (SpansDefinition C).
End Spans.

(** * Span Arrows *)

(** This defines the category of Span Arrows, which makes for
  the vertical arrows in the double category of spans, or the 2-cells in
  the bicategory of spans (when src_mor and tgt_mor are identities) *)

Module SpanArrowCategory (C : CategoryDefinition) (S : Spans C)  <: Category.
  Import C.
  Import S.

  Record span' :=
  mk_span' {
    src' : C.t;
    tgt' : C.t;
    carrier :> span src' tgt';
  }.
  Arguments mk_span' {_ _} (carrier).
  Coercion mk_span' : span >-> span'.

  Definition t : Type := span'.
  Definition m : t -> t -> Type :=
    fun A B => span_mor A B.

  Program Definition id : forall A, m A A :=
    fun A =>
    {|
      vtx_mor := id (vtx A);
      src_mor := id (src A);
      tgt_mor := id (tgt A);
    |}.
  Next Obligation.
    rewrite C.compose_id_right, C.compose_id_left; reflexivity.
  Qed.
  Next Obligation.
    rewrite C.compose_id_right, C.compose_id_left; reflexivity.
  Defined.

  Program Definition compose : forall {A B C}, m B C -> m A B -> m A C :=
    fun A B C => fun g f =>
    {|
      vtx_mor := C.compose (vtx_mor g) (vtx_mor f);
      src_mor := C.compose (src_mor g) (src_mor f);
      tgt_mor := C.compose (tgt_mor g) (tgt_mor f);
    |}.
  Next Obligation.
    rewrite <- C.compose_assoc. rewrite mor_src_leg_eq.
    rewrite compose_assoc. rewrite mor_src_leg_eq.
    rewrite compose_assoc. reflexivity.
  Qed.
  Next Obligation.
    rewrite <- C.compose_assoc. rewrite mor_tgt_leg_eq.
    rewrite compose_assoc. rewrite mor_tgt_leg_eq.
    rewrite compose_assoc. reflexivity.
  Qed.

  (** Properties *)

  Proposition compose_id_left :
    forall {A B} (f : m A B), compose (id B) f = f.
  Proof.
    intros; unfold compose, id.
    apply meq; cbn; rewrite C.compose_id_left; reflexivity.
  Qed.

  Proposition compose_id_right :
    forall {A B} (f : m A B), compose f (id A) = f.
  Proof.
    intros; unfold compose, id.
    apply meq; cbn; rewrite C.compose_id_right; reflexivity.
  Qed.

  Proposition compose_assoc :
    forall {A B C D} (f : m A B) (g : m B C) (h : m C D),
      compose (compose h g) f = compose h (compose g f).
  Proof.
    intros; unfold compose, id.
    apply meq; cbn; rewrite C.compose_assoc; reflexivity.
  Qed.

  Include CategoryTheory.

End SpanArrowCategory.

Module Type SpanArrowCategoryInstance (C : CategoryDefinition) (S : Spans C).
  Include (SpanArrowCategory C S).
End SpanArrowCategoryInstance.

Module SpanNotations (C : CategoryDefinition) (Sp : Spans C)
  (S : SpanArrowCategoryInstance C Sp).
  Coercion S.mk_span' : Sp.span >-> S.span'.
End SpanNotations.

Module Src (C : Category) (Sp : Spans C)
  (S : SpanArrowCategoryInstance C Sp) <: Functor S C.
  Import Sp.

  Definition omap : S.t -> C.t := fun A => S.src' A.
  Definition fmap : forall {A B}, S.m A B -> C.m (omap A) (omap B) :=
    fun _ _ => fun f => src_mor f.

  Proposition fmap_id :
    forall A, fmap (S.id A) = C.id (omap A).
  Proof.
    intros; unfold fmap; cbn; reflexivity.
  Qed.

  Proposition fmap_compose :
    forall {A B C} (g : S.m B C) (f : S.m A B),
      fmap (S.compose g f) = C.compose (fmap g) (fmap f).
  Proof.
    intros; unfold fmap; cbn; reflexivity.
  Qed.

  Include (FunctorTheory S C).
End Src.

Module Tgt (C : Category) (Sp : Spans C)
  (S : SpanArrowCategoryInstance C Sp) <: Functor S C.
  Import Sp.

  Definition omap : S.t -> C.t := fun A => S.tgt' A.
  Definition fmap : forall {A B}, S.m A B -> C.m (omap A) (omap B) :=
    fun _ _ => fun f => Sp.tgt_mor f.

  Proposition fmap_id :
    forall A, fmap (S.id A) = C.id (omap A).
  Proof.
    intros; unfold fmap; cbn; reflexivity.
  Qed.

  Proposition fmap_compose :
    forall {A B C} (g : S.m B C) (f : S.m A B),
      fmap (S.compose g f) = C.compose (fmap g) (fmap f).
  Proof.
    intros; unfold fmap; cbn; reflexivity.
  Qed.

  Include (FunctorTheory S C).
End Tgt.

Module IdSpan (C : Category) (Sp : Spans C)
  (S : SpanArrowCategoryInstance C Sp) <: Functor C S.
  Include (SpanNotations C Sp S).
  Import Sp.

  Program Definition omap : C.t -> S.t :=
  fun A =>
    {| vtx := A; src_leg := C.id A; tgt_leg := C.id A |}.

  Program Definition fmap : forall {A B}, C.m A B -> S.m (omap A) (omap B) :=
    fun A B => fun f =>
    {|
      vtx_mor := f;
      src_mor := f;
      tgt_mor := f;
    |}.
  Next Obligation.
    rewrite C.compose_id_left, C.compose_id_right; reflexivity.
  Qed.
  Next Obligation.
    rewrite C.compose_id_left, C.compose_id_right; reflexivity.
  Defined.

  Proposition fmap_id :
    forall A, fmap (C.id A) = S.id (omap A).
  Proof.
    intros; unfold fmap; cbn; apply meq; cbn; reflexivity.
  Qed.

  Proposition fmap_compose :
    forall {A B C} (g : C.m B C) (f : C.m A B),
      fmap (C.compose g f) = S.compose (fmap g) (fmap f).
  Proof.
    intros; unfold fmap; cbn; apply meq; cbn; reflexivity.
  Qed.

  Include (FunctorTheory C S).
End IdSpan.

Module Type SrcInstance (C : Category) (Sp : Spans C) (S : SpanArrowCategoryInstance C Sp).
  Include (Src C Sp S).
End SrcInstance.

Module Type TgtInstance (C : Category) (Sp : Spans C) (S : SpanArrowCategoryInstance C Sp).
  Include (Tgt C Sp S).
End TgtInstance.