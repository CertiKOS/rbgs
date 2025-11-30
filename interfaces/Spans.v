Require Import interfaces.Category.
Require Import interfaces.Functor.

Require Import interfaces.Pullbacks.

Require Import Coq.Logic.JMeq.
Require Import ProofIrrelevance.

(** * Span Arrows *)

(** This defines the category of Span Arrows, which makes for
  the vertical arrows in the double category of spans, or the 2-cells in
  the bicategory of spans. *)

Module SpanArrowCategory (C : CategoryDefinition) <: Category.
  Import C.

(**
  A span is just a diagram of the form:

  <<[src] <--[src_leg]-- [vtx] --[src_tgt]--> [tgt]>>

  These are the objects of the category of span arrows.
*)
  Record span :=
    mk_span {
      vtx : C.t;
      src: C.t;
      tgt: C.t;
      src_leg : C.m vtx src;
      tgt_leg : C.m vtx tgt;
    }.

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
  Record span_mor {A B : span} :=
    mk_span_mor {
      vtx_mor : C.m (vtx A) (vtx B);
      src_mor : C.m (src A) (src B);
      tgt_mor : C.m (tgt A) (tgt B);

      mor_src_leg_eq :
        C.compose (src_leg B) vtx_mor = C.compose src_mor (src_leg A);
      mor_tgt_leg_eq :
        C.compose (tgt_leg B) vtx_mor = C.compose tgt_mor (tgt_leg A);
    }.
  Arguments span_mor : clear implicits.

  Proposition meq {A B : span} (f g : span_mor A B) :
    vtx_mor f = vtx_mor g -> src_mor f = src_mor g -> tgt_mor f = tgt_mor g ->
      f = g.
  Proof.
    intros. destruct f, g; cbn in *; subst. f_equal; apply proof_irrelevance.
  Qed.

  Definition t : Type := span.
  Definition m : t -> t -> Type := span_mor.

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

Module Type SpanArrowCategoryInstance (C : CategoryDefinition).
  Include (SpanArrowCategory C).
End SpanArrowCategoryInstance.

Module Src (C : Category) (S : SpanArrowCategoryInstance C) <: Functor S C.

  Definition omap : S.t -> C.t := fun A => S.src A.
  Definition fmap : forall {A B}, S.m A B -> C.m (omap A) (omap B) :=
    fun _ _ => fun f => S.src_mor f.

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

Module Tgt (C : Category) (S : SpanArrowCategoryInstance C) <: Functor S C.

  Definition omap : S.t -> C.t := fun A => S.tgt A.
  Definition fmap : forall {A B}, S.m A B -> C.m (omap A) (omap B) :=
    fun _ _ => fun f => S.tgt_mor f.

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

Module IdSpan (C : Category) (S : SpanArrowCategoryInstance C) : Functor C S.
  Program Definition omap : C.t -> S.t :=
    fun A =>
    {|
      S.vtx := A;
      S.src := A;
      S.tgt := A;
      S.src_leg := C.id A;
      S.tgt_leg := C.id A;
    |}.
  Program Definition fmap : forall {A B}, C.m A B -> S.m (omap A) (omap B) :=
    fun A B => fun f =>
    {|
      S.vtx_mor := f;
      S.src_mor := f;
      S.tgt_mor := f;
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
    intros; unfold fmap; cbn; apply S.meq; cbn; reflexivity.
  Qed.

  Proposition fmap_compose :
    forall {A B C} (g : C.m B C) (f : C.m A B),
      fmap (C.compose g f) = S.compose (fmap g) (fmap f).
  Proof.
    intros; unfold fmap; cbn; apply S.meq; cbn; reflexivity.
  Qed.

  Include (FunctorTheory C S).
End IdSpan.

Module Type SrcInstance (C : Category) (S : SpanArrowCategoryInstance C).
  Include (Src C S).
End SrcInstance.

Module Type TgtInstance (C : Category) (S : SpanArrowCategoryInstance C).
  Include (Tgt C S).
End TgtInstance.

Module SpanComp (C : Category) (PB : Pullbacks C) (S : SpanArrowCategoryInstance C)
  (SF : SrcInstance C S) (TF : TgtInstance C S) (SP : FunctorPullbackCatInstance C S S TF SF) <:
  Functor SP S.

  Program Definition omap : SP.t -> S.t :=
    fun pb_span =>
    {|
      S.vtx := PB.pb_prod (S.tgt_leg (SP.fst pb_span)) (S.src_leg (SP.snd pb_span));
      S.src := S.src (SP.fst pb_span);
      S.tgt := S.tgt (SP.snd pb_span);
      S.src_leg :=
        C.compose (S.src_leg (SP.fst pb_span))
        (PB.pb_p1 (S.tgt_leg (SP.fst pb_span)) (S.src_leg (SP.snd pb_span)));
      S.tgt_leg :=
        C.compose (S.tgt_leg (SP.snd pb_span))
        (PB.pb_p2 (S.tgt_leg (SP.fst pb_span)) (S.src_leg (SP.snd pb_span)));
    |}.
  Next Obligation.
    destruct pb_span. simpl. unfold SF.omap, TF.omap in pb_eq_fst.
    rewrite pb_eq_fst. reflexivity.
  Defined.

  Program Definition fmap : forall {A B}, SP.m A B -> S.m (omap A) (omap B) :=
    fun A B => fun pb_span_mor =>
      {|
        S.vtx_mor := PB.pb_pair (f := S.tgt_leg (SP.fst B)) (g := S.src_leg (SP.snd B))
        (ll := C.compose (S.vtx_mor (SP.fst_mor pb_span_mor))
          (PB.pb_p1 (S.tgt_leg (SP.fst A)) (S.src_leg (SP.snd A))))
        (rl := C.compose (S.vtx_mor (SP.snd_mor pb_span_mor))
          (PB.pb_p2 (S.tgt_leg (SP.fst A)) (S.src_leg (SP.snd A))));
        S.src_mor := S.src_mor (SP.fst_mor pb_span_mor);
        S.tgt_mor := S.tgt_mor (SP.snd_mor pb_span_mor);
      |}.