Require Import coqrel.LogicalRelations.
Require Export Poset.


(** * Completely distributive lattices *)

(** ** Definition *)

Class CDLattice (L : Type) :=
  {
    cdl_poset :> Poset L;

    sup : forall {I}, (I -> L) -> L;
    inf : forall {I}, (I -> L) -> L;

    sup_ub {I} (i : I) (x : I -> L) : ref (x i) (sup x);
    sup_lub {I} (x : I -> L) (y : L) : (forall i, ref (x i) y) -> ref (sup x) y;

    inf_lb {I} (i : I) (x : I -> L) : ref (inf x) (x i);
    inf_glb {I} (x : L) (y : I -> L) : (forall i, ref x (y i)) -> ref x (inf y);

    sup_inf {I J} (x : forall i:I, J i -> L) :
      sup (fun i => inf (fun j => x i j)) =
      inf (fun f : (forall i, J i) => sup (fun i => x i (f i)));
  }.

(** The notations below work well in the context of completely
  distributive monads. *)

Notation "⋁ i .. j ; M" := (sup (fun i => .. (sup (fun j => M)) .. ))
    (at level 65, i binder, j binder, right associativity).
Notation "⋀ i .. j ; M" := (inf (fun i => .. (inf (fun j => M)) .. ))
    (at level 65, i binder, j binder, right associativity).

(** ** Properties of [sup] and [inf] *)

Section PROPERTIES.
  Context `{Lcd : CDLattice}.

  Lemma sup_at {I} (i : I) (x : L) (y : I -> L) :
    x ⊑ y i -> x ⊑ ⋁ i; y i.
  Proof.
    intros; etransitivity; eauto using sup_ub.
  Qed.

  Lemma inf_at {I} (i : I) (x : I -> L) (y : L) :
    x i ⊑ y -> ⋀ i; x i ⊑ y.
  Proof.
    intros; etransitivity; eauto using inf_lb.
  Qed.

  Lemma inf_sup {I J} (x : forall i:I, J i -> L) :
    ⋀ i; ⋁ j; x i j = ⋁ f; ⋀ i; x i (f i).
  Proof.
  Admitted.

End PROPERTIES.


(** * Joins and meets with predicates *)

(** It is often convenient to take the [sup] or [inf] by ranging over
  the elements of an index type which satisfy a given predicate. *)

Notation "⋁ { x | P } ; M" :=
  (sup (I := sig (fun x => P)) (fun '(exist _ x _) => M))
  (at level 65, x ident, right associativity).
Notation "⋁ { x : A | P } ; M" :=
  (sup (I := sig (fun x : A => P)) (fun '(exist _ x _) => M))
  (at level 65, A at next level, x ident, right associativity).
Notation "⋀ { x | P } ; M" :=
  (inf (I := sig (fun x => P)) (fun '(exist _ x _) => M))
  (at level 65, x ident, right associativity).
Notation "⋀ { x : A | P } ; M" :=
  (inf (I := sig (fun x : A => P)) (fun '(exist _ x _) => M))
  (at level 65, x ident, right associativity).

Section PREDICATES.
  Context `{Lcd : CDLattice}.

  Lemma psup_ub {I} (i : I) (P : I -> Prop) (x : I -> L) :
    P i -> x i ⊑ ⋁{ i | P i }; x i.
  Proof.
    intros Hi.
    apply (sup_ub (exist P i Hi) (fun '(exist _ i _) => x i)).
  Qed.

  Lemma psup_at {I} (i : I) (P : I -> Prop) (x : L) (y : I -> L) :
    P i -> x ⊑ y i -> x ⊑ ⋁{ i | P i }; y i.
  Proof.
    intros Hi Hx. etransitivity; eauto using psup_ub.
  Qed.

  Lemma psup_lub {I} (P : I -> Prop) (x : I -> L) (y : L) :
    (forall i, P i -> x i ⊑ y) ->
    ⋁{ i | P i }; x i ⊑ y.
  Proof.
    intros Hy. apply sup_lub. intros [i Hi]. auto.
  Qed.

  Lemma pinf_lb {I} (i : I) (P : I -> Prop) (x : I -> L) :
    P i -> ⋀{ i | P i }; x i ⊑ x i.
  Proof.
    intros Hi.
    apply (inf_lb (exist P i Hi) (fun '(exist _ i _) => x i)).
  Qed.

  Lemma pinf_at {I} (i : I) (P : I -> Prop) (x : I -> L) (y : L) :
    P i -> x i ⊑ y -> ⋀{ i | P i }; x i ⊑ y.
  Proof.
    intros Hi Hy. etransitivity; eauto using pinf_lb.
  Qed.

  Lemma pinf_glb {I} (P : I -> Prop) (x : L) (y : I -> L) :
    (forall i, P i -> x ⊑ y i) ->
    x ⊑ ⋀{ i | P i }; y i.
  Proof.
    intros Hy. apply inf_glb. intros [i Hi]. auto.
  Qed.
End PREDICATES.


(** * Derived operations *)

Section OPS.
  Context `{Acdl : CDLattice}.

  (** Least element *)

  Definition bot :=
    ⋁ i : Empty_set; match i with end.

  Lemma bot_lb x :
    ref bot x.
  Admitted.

  (** ** Binary joins *)

  Definition join (x y : L) :=
    ⋁ b : bool; if b then x else y.

  Lemma join_ub_l x y :
    ref x (join x y).
  Admitted.

  Lemma join_ub_r x y :
    ref y (join x y).
  Admitted.

  Lemma join_lub x y z :
    ref x z -> ref y z -> ref (join x y) z.
  Admitted.

  Lemma join_l x y z :
    ref x y ->
    ref x (join y z).
  Proof.
    intro.
    etransitivity; eauto.
    apply join_ub_l.
  Qed.

  Lemma join_r x y z :
    ref x z ->
    ref x (join y z).
  Proof.
    intro.
    etransitivity; eauto.
    apply join_ub_r.
  Qed.

  (** ** Greatest element *)  

  Definition top :=
    ⋀ i : Empty_set; match i with end.

  Lemma top_ub x :
    ref x top.
  Admitted.

  (** ** Binary meets *)

  Definition meet (x y : L) :=
    ⋀ b : bool; if b then x else y.

  Lemma meet_ub_l x y :
    ref (meet x y) x.
  Admitted.

  Lemma meet_ub_r x y :
    ref (meet x y) y.
  Admitted.

  Lemma meet_glb x y z :
    ref x y -> ref x z -> ref x (meet y z).
  Admitted.

  (** ** Properties *)

  Lemma join_bot_l x :
    join bot x = x.
  Admitted.

  Lemma join_top_l x :
    join top x = top.
  Admitted.

  Lemma join_meet_l x y z :
    join (meet x y) z = meet (join x z) (join y z).
  Admitted.

  (* ... foo_bar_l, foo_bar_r ... *)

  Lemma join_comm x y :
    join x y = join y x.
  Admitted.

  Lemma meet_comm x y :
    meet x y = meet y x.
  Admitted.

  Lemma join_idemp x :
    join x x = x.
  Admitted.

  Lemma meet_idemp x :
    meet x x = x.
  Admitted.

  (** These properties are more than enough to completely define the
    derived operations, so that relying on their concrete definition
    should not be necessary. *)

  Global Opaque bot top join meet.

End OPS.

Notation "⊥" := bot.
Notation "⊤" := top.
Notation "(⊔)" := join.
Notation "(⊓)" := meet.
Infix "⊔" := join (at level 50).
Infix "⊓" := meet (at level 50).
