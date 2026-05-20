Require Export structures.Posets.


(** * Completely distributive lattices *)

(** ** Definition *)

Class CDLattice (L : Type) :=
  {
    cdl_poset :> Poset L;

    lsup : forall {I}, (I -> L) -> L;
    linf : forall {I}, (I -> L) -> L;

    lsup_sup {I} (u : I -> L) :> IsSup u (lsup u);
    linf_inf {I} (u : I -> L) :> IsInf u (linf u);

    sup_inf {I J} (x : forall i:I, J i -> L) :
      lsup (fun i => linf (fun j => x i j)) =
      linf (fun f : (forall i, J i) => lsup (fun i => x i (f i)));
  }.

(*
Delimit Scope cdlat_scope with cdlat.
Bind Scope cdlat_scope with cdlattice.
*)

(** The notations below work well in the context of completely
  distributive monads. *)

Notation "'sup' i .. j , M" := (lsup (fun i => .. (lsup (fun j => M)) .. ))
  (at level 65, i binder, j binder, right associativity).

Notation "'inf' i .. j , M" := (linf (fun i => .. (linf (fun j => M)) .. ))
  (at level 65, i binder, j binder, right associativity).

(** ** Properties of [sup] and [inf] *)

Section PROPERTIES.
  Context {L} `{HL : !CDLattice L}.

  Lemma inf_sup {I J} (x : forall i:I, J i -> L) :
    inf i, sup j, x i j = sup f, inf i, x i (f i).
  Proof.
    apply antisymmetry.
    - admit.
    - apply sup_lub. intros f.
      apply inf_glb. intros i.
      apply (inf_at i).
      apply (sup_at (f i)).
      reflexivity.
  Admitted.

End PROPERTIES.


(** * Joins and meets with predicates *)

(** It is often convenient to take the [sup] or [inf] by ranging over
  the elements of an index type which satisfy a given predicate. *)

Definition fsup `{CDLattice} {I} (P : I -> Prop) (f : I -> L) :=
  lsup (I := sig P) (fun x => f (proj1_sig x)).

Notation "'sup' { x | P } , M" :=
  (fsup (fun x => P) (fun x => M))
  (at level 65, x name, right associativity).
Notation "'sup' { x : A | P } , M" :=
  (fsup (fun x : A => P) (fun x : A => M))
  (at level 65, A at next level, x name, right associativity).

Definition finf `{CDLattice} {I} (P : I -> Prop) (f : I -> L) :=
  linf (I := sig P) (fun x => f (proj1_sig x)).

Notation "'inf' { x | P } , M" :=
  (finf (fun x => P) (fun x => M))
  (at level 65, x name, right associativity).
Notation "'inf' { x : A | P } , M" :=
  (finf (fun x : A => P) (fun x : A => M))
  (at level 65, x name, right associativity).

Section PREDICATES.
  Context `{Lcdl : CDLattice}.

  Lemma fsup_ub {I} (i : I) (P : I -> Prop) (x : I -> L) :
    P i -> x i <= fsup P x.
  Proof.
    intros Hi. apply (sup_at (exist P i Hi)). reflexivity.
  Qed.

  Lemma fsup_at {I} (i : I) (P : I -> Prop) (x : L) (y : I -> L) :
    P i -> x <= y i -> x <= fsup P y.
  Proof.
    intros Hi Hx. etransitivity; eauto using fsup_ub.
  Qed.

  Lemma fsup_lub {I} (P : I -> Prop) (x : I -> L) (y : L) :
    (forall i, P i -> x i <= y) -> fsup P x <= y.
  Proof.
    intros Hy. apply sup_lub. intros [i Hi]. auto.
  Qed.

  Lemma finf_lb {I} (i : I) (P : I -> Prop) (x : I -> L) :
    P i -> finf P x <= x i.
  Proof.
    intros Hi. apply (inf_at (exist P i Hi)). reflexivity.
  Qed.

  Lemma finf_at {I} (i : I) (P : I -> Prop) (x : I -> L) (y : L) :
    P i -> x i <= y -> finf P x <= y.
  Proof.
    intros Hi Hy. etransitivity; eauto using finf_lb.
  Qed.

  Lemma finf_glb {I} (P : I -> Prop) (x : L) (y : I -> L) :
    (forall i, P i -> x <= y i) -> x <= finf P y.
  Proof.
    intros Hy. apply inf_glb. intros [i Hi]. auto.
  Qed.
End PREDICATES.


(** * Derived operations *)

Section OPS.
  Context `{Lcdl : CDLattice}.

  (** Least element *)

  Definition undef : L :=
    sup i : Empty_set, match i with end.

  Lemma undef_lb x :
    ref undef x.
  Proof.
    apply sup_lub. intros [ ].
  Qed.

  (** ** Binary joins *)

  Definition join (x y : L) :=
    sup b : bool, if b then x else y.

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

  Lemma ref_join x y :
    x <= y <-> join x y = y.
  Proof.
    split; intro.
    - apply antisymmetry, join_ub_r.
      apply join_lub; auto. reflexivity.
    - rewrite <- H. apply join_ub_l.
  Qed.

  (** ** Greatest element *)  

  Definition top : L :=
    inf i : Empty_set, match i with end.

  Lemma top_ub x :
    ref x top.
  Admitted.

  (** ** Binary meets *)

  Definition meet (x y : L) :=
    inf b : bool, if b then x else y.

  Lemma meet_lb_l x y :
    ref (meet x y) x.
  Admitted.

  Lemma meet_lb_r x y :
    ref (meet x y) y.
  Admitted.

  Lemma meet_glb x y z :
    ref x y -> ref x z -> ref x (meet y z).
  Admitted.

  Lemma meet_l x y z :
    ref x z ->
    ref (meet x y) z.
  Proof.
    intro.
    etransitivity; eauto.
    apply meet_lb_l.
  Qed.

  Lemma meet_r x y z :
    ref y z ->
    ref (meet x y) z.
  Proof.
    intro.
    etransitivity; eauto.
    apply meet_lb_r.
  Qed.

  Lemma ref_meet x y :
    x <= y <-> meet x y = x.
  Proof.
    split; intro.
    - apply antisymmetry. apply meet_lb_l.
      apply meet_glb; auto. reflexivity.
    - rewrite <- H. apply meet_lb_r.
  Qed.

  (** ** Properties *)

  Lemma join_undef_l x :
    join undef x = x.
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

  Global Opaque undef top join meet.

End OPS.

Infix "||" := join (at level 50, left associativity).
Infix "&&" := meet (at level 40, left associativity).
