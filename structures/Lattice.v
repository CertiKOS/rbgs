Require Export structures.Poset.
Require Import Coq.Logic.Classical.
Require Import Coq.Logic.ChoiceFacts.

Axiom dep_choice : DependentFunctionalChoice.

(** * Completely distributive lattices *)

(** ** Definition *)

Record cdlattice :=
  {
    cdl_poset :> poset;

    lsup : forall {I}, (I -> cdl_poset) -> cdl_poset;
    linf : forall {I}, (I -> cdl_poset) -> cdl_poset;

    sup_ub {I} (i : I) (x : I -> cdl_poset) :
      ref (x i) (lsup x);
    sup_lub {I} (x : I -> cdl_poset) (y : cdl_poset) :
      (forall i, ref (x i) y) ->
      ref (lsup x) y;

    inf_lb {I} (i : I) (x : I -> cdl_poset) :
      ref (linf x) (x i);
    inf_glb {I} (x : cdl_poset) (y : I -> cdl_poset) :
      (forall i, ref x (y i)) ->
      ref x (linf y);

    sup_inf {I J} (x : forall i:I, J i -> cdl_poset) :
      lsup (fun i => linf (fun j => x i j)) =
      linf (fun f : (forall i, J i) => lsup (fun i => x i (f i)));
  }.

Arguments lsup {_ _}.
Arguments linf {_ _}.
Arguments sup_ub {_ _}.
Arguments sup_lub {_ _}.
Arguments inf_lb {_ _}.
Arguments inf_glb {_ _}.

Delimit Scope cdlat_scope with cdlat.
Bind Scope cdlat_scope with cdlattice.

(** The notations below work well in the context of completely
  distributive monads. *)

Notation "'sup' i .. j , M" := (lsup (fun i => .. (lsup (fun j => M)) .. ))
  (at level 65, i binder, j binder, right associativity).

Notation "'inf' i .. j , M" := (linf (fun i => .. (linf (fun j => M)) .. ))
  (at level 65, i binder, j binder, right associativity).

(** ** Properties of [sup] and [inf] *)

Section PROPERTIES.
  Context {L : cdlattice}.

  Lemma sup_at {I} (i : I) (x : L) (y : I -> L) :
    x [= y i -> x [= sup i, y i.
  Proof.
    intros; etransitivity; eauto using sup_ub.
  Qed.

  Lemma inf_at {I} (i : I) (x : I -> L) (y : L) :
    x i [= y -> inf i, x i [= y.
  Proof.
    intros; etransitivity; eauto using inf_lb.
  Qed.

  Lemma sup_iff {I} (x : I -> L) (y : L) :
    lsup x [= y <-> forall i, x i [= y.
  Proof.
    split.
    - intros H i. etransitivity; eauto using sup_ub.
    - apply sup_lub.
  Qed.

  Lemma inf_iff {I} (x : L) (y : I -> L) :
    x [= linf y <-> forall i, x [= y i.
  Proof.
    split.
    - intros H i. etransitivity; eauto using inf_lb.
    - apply inf_glb.
  Qed.

  Local Lemma not_exists_forall {I J} {P: forall i : I, J i -> Prop}:
    (~ (exists i : I, forall j : J i, P i j)) <-> forall i : I, exists j : J i, ~ P i j.
  Proof.
    split; firstorder.
    eapply not_all_ex_not in H. apply H.
  Qed.

  Local Lemma not_exists {A} {P : A -> Prop}:
    (~ exists x, P x) <-> (forall x, ~ P x).
  Proof.
    split; firstorder.
  Qed.

  Local Lemma l {I J} (x : forall i:I, J i -> L) (F: (forall i: I, J i) -> I):
    exists (i: I), forall j: J i, exists f: (forall i: I, J i), x i j = x (F f) (f (F f)).
  Proof.
    apply NNPP. intros contra.
    assert (forall f, exists i, x i (f i) = x (F f) (f (F f))).
    {
      intros f. eexists. reflexivity.
    }
    assert (exists f, forall i, ~ x i (f i) = x (F f) (f (F f))).
    {
      rewrite not_exists_forall in contra.
      apply dep_choice in contra.
      destruct contra as [f Hf].
      exists f. intros i. specialize (Hf i).
      rewrite not_exists in Hf. apply Hf.
    }
    firstorder.
  Qed.

  Lemma inf_sup {I J} (x : forall i:I, J i -> L) :
    inf i, sup j, x i j = sup f, inf i, x i (f i).
  Proof.
    rewrite sup_inf. apply antisymmetry.
    - rewrite inf_iff. intro F.
      pose proof (l x F) as [i Hi].
      apply (inf_at i).
      rewrite sup_iff.
      intros j. specialize (Hi j) as [f Hf].
      eapply sup_at.
      rewrite Hf. reflexivity.
    - rewrite inf_iff. intros i.
      eapply inf_at. instantiate (1 := fun _ => i). cbn.
      rewrite sup_iff. intros f.
      eapply sup_at. instantiate (1 := f i).
      reflexivity.
  Qed.

End PROPERTIES.


(** * Joins and meets with predicates *)

(** It is often convenient to take the [sup] or [inf] by ranging over
  the elements of an index type which satisfy a given predicate. *)

Definition fsup {L : cdlattice} {I} (P : I -> Prop) (f : I -> L) :=
  lsup (I := sig P) (fun x => f (proj1_sig x)).

Notation "'sup' { x | P } , M" :=
  (fsup (fun x => P) (fun x => M))
  (at level 65, x ident, right associativity).
Notation "'sup' { x : A | P } , M" :=
  (fsup (fun x : A => P) (fun x : A => M))
  (at level 65, A at next level, x ident, right associativity).

Definition finf {L : cdlattice} {I} (P : I -> Prop) (f : I -> L) :=
  linf (I := sig P) (fun x => f (proj1_sig x)).

Notation "'inf' { x | P } , M" :=
  (finf (fun x => P) (fun x => M))
  (at level 65, x ident, right associativity).
Notation "'inf' { x : A | P } , M" :=
  (finf (fun x : A => P) (fun x : A => M))
  (at level 65, x ident, right associativity).

Section PREDICATES.
  Context {L : cdlattice}.

  Lemma fsup_ub {I} (i : I) (P : I -> Prop) (x : I -> L) :
    P i -> x i [= fsup P x.
  Proof.
    intros Hi.
    apply (sup_ub (exist P i Hi) (fun i => x (proj1_sig i))).
  Qed.

  Lemma fsup_at {I} (i : I) (P : I -> Prop) (x : L) (y : I -> L) :
    P i -> x [= y i -> x [= fsup P y.
  Proof.
    intros Hi Hx. etransitivity; eauto using fsup_ub.
  Qed.

  Lemma fsup_lub {I} (P : I -> Prop) (x : I -> L) (y : L) :
    (forall i, P i -> x i [= y) -> fsup P x [= y.
  Proof.
    intros Hy. apply sup_lub. intros [i Hi]. auto.
  Qed.

  Lemma finf_lb {I} (i : I) (P : I -> Prop) (x : I -> L) :
    P i -> finf P x [= x i.
  Proof.
    intros Hi.
    apply (inf_lb (exist P i Hi) (fun i => x (proj1_sig i))).
  Qed.

  Lemma finf_at {I} (i : I) (P : I -> Prop) (x : I -> L) (y : L) :
    P i -> x i [= y -> finf P x [= y.
  Proof.
    intros Hi Hy. etransitivity; eauto using finf_lb.
  Qed.

  Lemma finf_glb {I} (P : I -> Prop) (x : L) (y : I -> L) :
    (forall i, P i -> x [= y i) -> x [= finf P y.
  Proof.
    intros Hy. apply inf_glb. intros [i Hi]. auto.
  Qed.
End PREDICATES.


(** * Derived operations *)

Section OPS.
  Context {L : cdlattice}.

  (** Least element *)

  Definition bot : L :=
    sup i : Empty_set, match i with end.

  Lemma bot_lb x :
    ref bot x.
  Proof.
    unfold bot. rewrite sup_iff. intros [ ].
  Qed.

  (** ** Binary joins *)

  Definition join (x y : L) :=
    sup b : bool, if b then x else y.

  Lemma join_ub_l x y :
    ref x (join x y).
  Proof.
    unfold join. apply sup_at with (i := true). reflexivity.
  Qed.

  Lemma join_ub_r x y :
    ref y (join x y).
    unfold join. apply sup_at with (i := false). reflexivity.
  Qed.

  Lemma join_lub x y z :
    ref x z -> ref y z -> ref (join x y) z.
  Proof.
    intros Hx Hy. unfold join.
    rewrite sup_iff. intros [|]; auto.
  Qed.

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
    x [= y <-> join x y = y.
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
  Proof.
    unfold top. rewrite inf_iff. intros [ ].
  Qed.

  (** ** Binary meets *)

  Definition meet (x y : L) :=
    inf b : bool, if b then x else y.

  Lemma meet_lb_l x y :
    ref (meet x y) x.
  Proof.
    unfold meet. apply inf_at with (i := true). reflexivity.
  Qed.

  Lemma meet_lb_r x y :
    ref (meet x y) y.
  Proof.
    unfold meet. apply inf_at with (i := false). reflexivity.
  Qed.

  Lemma meet_glb x y z :
    ref x y -> ref x z -> ref x (meet y z).
  Proof.
    intros Hy Hz. unfold meet.
    rewrite inf_iff. intros [|]; auto.
  Qed.

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
    x [= y <-> meet x y = x.
  Proof.
    split; intro.
    - apply antisymmetry. apply meet_lb_l.
      apply meet_glb; auto. reflexivity.
    - rewrite <- H. apply meet_lb_r.
  Qed.

  Hint Resolve join_ub_r
       join_ub_l
       join_lub
       meet_lb_r
       meet_lb_l
       meet_glb
       bot_lb
       top_ub.

  (** ** Properties *)

  Lemma join_bot_l x :
    join bot x = x.
  Proof.
    apply antisymmetry; auto. apply join_lub; easy.
  Qed.

  Lemma join_top_l x :
    join top x = top.
  Proof.
    apply antisymmetry; auto.
  Qed.

  Lemma join_meet_l x y z :
    join (meet x y) z = meet (join x z) (join y z).
  Proof.
    replace (join (meet x y) z) with
        (sup (i : bool), inf (j : bool), (if i then (if j then x else y) else z)).
    - rewrite sup_inf. apply antisymmetry.
      + apply meet_glb; eapply inf_at.
        * instantiate (1 := fun _ => true). cbn. reflexivity.
        * instantiate (1 := fun _ => false). cbn. reflexivity.
      + rewrite inf_iff. intros f.
        destruct (f true) eqn: Ht; destruct (f false) eqn: Hf.
        * apply meet_l. eapply sup_iff.
          intros [|]; eapply sup_at.
          -- instantiate (1 := true). cbn. rewrite Ht. reflexivity.
          -- instantiate (1 := false). cbn. reflexivity.
        * apply meet_l. eapply sup_iff.
          intros [|]; eapply sup_at.
          -- instantiate (1 := true). cbn. rewrite Ht. reflexivity.
          -- instantiate (1 := false). cbn. reflexivity.
        * apply meet_r. eapply sup_iff.
          intros [|]; eapply sup_at.
          -- instantiate (1 := true). cbn. rewrite Ht. reflexivity.
          -- instantiate (1 := false). cbn. reflexivity.
        * apply meet_r. eapply sup_iff.
          intros [|]; eapply sup_at.
          -- instantiate (1 := true). cbn. rewrite Ht. reflexivity.
          -- instantiate (1 := false). cbn. reflexivity.
    - unfold join, meet. apply antisymmetry.
      + rewrite sup_iff. intros [|]; eapply sup_at.
        * instantiate (1 := true). cbn. reflexivity.
        * instantiate (1 := false). cbn.
          apply inf_at. exact true. reflexivity.
      + rewrite sup_iff. intros [|]; eapply sup_at.
        * instantiate (1 := true). cbn. reflexivity.
        * instantiate (1 := false). cbn.
          rewrite inf_iff. intros. reflexivity.
  Qed.

  (* ... foo_bar_l, foo_bar_r ... *)


  Lemma join_comm x y :
    join x y = join y x.
  Proof.
    apply antisymmetry; apply join_lub; auto.
  Qed.

  Lemma meet_comm x y :
    meet x y = meet y x.
  Proof.
    apply antisymmetry; apply meet_glb; auto.
  Qed.

  Lemma join_idemp x :
    join x x = x.
  Proof.
    now rewrite <- ref_join.
  Qed.

  Lemma meet_idemp x :
    meet x x = x.
  Proof.
    now rewrite <- ref_meet.
  Qed.

  (** These properties are more than enough to completely define the
    derived operations, so that relying on their concrete definition
    should not be necessary. *)

  Global Opaque bot top join meet.

End OPS.

Infix "||" := join (at level 50, left associativity).
Infix "&&" := meet (at level 40, left associativity).

(** ** Miscellaneous Properties *)
Lemma sup_option {L: cdlattice} {A} (f: A -> L) (g: L):
  sup x: option A,
      match x with
      | Some a => f a
      | None => g
      end = g || sup x: A, f x.
Proof with reflexivity.
  apply antisymmetry.
  - apply sup_iff. intros [a|].
    + apply join_r. apply (sup_at a)...
    + apply join_l...
  - apply join_lub.
    + apply (sup_at None)...
    + apply sup_iff. intros a.
      apply (sup_at (Some a))...
Qed.

Lemma sup_sup {L: cdlattice} {I J: Type} (c: I -> J -> L):
  sup i, sup j, c i j = sup j, sup i, c i j.
Proof with reflexivity.
  apply antisymmetry.
  - apply sup_iff. intros i. apply sup_iff. intros j.
    apply (sup_at j). apply (sup_at i)...
  - apply sup_iff. intros j. apply sup_iff. intros i.
    apply (sup_at i). apply (sup_at j)...
Qed.

Require Import FunctionalExtensionality.

Definition c {L: cdlattice} {I: Type} (x: L) (y: I -> L): forall (b: bool), (if b return Type then unit else I) -> L.
Proof.
  intros [|].
  - intros. refine x.
  - refine y.
Defined.

Definition fc {I: Type} (i: I): forall (i: bool), if i return Type then unit else I.
Proof.
  intros [|].
  - refine tt.
  - refine i.
Defined.

Lemma join_inf {L: cdlattice} {I: Type} (x: L) (y: I -> L):
  x || (inf i, y i) = inf i, x || y i.
Proof with reflexivity.
  pose proof @sup_inf.
  specialize (H L _ _ (c x y)). cbn in H.
  Local Transparent join.
  unfold join.
  assert (sup b : bool, (if b then x else inf i : I, y i) =
                       sup i : bool, inf j : if i return Type then unit else I, c x y i j) as ->.
  {
    f_equal. apply functional_extensionality.
    intros [|]; cbn.
    - apply antisymmetry.
      + apply inf_iff. intros...
      + apply (inf_at tt)...
    - reflexivity.
  }
  rewrite H. clear H.
  apply antisymmetry.
  - apply inf_iff. intros i.
    apply (inf_at (fc i)).
    apply sup_iff. intros [|]; cbn.
    + apply (sup_at true)...
    + apply (sup_at false)...
  - apply inf_iff. intros f.
    apply (inf_at (f false)).
    apply sup_iff. intros [|]; cbn.
    + apply (sup_at true)...
    + apply (sup_at false)...
Qed.
