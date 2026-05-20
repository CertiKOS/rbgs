Require Import Coq.Logic.Classical.
Require Import FunctionalExtensionality.
Require Import PropExtensionality.
Require Import ProofIrrelevance.
Require Import Program.
Require Import coqrel.LogicalRelations.
Require Import interfaces.Category.
Require Import interfaces.ConcreteCategory.
Require Import structures.Posets.

(** * Directed-complete partial orders *)

(** The semantics of loops, iteration or recursion are often computed
  as limits of sequences of increasingly terminating computations.
  ...

 *)

(** ** Directed sets *)

(** *** Definition *)

(** Since we are primarily interested in bounded dcpos,
  we use a non-standard definition of directed set which permits
  empty sets. This allows us to treat the lower bound uniformly
  as a directed supremum. *)

Class Directed `{PartialOrder} {I} (x : I -> P) :=
  directed : forall i j, exists k, R (x i) (x k) /\ R (x j) (x k).

(** *** Basic instances *)

Global Instance Empty_set_directed `{PartialOrder} (x : Empty_set -> P) :
  Directed x.
Proof.
  intros [ ].
Qed.  

Global Instance unit_set_directed `{PartialOrder} (x : unit -> P) :
  Directed x.
Proof.
  intros [ ] [ ]. exists tt.
  split; reflexivity.
Qed.

Lemma pair_directed `{PartialOrder} (x y : P) :
  R x y ->
  Directed (bool_rect _ y x).
Proof.
  intros Hxy i j. exists true. cbn.
  destruct i, j; cbn; split; auto; reflexivity.
Qed.

Global Hint Extern 1 (Directed _) =>
  eapply @pair_directed; assumption : typeclass_instances.

(** *** Image through a monotonic function *)

Lemma directed_apply {P Q R S} (f : P -> Q) {I} (x : I -> P) :
  forall HR : @PartialOrder P R,
  forall HQ : @PartialOrder Q S,
  Monotonic f (R ++> S) ->
  Directed x ->
  Directed (fun i => f (x i)).
Proof.
  intros HR HQ Hf Hx i j. red in Hf.
  destruct (directed i j) as (k & Hik & Hjk).
  exists k. split; rauto.
Qed.

Global Hint Extern 5 (Directed (fun i => ?f (?x i))) =>
  eapply @directed_apply : typeclass_instances.

(** ** DCPOs *)

(** A directed-complete partial order is a poset where every directed
  subset has a supremum. Since we define directed sets as possibly
  empty, the resulting structure is a bounded dcpo. *)

Class DCPO (P : Type) :=
  {
    lce : relation P;
    lce_po :> PartialOrder lce;
    dsup : forall {I} (x : I -> P) `{Hx: !Directed x}, P;
    dsup_is_sup {I} (x : I -> P) `{!Directed x} :> IsSup x (dsup x);
  }.

Definition lct `{DCPO} x y :=
  lce x y /\ x <> y.

Lemma lct_not_lce `{DCPO} x y :
  lct x y -> ~ lce y x.
Proof.
  intros [Hxy Hneq] Hyx.
  apply Hneq, antisymmetry; auto.
Qed.

(** *** Properties of [dsup] *)

(** For convenience, we provide specialized versions of
  the supremum properties. *)

Lemma dsup_ub `{DCPO} {I} (x : I -> P) `{Dx : !Directed x} (i : I) :
  lce (x i) (dsup x).
Proof.
  apply sup_ub.
Qed.

Lemma dsup_lub `{DCPO} {I} (x : I -> P) `{Dx : !Directed x} (y : P) :
  (forall i, lce (x i) y) -> lce (dsup x) y.
Proof.
  apply sup_lub.
Qed.

(** *** Least element *)

Definition bot `{DCPO} :=
  dsup (Empty_set_rect _).

Lemma bot_lb `{DCPO} x :
  lce bot x.
Proof.
  apply sup_lub. tauto.
Qed.

(** *** Binary case for [dsup] *)

(** In some proofs below we will need to express ordering
  in terms of directed suprema of pairs. Below we provide
  the relevant properties. *)

Definition bset {A} (x y : A) : bool -> A :=
  bool_rect _ y x.

Lemma bset_natural {A B} (f : A -> B) (x y : A) :
  bset (f x) (f y) = fun i => f (bset x y i).
Proof.
  apply functional_extensionality.
  intros [|]; reflexivity.
Qed.

(** Pairs like the ones defined above are directed when
  the two elements are related. *)

Lemma bset_directed_r `{DCPO} (x y : P) :
  lce x y -> Directed (bset x y).
Proof.
  intros Hxy i j. exists true. cbn.
  destruct i, j; cbn; split; auto; reflexivity.
Qed.

Global Hint Extern 1 (Directed _) =>
  apply @bset_directed_r; assumption : typeclass_instances.

Lemma bset_directed_l `{DCPO} (x y : P) :
  lce y x -> Directed (bset x y).
Proof.
  intros Hxy i j. exists false. cbn.
  destruct i, j; cbn; split; auto; reflexivity.
Qed.

Global Hint Extern 1 (Directed _) =>
  apply @bset_directed_l; assumption : typeclass_instances.

(** Moreover, the supremum is the largest of the two elements. *)

Lemma lce_dsup_r `{DCPO} (x y : P) `{Dxy: !Directed (bset x y)} :
  lce x y -> dsup (bset x y) = y.
Proof.
  intros Hxy.
  apply antisymmetry.
  - apply dsup_lub. intros [|]; cbn; auto. reflexivity.
  - apply (dsup_ub (bset x y) true).
Qed.

Lemma lce_dsup_l `{DCPO} (x y : P) `{Dxy: !Directed (bset x y)} :
  lce y x -> dsup (bset x y) = x.
Proof.
  intros Hxy.
  apply antisymmetry.
  - apply dsup_lub. intros [|]; cbn; auto. reflexivity.
  - apply (dsup_ub (bset x y) false).
Qed.

(** ** Derived DCPOs *)

(** *** Binary products *)

Section PROD_DCPO.
  Context {P Q} `{Pdcpo : DCPO P} `{Qdcpo : DCPO Q}.

  Local Instance prod_dcpo_po :
    @PartialOrder (P * Q) (lce * lce).
  Proof.
    split.
    - typeclasses eauto.
    - intros [x1 x2] [y1 y2] [Hxy1 Hxy2] [Hyx1 Hyx2]. cbn in *.
      f_equal; apply antisymmetry; auto.
  Qed.

  Local Instance prod_directed_fst {I} (x : I -> P * Q) :
    Directed x ->
    Directed (fun i => fst (x i)).
  Proof.
    intros Hx.
    eapply directed_apply; auto.
    rauto.
  Qed.

  Local Instance prod_directed_snd {I} (x : I -> P * Q) :
    Directed x ->
    Directed (fun i => snd (x i)).
  Proof.
    intros Hx.
    eapply directed_apply; auto.
    rauto.
  Qed.

  Global Instance prod_issup {I} (x : I -> P * Q) (y : P * Q) :
    IsSup (fun i => fst (x i)) (fst y) ->
    IsSup (fun i => snd (x i)) (snd y) ->
    IsSup x y.
  Proof.
    firstorder.
  Qed.

  Local Program Instance prod_dcpo : DCPO (P * Q) :=
    {
      lce := lce * lce;
      dsup I x Hx := (dsup (fun i => fst (x i)), dsup (fun i => snd (x i)));
    }.

End PROD_DCPO.

Global Hint Extern 2 (DCPO (?P * ?Q)) =>
  eapply @prod_dcpo : typeclass_instances.

Global Hint Extern 1 (Directed (fun i => fst _)) =>
  eapply @prod_directed_fst : typeclass_instances.

Global Hint Extern 1 (Directed (fun i => snd _)) =>
  eapply @prod_directed_snd : typeclass_instances.

(** *** Dependent products *)

Section FORALL_DCPO.
  Context {I} {P : I -> Type} `{Pdcpo : forall i:I, DCPO (P i)}.
  Obligation Tactic := cbn.

  Local Instance forall_dcpo_po :
    @PartialOrder (forall i, P i) (forallr - @ i, lce).
  Proof.
    repeat split.
    - intros x i.
      reflexivity.
    - intros x y z Hxy Hyz i.
      etransitivity; eauto.
    - intros x y Hxy Hyx.
      apply functional_extensionality_dep. intros i.
      apply antisymmetry; auto.
  Qed.

  Global Instance forall_directed {J} (x : J -> forall i:I, P i) (i : I) :
    Directed x ->
    Directed (fun j => x j i).
  Proof.
    firstorder.
  Qed.

  Global Instance forall_issup {J} (x: J -> forall i, P i) (y: forall i, P i) :
    (forall i, IsSup (fun j => x j i) (y i)) ->
    IsSup x y.
  Proof.
    intros Hy.
    split.
    - firstorder.
    - intros z Hxz i.
      apply sup_lub.
      firstorder.
  Qed.

  Local Instance forall_dcpo : DCPO (forall i, P i) :=
    {
      lce := forallr - @ i, lce;
      dsup J x Hx i := dsup (fun j => x j i);
    }.

End FORALL_DCPO.

Global Hint Extern 1 (DCPO (forall i, _)) =>
  eapply @forall_dcpo : typeclass_instances.

(** ** Scott-continuous functions *)

(** *** Definition *)

(** A Scott-continuous function preserves directed suprema.
  The formulation below uses monotonicity as a starting point.
  This takes care of preserving the "upper bound" aspect of
  suprema, and we add the "least" as a separate condition. *)

(** We use a flag [strict] to control whether the morphism
  is expected to preserve [bot]. This is done by apply the
  following condition to the index set used with [dsup].

  NB: this could be incorporated into the [Directed] class, and
  the same approach could be used to jointly define bounded and
  not-necessarily-bounded DCPOs. *)

Class ArityCondition (strict : bool) J :=
  arity_condition : if strict then True else inhabited J.

Global Instance ac_strict_trivial J :
  ArityCondition true J.
Proof.
  firstorder.
Qed.

Global Instance ac_nonstrict_unit :
  ArityCondition false unit.
Proof.
  repeat constructor.
Qed.

Global Instance ac_nonstrict_bool :
  ArityCondition false bool.
Proof.
  repeat constructor.
Qed.

Global Instance ac_nonstrict_nat :
  ArityCondition false nat.
Proof.
  repeat constructor.
Qed.

(** Our definition states that the image of [dsup x] is the supremum
  of the image of [x]. This way we don't need to involve the target
  [dsup] operation, which is only defined when [f x] is directed.
  The preservation of the "upper bound" condition is equivalent to
  monotonicity; the "least" condition is just stated as-is. *)

Class ScottContinuous strict {A B} `{Adcpo: DCPO A} `{Bdcpo: DCPO B} (f: A -> B) :=
  {
    sc_lce :>
      Monotonic f (lce ++> lce);
    sc_lub `{HJ : ArityCondition strict} (x: J -> A) `{Dx: !Directed x} y:
      (forall j, lce (f (x j)) y) -> lce (f (dsup x)) y;
  }.

(** Any strict Scott-continuous functions is also non-strict Scott-continuous. *)

Lemma sc_weaken `(ScottContinuous true) :
  ScottContinuous false f.
Proof.
  firstorder.
Qed.

Global Hint Extern 1 (ScottContinuous false _) =>
  eapply @sc_weaken : typeclass_instances.

(** *** Equational statement *)

Section SC_SUP.
  Context `{ScottContinuous}.

  (** The definition above is equivalent to this statement. *)

  Local Instance sc_sup {J} (x : J -> A) (y : A) :
    IsSup x y ->
    ArityCondition strict J ->
    Directed x ->
    IsSup (fun j => f (x j)) (f y).
  Proof.
    split.
    - intro j. monotonicity. apply sup_ub.
    - rewrite (sup_unique y (dsup x)).
      apply sc_lub.
  Qed.

  (** Because suprema are unique, this means [dsup] is preserved. *)

  Context `{HJ : ArityCondition strict} (x : J -> A) `{Dx: !Directed x}.

  Lemma sc_dsup `{Dy: !Directed (fun i => f (x i))} :
    f (dsup x) = dsup (fun i => f (x i)).
  Proof.
    apply (sup_unique _ _).
  Qed.

  (** For maximum generality, the lemma above is stated in terms of
    a pre-existing proof that the image set is directed, but when
    rewriting we will often need the following instance. *)

  Lemma sc_directed :
    Directed (fun i => f (x i)).
  Proof.
    intros i j.
    destruct (directed i j) as (k & Hi & Hj).
    exists k. split; rauto.
  Qed.

End SC_SUP.

Global Hint Extern 2 (IsSup _ (?f ?a)) =>
  eapply @sc_sup : typeclass_instances.

Global Hint Extern 2 (Directed (fun i => _)) =>
  eapply @sc_directed : typeclass_instances.

(** *** Composition *)

Global Instance sc_id `{Adcpo : DCPO} strict :
  ScottContinuous strict (fun a => a).
Proof.
  split.
  - rauto.
  - intros. apply sup_lub. auto.
Qed.

Global Instance sc_compose {A B C} `{DCPO A} `{DCPO B} `{DCPO C} {strict} :
  forall (g : B -> C) (f : A -> B),
    ScottContinuous strict g ->
    ScottContinuous strict f ->
    ScottContinuous strict (fun a => g (f a)).
Proof.
  intros g f Hg Hf. split.
  - rauto.
  - intros. apply sup_lub. auto.
Qed.

(** ** Category of DCPOs and strict Scott-continuous functions *)

Module DCPO <: ConcreteCategory.

  Class Structure (P : Type) : Type :=
    structure_dcpo : DCPO P.

  Global Hint Immediate structure_dcpo : typeclass_instances.
  Global Hint Extern 1 (Structure _) => red : typeclass_instances.

  Class Morphism {A B} `{Adcpo: DCPO A} `{Bdcpo: DCPO B} (f : A -> B) :=
    morphism_sc : ScottContinuous true f.

  Global Hint Immediate morphism_sc : typeclass_instances.
  Global Hint Extern 1 (Morphism _) => red : typeclass_instances.

  Global Instance id_mor `{DCPO} :
    Morphism (fun x => x).
  Proof.
    typeclasses eauto.
  Qed.

  Global Instance compose_mor :
    forall {A B C} `{DCPO A} `{DCPO B} `{DCPO C} (g: B -> C) (f: A -> B),
      Morphism g ->
      Morphism f ->
      Morphism (fun x => g (f x)).
  Proof.
    typeclasses eauto.
  Qed.

  Include ConcreteCategoryTheory.

End DCPO.

Notation dcpo := DCPO.structured_set.


(** * Free DCPO *)

(** The free DCPO generated by a set [X] is the flat semilattice which
  extends [X] with a bottom element. This is in essence [option X],
  however that computable version does not allow us to define the
  possibly infinite directed suprema we need. The version below allows
  these suprema to be defined at the expense of computability. *)

Module FDC.
  Local Obligation Tactic := cbn.

  (** ** Definition *)

  (** Our construction uses sets with at most one element.
    They are ordered under set inclusion.  *)

  Record carrier {A : Type} :=
    {
      is : A -> Prop;
      is_unique a b : is a -> is b -> a = b;
    }.

  Arguments carrier : clear implicits.

  Global Program Instance structure A : DCPO (carrier A) :=
    {
      lce x y := forall a, is x a -> is y a;
      dsup I x Dx := {| is a := exists i, is (x i) a |};
    }.
  Next Obligation. (* partial order *)
    intros A. split.
    - firstorder.
    - intros [x Hx] [y Hy] Hxy Hyx. cbn in *.
      cut (x = y). { intro. subst. f_equal. apply proof_irrelevance. }
      apply functional_extensionality. intro a.
      apply propositional_extensionality. firstorder.
  Qed.
  Next Obligation. (* dsup well-defined *)
    intros A I x Dx a b [i Hi] [j Hj].
    pose proof (Dx i j) as (k & Hik & Hjk).
    eauto using is_unique.
  Qed.
  Next Obligation. (* dsup is supremum *)
    firstorder.
  Qed.

  (** ** Monad stuff / map from Set *)

  Program Definition emb {A} (a : A) : carrier A :=
    {| is := eq a |}.
  Next Obligation.
    congruence.
  Qed.

  Program Definition ext {A} `{Pdc: DCPO} (f : A -> P) (x : carrier A) : P :=
    dsup (I := {a | is x a}) (fun a => f (`a)) (Hx := _).
  Next Obligation.
    intros A P Pdc f x [a Ha] [b Hb]. cbn.
    assert (a = b) by eauto using is_unique; subst b.
    exists (exist _ a Ha). cbn. split; reflexivity.
  Qed.

  Lemma ext_emb_r {A} `{DCPO} (f : A -> P) (a : A) :
    ext f (emb a) = f a.
  Proof.
    apply antisymmetry.
    - apply sup_lub. intros [_ [ ]]. cbn.
      reflexivity.
    - apply (sup_at (exist _ a eq_refl)). cbn.
      reflexivity.
  Qed.

  Lemma ext_emb_l {A} (x : carrier A) :
    ext emb x = x.
  Proof.
    apply antisymmetry; cbn.
    - intros _ [[a Ha] [ ]]. auto.
    - intros a Ha. exists (exist _ a Ha). auto.
  Qed.

  Lemma ext_ext {A B C} (g : B -> carrier C) (f : A -> carrier B) (x : carrier A) :
    ext g (ext f x) = ext (fun b => ext g (f b)) x.
  Proof.
    apply antisymmetry; cbn.
    - intros c [[b [[a Ha] Hb]] Hc]. cbn in *.
      exists (exist _ a Ha). cbn.
      exists (exist _ b Hb). cbn.
      assumption.
    - intros c [[a Ha] [[b Hb] Hc]]. cbn in *.
      exists (exist _ b (ex_intro _ (exist _ a Ha) Hb)). cbn.
      assumption.
  Qed.

End FDC.

Notation fdc := FDC.carrier.


(** * Fixed point constructions *)

(** ** Overview *)

(** Every monotone function [f : D -> D] in a DCPO [D] admits
  a least fixed point [μf : D]. This can be used to obtain semantics
  for loops and recursion that abstract away the numbers of unfolding
  steps involved in reaching a result, retaining only a distinction
  between computations based on whether they terminate, and the result
  they produce when they do.

  For example, consider the traditional example of a recursive function:

      fact n := if n=0 then 1 else n * fact (n-1).

  We would like to interpret this definition as [⟦fact⟧ : Z -> fdc Z]
  in the domain of partial functions from integers to integers, so that
  [⟦fact⟧(n)] gives the result of calling [fact] with argument value [n],
  or is undefined when this would result in a non-terminating computation.
  We can compute this partial function as a fixed point of the functional
  [Φ : (Z -> fdc Z) -> (Z -> fdc Z)] defined as:

      Φ F n := if n=0 then 1 else n * F (n-1).

  Note that [Φ] avoids self-referentiality by "delegating" the
  computation of recursive calls to its function argument [F].
  It is monotone in the sense that plugging in an [F'] defined
  for more [n]'s but otherwise idendical to [F] will yield a similarly
  "more defined" [Φ F ⊑ Φ F']. Hence, by our fixed point construction
  we can obtain a function [μΦ : Z -> fdc Z] such that [Φ μΦ = μφ].
  In other words, [μΦ] is a version of [Φ] which can handle
  its own recursive calls:

      μΦ n  =  Φ μΦ n  =  if n=0 then 1 else n * μΦ (n-1).

  Below we provide two constructions of the least fixed point in a DCPO.
  The Kleene-style fixed point requires [Φ] to be Scott-continuous,
  but is simpler to define and illustrates the basic ideas behind the
  construction. The Tarsky-style construction applies to all monotonic
  functions regardless of continuity, but requires generalizing the
  Kleene iteration to ordinal numbers. *)

(** ** Kleene fixed point *)

Section LFP.
  Context `{Pdcpo : DCPO} (f : P -> P) `{Hf : !ScottContinuous false f}.

  (** *** Approximation sequence *)

  (** Consider a Scott-continuous function [f : D -> D] on a DCPO [D].
    Since [⊥ ≲ f ⊥] and [f] is monotonic, we have [f ⊥ ≲ f (f ⊥)],
    and in turn [f (f ⊥) ≲ f (f (f ⊥))] etc, so that by induction on [n]
    the iterates [f^n ⊥ ≲ f (f^n ⊥)] are aleady postfixed points of [f]
    and constitute an increasing sequence. By virtue of being a
    postfixed point, each iterate is either a fixed point with
    [f^{n+1} = f (f^n) = f^n], or is succeeded by an approximation
    [f^{n+1} <> f^n] that is strictly greater than all preceding ones.
    Moreover, since [⊥ ≲ x] and [f^n x ≲ x] for any prefixed point [x],
    it must be the case that [f^n ⊥ ≲ x] for any fixed (and therefore
    prefixed) point [x]. *)

  Fixpoint lfp_approx (n : nat) :=
    match n with
      | 0 => bot
      | S p => f (lfp_approx p)
    end.

  Lemma lfp_approx_incr n :
    lce (lfp_approx n) (lfp_approx (S n)).
  Proof.
    induction n; cbn.
    - apply bot_lb.
    - rauto.
  Qed.

  Local Instance lfp_approx_lce :
    Monotonic lfp_approx (Peano.le ++> lce).
  Proof.
    intros m n Hmn.
    induction Hmn.
    - reflexivity.
    - etransitivity; eauto using lfp_approx_incr.
  Qed.

  (** *** Limit *)

  (** Although the sequence [f^n ⊥] may never itself reach the actual
    least fixed point [μf], its limit [f^* ⊥ := dsup n, f^n ⊥] shares
    the property of being a postfixed point and below any prefixed point. *)

  Global Instance lfp_approx_directed :
    Directed lfp_approx.
  Proof.
    intros m n. exists (Nat.max m n).
    split; monotonicity.
    - apply PeanoNat.Nat.le_max_l.
    - apply PeanoNat.Nat.le_max_r.
  Qed.

  Definition lfp :=
    dsup lfp_approx.

  (** *** Properties *)

  (** Moreover, if [f] is Scott-continuous, then
    [f (f^* ⊥) = dsup n, f (f^n ⊥) = dsup n, f^(n+1) ⊥ = f^* ⊥]
    so that [f^* ⊥] is indeed the least fixed point. *)

  Lemma lfp_fixed :
    f lfp = lfp.
  Proof.
    unfold lfp.
    apply antisymmetry.
    - apply sup_lub. intros n.
      apply sup_at with (S n).
      reflexivity.
    - apply sup_lub. intros [|n]; cbn.
      + apply bot_lb.
      + monotonicity.
        apply sup_ub.
  Qed.

  Lemma lfp_least (x : P) :
    f x = x -> lce lfp x.
  Proof.
    intros Hx.
    apply sup_lub. intros n.
    induction n; cbn.
    - apply bot_lb.
    - rewrite <- Hx.
      rauto.
  Qed.

  Lemma lfp_least_prefixed (y : P) :
    lce (f y) y -> lce lfp y.
  Proof.
    intros H.
    apply sup_lub. intros n.
    induction n; cbn; intros.
    - apply bot_lb.
    - etransitivity; rauto.
  Qed.
End LFP.

(** Unfortunately, in some applications the recursive processes
  we wish to study fail Scott-continuity. This is especially true
  in the context of concurrency and fair scheduling, which involve
  infinite nondeterminism. In that case, even [f^* ⊥] may not be
  a fixed point yet, and further applications of [f] and taking
  limits may be necessary. To account for this process we must
  generalize the finite iterates [f^n ⊥] from natural numbers [n]
  to ordinal numbers [α] and a corresponding notion of
  transfinite iterates [f^α]. *)

(** ** Ordinal numbers *)

(** To index our new approximation sequence, we need
  a representation of ordinal numbers. Ordinal numbers
  generalize natural numbers by allowing the construction
  of a least upper bound for any set of predecessor
  ("limit ordinals") as well as zero and successors. *)

Module Ord.

  (** *** Definition *)

  (** We represent ordinals using an inductive type with
    a single constructor [sup_succ {I} : (I -> ord) -> ord],
    where [sup_succ α] represents the limit ordinal ⋃ᵢ (αᵢ + 1).
    Zero can be represented as [sup_succ (I := Empty_set) _]
    and the successor of [α] as [sup_succ (I := unit) (fun _ => α)].
    In other words, as with [nat], the number being represented
    corresponds to the depth of the tree, but unlike [nat] the
    branching allows us to construct trees with infinite depths.

    This approach is used in the mechanization of ordinals
    published by the SNU Software Foundations Laboratory at
    https://github.com/snu-sf/Ordinal.
    Note that the representation is not canonical since
    multiple sets may have the same sup, but this does not
    matter for our purposes. *)

  (** For clarity, we name the universe [Ord.U] from which
    we draw the possible arities of [sup_succ]. *)

  Definition U : Type := Type.

  Inductive t :=
    sup_succ {
      ar : U;
      pred : ar -> t;
    }.

  Arguments sup_succ {ar}.

  (** *** Ordering *)

  (** Since every ordinal is a constructed as a [sup],
    they can be ordered as follows. *)

  Fixpoint le (α β : t) : Prop :=
    forall i, exists j, le (pred α i) (pred β j).

  (** Note that [le] is not antisymmetric but defines a preorder.
    There is an equivalence class in this preorder for each ordinal. *)

  Global Instance le_preo :
    PreOrder le.
  Proof.
    split.
    - intros α.
      induction α; cbn; eauto.
    - intros α.
      induction α as [I αs Hα]; cbn.
      intros β. revert I αs Hα.
      induction β as [J βs Hβ]; cbn.
      intros I αs IHα [K γs] Hαβ Hβγ.
      intros i.
      specialize (Hαβ i) as [j Hij].
      specialize (Hβγ j) as [k Hjk].
      eauto.
  Qed.

  (** As expected, every ordinal is strictly greated than
    its predecessors. *)

  Lemma le_pred α :
    forall i, le (pred α i) α.
  Proof.
    induction α as [I α IHα]. cbn.
    intros i. destruct (α i) eqn:?. cbn.
    intros k. exists i. specialize (IHα i).
    rewrite Heqt0 in IHα. cbn in *. specialize (IHα k).
    congruence.
  Qed.

  Lemma max_succ_new α :
    forall i, ~ le α (pred α i).
  Proof.
    induction α as [I α IHα]. cbn.
    intros i Hi. specialize (Hi i) as [j H].
    eapply IHα; eauto.
  Qed.

  (** Ordinals are totally ordered. This property is important
    because it means every increasing [ord]-indexed sequence in
    a dcpo is directed and therefore has a [sup]. *)

  Lemma le_total α β :
    le α β \/ le β α.
  Proof.
    destruct (classic (le α β)); auto. right. revert β H.
    induction α as [I α IHα]. cbn. intros β H.
    induction β as [J β IHβ]. cbn. intros j.
    apply not_all_ex_not in H as [i HI]. exists i.
    apply not_ex_all_not with (n := j) in HI.
    eauto.
  Qed.

  (** We can also define the associated strict order. *)

  Definition lt (α β : t) : Prop :=
    exists j, le α (pred β j).

  Global Instance lt_le :
    subrelation lt le.
  Proof.
    intros α β [j Hj].
    rewrite le_pred in Hj.
    assumption.
  Qed.

  Lemma lt_not_le α β :
    lt α β <-> ~ le β α.
  Proof.
    split.
    - intros [i Hαβ] Hβα.
      apply (max_succ_new β i).
      rauto.
    - unfold lt. revert α.
      induction β as [J β IHβ]. cbn. intros α.
      destruct α as [I α]. cbn. intros H.
      apply not_all_ex_not in H as [i H]. exists i. intros j.
      apply not_ex_all_not with (n := j) in H. eauto.
  Qed.

  Lemma pred_lt α i :
    lt (pred α i) α.
  Proof.
    apply lt_not_le.
    apply max_succ_new.
  Qed.

  Lemma lt_le_r α β γ :
    lt α β -> le β γ -> lt α γ.
  Proof.
    intros Hαβ Hβγ. apply lt_not_le. intros Hγα.
    apply lt_not_le in Hαβ. apply Hαβ. rauto.
  Qed.

  Lemma lt_wf :
    well_founded lt.
  Proof.
    intros γ.
    generalize (reflexivity (R:=le) γ).
    generalize γ at 1 3 as β.
    induction γ as [K γ IHγ]. intros β Hβ.
    constructor. intros α Hα.
    eapply lt_le_r in Hα; eauto.
    destruct Hα as [k Hα]. cbn in Hα. eauto.
  Qed.

  (** *** Ascending chains *)

  (** The key property we will use to show that the transfinite
    iterates of [f] eventually reach a fixed point is that
    for every element of a well-founded set, we can construct
    an ordinal number [α] such that no strictly increasing
    [α]-chain reaches it.  *)

  Section MAX_CHAINS.
    Context {A} (R : relation A).

    (** The following predicate states that there exists
      an [α]-chain ending in [y]. *)

    Fixpoint chain_to (α : t) (y : A) : Prop :=
      forall i, exists x, chain_to (Ord.pred α i) x /\ R x y.

    (** We can then describe the largest ordinal [α] such
      that there is an [α]-chain ending in [y] as follows. *)

    Program Fixpoint rank (y : A) (Hy : Acc R y) : t :=
      sup_succ (fun x : {x | R x y} => rank (` x) _).
    Next Obligation.
      destruct Hy; auto.
    Defined.

    Lemma rank_incr x y (Hxy : R x y) (Hx : Acc R x) (Hy : Acc R y) :
      ~ le (rank y Hy) (rank x Hx).
    Proof.
      destruct Hy as [Hy]. cbn.
      intros H. specialize (H (exist _ x Hxy)) as [j Hj]. cbn in *.
      assert (Hx = Hy x Hxy) by apply proof_irrelevance. subst.
      eapply max_succ_new; eauto.
    Qed.

    Lemma max_chain_length α y Hy :
      chain_to α y -> le α (rank y Hy).
    Proof.
      revert y Hy.
      induction α as [I α IHα]. cbn. intros y Hy Hα i.
      destruct Hy as [Hy]. cbn.
      specialize (Hα i) as (x & Hx & Hxy).
      exists (exist _ x Hxy). cbn. auto.
    Qed.

    (** This means we can define an ordinal larger than any chain. *)

    Definition not_a_chain_length (HR : well_founded R) :=
      sup_succ (fun y => rank y (HR y)).

    Lemma no_long_chain_to y HR :
      ~ chain_to (not_a_chain_length HR) y.
    Proof.
      cbn. intros H. specialize (H y) as (x & Hx & Hxy).
      apply (max_chain_length _ _ (HR x)) in Hx.
      eapply rank_incr; eauto.
    Qed.
  End MAX_CHAINS.

End Ord.

Notation ord := Ord.t.

(** ** Tarsky-style fixed point *)

(** To obtain the least fixed point, we generalize the Kleene
  construction used in the continuous case by constructing
  a family of approximants [f_α] such that [f_(⋃ᵢ 1+αᵢ) = ⋁ᵢ f(f_αᵢ)].
  Note that we recover the Kleene iterates as the special cases
  [f_n = f^n(⊥)] for [n∈ℕ], and [f_ω = f^*(⊥)].

  This construction is documented for example in the paper
  "Constructive versions of Tarski's fixed point theorems"
  by Cousot & Cousot. *)

Module TFP.
  Section TFP.

  Context `{Pdcpo : DCPO} (f : P -> P) `{Hf : Monotonic f (lce ++> lce)}.

  (** *** Specification *)

  (** While we will eventually be able to construct [f_α]
    by recursion on the structure of [α], the recursion step
    involves a supremum that is only defined by virtue of
    the set of predecessor approximants being directed.
    In turn this is true only because these approximants
    increase with [α] and the fact that ordinal numbers
    are totally ordered.

    Because of this somewhat circular dependency between
    the definition and some of its logical consequences,
    writing a specification first is more convenient. *)

  Fixpoint Approximant (α : ord) (y : P) : Prop :=
    exists x,
      (forall i, Approximant (Ord.pred α i) (x i)) /\
      IsSup (fun i => f (x i)) y.

  Existing Class Approximant.

  (** To show that they can be constructed, we must first
    establish that the approximants increase with their
    ordinal index. *)

  Lemma approx_le α β x y :
    Ord.le α β ->
    Approximant α x ->
    Approximant β y ->
    lce x y.
  Proof.
    revert β x y.
    induction α as [I α IHα]. cbn. intros β.
    induction β as [J β IHβ]. cbn. intros x y Hαβ (xs & Hα & Hx) (ys & Hβ & Hy).
    apply sup_lub. intros i.
    specialize (Hαβ i) as [j Hij].
    apply (sup_at j).
    monotonicity. eauto.
  Qed.

  (** *** Construction step *)

  (** Because ordinals are totally ordered, this means all sets
    of approximants are directed, and we can take their sup. *)

  Local Instance approx_directed {I} α x :
    (forall i:I, Approximant (α i) (x i)) ->
    Directed (fun i => f (x i)).
  Proof.
    intros Hx i j.
    destruct (Ord.le_total (α i) (α j)) as [H|H];
    [exists j | exists i]; split; rstep;
    eapply approx_le; eauto.
  Qed.

  Local Instance approx_step α x :
    forall (Hx : forall i, Approximant (Ord.pred α i) (x i)),
    Approximant α (dsup (fun i => f (x i))).
  Proof.
    destruct α as [I α]. cbn.
    eauto with typeclass_instances.
  Qed.

  (** *** Definition *)

  (** With all this in place we can now define the recursive
    construction of our approximants. *)

  Record approximant {α : ord} :=
    mka {
      aval :> P;
      aprop : Approximant α aval;
    }.

  Arguments approximant : clear implicits.
  Arguments mka {_} _ {_}.
  Local Existing Instance aprop.

  Fixpoint approx_construct (α : ord) : approximant α :=
    mka (dsup (fun i => f (approx_construct (Ord.pred α i)))).

  Notation approx α := (aval (approx_construct α)).

  (** *** Well-foundedness *)

  (** The set of approximants is well-ordered with respect to
    the underlying dcpo. *)

  Lemma approx_lt α β x y :
    lct x y ->
    Approximant α x ->
    Approximant β y ->
    ~ Ord.le β α.
  Proof.
    intros Hxy Hx Hy Hβα.
    eapply lct_not_lce; eauto.
    eapply approx_le; eauto.
  Qed.

  (** Based on this specification, we can show that the set
    of approximants generated in this way is well-founded. *)

  Record candidate : Ord.U :=
    mkc {
      cval :> P;
      cprop : exists α, Approximant α cval;
    }.

  Definition lt (x y : candidate) :=
    lct (cval x) (cval y).

  Lemma lt_wf :
    well_founded lt.
  Proof.
    intros (y & β & Hy). revert y Hy.
    pose proof (Ord.lt_wf β).
    induction H as [β Hβ IHβ]. intros y Hy.
    constructor. intros (x & α & Hx) Hxy. red in Hxy. cbn in *.
    apply IHβ. clear - Hf Hx Hy Hxy.
    apply Ord.lt_not_le. intros Hβα.
    apply lct_not_lce in Hxy. apply Hxy.
    eapply approx_le; eauto.
  Qed.

  Definition lfp :=
    approx (Ord.not_a_chain_length lt lt_wf).

  (** Now we can show that this is indeed the least fixed point. *)

  Lemma approx_postfixed `{Approximant} :
    lce y (f y).
  Proof.
    revert y H.
    induction α as [I α IHα]. cbn in *. intros y (x & Hx & Hy).
    apply sup_lub. intros i.
    monotonicity.
    apply (sup_at i). eauto.
  Qed.

  Lemma approx_below_prefixed `{Approximant} z :
    lce (f z) z ->
    lce y z.
  Proof.
    revert y z H.
    induction α as [I α IHα]. cbn. intros y z (x & Hx & Hy) Hz.
    apply sup_lub. intros i.
    etransitivity; eauto.
  Qed.

  Lemma approx_unfold (α : ord) :
    approx α = dsup (fun i => f (approx (Ord.pred α i))).
  Proof.
    destruct α. reflexivity.
  Qed.

  Lemma approx_stops (α : ord) (i : Ord.ar α) :
    f (approx (Ord.pred α i)) = approx (Ord.pred α i) ->
    f (approx α) = approx α.
  Proof.
    intros Hi.
    apply antisymmetry; auto using approx_postfixed.
    transitivity (f (approx (Ord.pred α i))).
    - rewrite <- Hi. monotonicity.
      rewrite approx_unfold. apply sup_lub. intros j.
      monotonicity.
      apply approx_below_prefixed. rauto.
    - rewrite Hi.
      eapply approx_le; auto using aprop.
      apply Ord.le_pred.
  Qed.

  Lemma approx_chain α :
    Ord.chain_to lt α (mkc (approx α) (ex_intro _ α (_ : Approximant α (approx α)))) \/
    f (approx α) = approx α.
  Proof.
    induction α as [I α IHα]. cbn.
    destruct (classic (forall i, f (approx (α i)) <> approx (α i))).
    - left. intros i.
      exists (mkc (approx (α i)) (ex_intro _ (α i) (_ : Approximant _ (approx (α i))))).
      split.
      + destruct (IHα i); eauto.
        eelim H; eauto.
      + red. cbn. split.
        * rewrite (approx_postfixed (y := approx (α i))).
          apply (sup_at i). reflexivity.
        * intro Hxy. apply (H i). apply antisymmetry.
          -- rewrite Hxy at 2. apply (sup_at i). reflexivity.
          -- apply approx_postfixed.
    - right.
      apply not_all_ex_not in H as [i Hi]. apply NNPP in Hi.
      eapply (approx_stops (Ord.sup_succ α)); eauto.
  Qed.

  Lemma lfp_fixed :
    f lfp = lfp.
  Proof.
    edestruct approx_chain; eauto.
    eelim Ord.no_long_chain_to; eauto.
  Qed.

  Lemma lfp_least_prefixed y :
    lce (f y) y -> lce lfp y.
  Proof.
    apply approx_below_prefixed.
  Qed.

  Lemma lfp_least y :
    f y = y -> lce lfp y.
  Proof.
    intro.
    apply lfp_least_prefixed.
    rauto.
  Qed.

  End TFP.
End TFP.

(** When [f] is Scott-continuous then the two constructions coincide. *)

Lemma lfp_kleene `{Pdcpo : DCPO} f `{Hf : !ScottContinuous false f} :
  TFP.lfp f = lfp f.
Proof.
  apply antisymmetry.
  - apply TFP.lfp_least. apply lfp_fixed.
  - apply lfp_least. apply TFP.lfp_fixed.
Qed.
