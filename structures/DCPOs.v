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

(** ** Kleene fixed point *)

(** *** Definition *)

Section LFP.
  Context `{Pdcpo : DCPO} (f : P -> P) `{Hf : !ScottContinuous false f}.

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
End LFP.


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
