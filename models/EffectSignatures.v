Require Import interfaces.Category.
Require Import interfaces.FunctorCategory.
Require Import interfaces.Functor.
Require Import interfaces.MonoidalCategory.
Require Import interfaces.Limits.
Require Import models.Sets.
Require Import FunctionalExtensionality.


(** * Effect signatures *)

(** Category of effect signatures and their homomorphisms.
  This is also known as [Poly] and corresponds to one common
  definition of polynomial endofunctors on [Set]. Here we
  choose to adopt the more algebraic view and terminology
  which is prevalent in computer science applications. *)

Module SigBase <: CartesianCategory.

  (** ** Definition *)

  (** *** Basic definition *)

  (** A signature is a set of operations with arities,
    given in the form of index sets denoting argument positions. *)

  Record sig :=
    {
      op : Type;
      ar : op -> Type;
    }.

  Arguments ar {_} _.

  (** *** Dependent type presentation *)

  (** Signatures can also be represented as dependent types.
    This is the approach taken in the interaction trees library.
    In that case [E N] is the set of operations of arity [N]. *)

  Definition esig := Type -> Type.

  (** *** Converting between the two forms *)

  (** We prefer to avoid using [esig] as our working version
    and dealing with the associated issues of dependent elimination.
    However this form is very convenient for declaring signatures,
    and is used in the interaction trees library, so we provide ways
    to convert between them. *)

  Variant eop (E : esig) :=
    | mkop {X} : E X -> eop E.

  Arguments mkop {E X} m.

  Definition ear {E} (m : eop E) : Type :=
    match m with @mkop _ X _ => X end.

  Definition esig_sig (E : esig) : sig :=
    {|
      op := eop E;
      ar := ear;
    |}.

  Variant sig_esig (E : sig) : esig :=
    | sig_esig_op (m : op E) : sig_esig E (ar m).

  (** In any case, in the remainder of this file we will
    use the [sig] presentation as the one of interest. *)

  Definition t := sig.

  (** ** Applications *)

  (** The following type encodes simple terms of the form
    [m(x_n)_{n∈ar(m)}] consisting of an operation [m] of [E]
    with arguments [x_n] taken in the set [X]. In other words,
    this is the type [∑m∈E · ∏n∈ar(m) · X] *)

  Record application {E : t} {X : Type} :=
    apply {
      operator : op E;
      operand : ar operator -> X;
    }.

  Arguments application : clear implicits.
  Arguments apply {E X} _ _.

  (** We will sometimes use the following notation for simple terms,
    which evokes the game/effects interpretation of signatures.
    NB: The notation [>=] is traditionally used for the [bind]
    operator of monads which feeds its left-hand side to the Kleisli
    extension of the function on the right-hand side. The notation
    below is very much related to this, since it basically feeds the
    outcome of the operation [m] to the argument map [n => x];
    it is a sort of "syntactic bind". However we may need to change
    the notation if we want to be able to use [>=] for monads in the
    future. One good candidate would be [>-]. *)

  Notation "m >= n => x" :=
    {| operator := m; operand n := x |}
    (at level 70, n binder).

  (** We can transform an application by using a given function
    on every argument. *)

  Definition amap {E : t} {X Y} (f : X -> Y) : application E X -> application E Y :=
    fun x => operator x >= n => f (operand x n).

  (** This forms the morphism part of a [Set] endofunctor
    associated with [application E], as shown below. *)

  Lemma amap_id {E : t} {X} (u : application E X) :
    amap (fun x => x) u = u.
  Proof.
    destruct u; reflexivity.
  Qed.

  Lemma amap_compose {E : t} {X Y Z} (g : Y -> Z) (f : X -> Y) (u : application E X) :
    amap g (amap f u) = amap (fun x => g (f x)) u.
  Proof.
    destruct u; reflexivity.
  Qed.

  (** ** Homomorphisms *)

  (** A homomorphism between signatures maps operations forward 
    and outcomes (argument positions) backward. We can use the
    definitions above to formalize this in the following way:
    for each operation of [E], we give a simple term in [F],
    and the arguments used in this term refer back to the valid
    argument positions for the operation of [E]. *)

  Definition m (E F : t) :=
    forall (m : op E), application F (ar m).

  (** Signature homomorphisms can be used to transform simple terms
    of the signature [E] into simple terms of the signature [F]. *)

  Definition hmap {E F} (ϕ : m E F) X : application E X -> application F X :=
    fun x => amap (operand x) (ϕ (operator x)).

  (** So whereas [amap f : application E X -> application E Y] acts
    on the arguments, [hmap φ : application E X -> application F X]
    acts on structure of the term (operator and argument positions).
    The structure and arguments can be transformed independently:
    the result will be the same no matter which one we tranform first. *)

  Lemma hmap_natural {E F} (ϕ : m E F) {X Y} (f : X -> Y) (u : application E X) :
    amap f (hmap ϕ X u) = hmap ϕ Y (amap f u).
  Proof.
    reflexivity.
  Qed.

  (** In fact, [application], [amap] and [hmap] together define a
    functor from the category of signatures and signature homomorphisms
    to the category of endofunctors on Set and natural transformations. *)

  (** ** Compositional structure *)

  Definition id E : m E E :=
    fun m => m >= n => n.

  Definition compose {E F G} (ψ : m F G) (ϕ : m E F) : m E G :=
    fun m => hmap ψ _ (ϕ m).

  Lemma hmap_id {E : t} :
    forall X u, hmap (@id E) X u = u.
  Proof.
    destruct u as [m k].
    reflexivity.
  Qed.

  Lemma hmap_compose {E F G} (ψ : m F G) (ϕ : m E F) :
    forall X t, hmap (compose ψ ϕ) X t = hmap ψ X (hmap ϕ X t).
  Proof.
    intros X [m x]; cbn.
    apply hmap_natural.
  Qed.

  Lemma compose_id_left {E F} (ϕ : m E F) :
    compose (id F) ϕ = ϕ.
  Proof.
    apply functional_extensionality_dep; intros m.
    unfold compose.
    apply hmap_id.
  Qed.

  Lemma compose_id_right {E F} (ϕ : m E F) :
    compose ϕ (id E) = ϕ.
  Proof.
    apply functional_extensionality_dep; intros m.
    unfold compose; cbn.
    apply amap_id.
  Qed.

  Lemma compose_assoc {E F G H} (ϕ: m E F) (ψ: m F G) (θ: m G H) :
    compose (compose θ ψ) ϕ = compose θ (compose ψ ϕ).
  Proof.
    apply functional_extensionality_dep; intros m.
    unfold compose.
    apply hmap_compose.
  Qed.

  Include CategoryTheory.

  (** ** Products *)

  (** The operations of a product of signature contain one operation
    from each of the components, and their arity is the sum of each one.
    In terms of games, the player Σ provides a move in each component game,
    but Π only chooses to reply in one of them. *)

  (** *** Products of arbitrary arity *)

  Record ops {I} (A : I -> t) : Type :=
    mkops { prod_op i :> op (A i) }.

  Arguments prod_op {I A}.

  Canonical Structure prod {I} (A : I -> t) : t :=
    {|
      op := ops A;
      ar m := {i & ar (m i)};
    |}.

  Definition pi {I A} (i : I) : prod A ~~> A i :=
    fun m => m i >= n => existT _ i n.

  Definition tuple {I X A} (f : forall i:I, X ~~> A i) : X ~~> prod A := 
    fun x => {| prod_op i := operator (f i x) |} >=
          '(existT _ i ni) => operand (f i x) ni.

  Proposition pi_tuple {I X A} (f : forall i:I, X ~~> A i) (i : I) :
    pi i @ tuple f = f i.
  Proof.
    unfold compose, hmap, amap, tuple, pi.
    apply functional_extensionality_dep. intro m. cbn.
    destruct (f i m) as [mi k]. cbn. auto.
  Qed.

  Proposition tuple_pi {I X A} (x : X ~~> @prod I A) :
    tuple (fun i => compose (pi i) x) = x.
  Proof.
    apply functional_extensionality_dep. intro m.
    unfold tuple, compose. destruct (x m) as [[f] k]. cbn. f_equal.
    apply functional_extensionality. intros [i ni]. auto.
  Qed.

  Include ProductsTheory.

  (** *** Binary products *)

  (** For now we use this generic implementation of the [Cartesian]
    interface, but we may want to give an explicit definition
    based on the [unit] and [prod] types. *)

  Include CartesianFromProducts.

  (** ** Coproducts *)

  (** In the coproduct we just choose an operation from the component
    signatures, which retains its arity. *)

  (** *** Coproducts of any arities *)

  Canonical Structure coprod {I} (A : I -> t) :=
    {|
      op := {i:I & op (A i)};
      ar '(existT _ i m) := ar m;
    |}.

  Definition iota {I A} (i : I) : A i ~~> coprod A :=
    fun m => existT _ i m >= n => n.

  Definition cotuple {I X A} (f : forall i:I, A i ~~> X) : coprod A ~~> X :=
    fun '(existT _ i m) => operator (f i m) >= n => operand (f i m) n.

  Proposition cotuple_iota {I X A} (f : forall i:I, A i ~~> X) (i : I) :
    cotuple f @ iota i = f i.
  Proof.
    unfold cotuple, iota, compose, hmap, amap.
    apply functional_extensionality_dep. intro m. cbn.
    destruct (f i m) as [x k]. cbn. auto.
  Qed.

  Proposition iota_cotuple {I X A} (f : @coprod I A ~~> X) :
    cotuple (fun i => f @ iota i) = f.
  Proof.
    apply functional_extensionality_dep. intros [i m]. cbn.
    destruct f as [x k]. cbn. auto.
  Qed.

  Include CoproductsTheory.

  (** *** Binary coproducts *)

  (** I still need to formalize the monoidal structures associated
    with coproducts in the [MonoidalCategory] library. *)

End SigBase.

(** ** Tensor product *)

Module Type SigTensReq.
  Include SigBase.
End SigTensReq.

Module SigTens (B : SigTensReq) <: Monoidal SigBase.
  Import B.
  Unset Program Cases.

  Module Tens <: MonoidalStructure B.

  Canonical Structure omap (E F : t) : t :=
    {|
      op := op E * op F;
      ar '(m1, m2) := (ar m1 * ar m2)%type;
    |}.

  Local Infix "*" := omap : obj_scope.

  Definition fmap {E1 E2 F1 F2} : E1~~>F1 -> E2~~>F2 -> (E1 * E2 ~~> F1 * F2) :=
    fun f1 f2 '(m1, m2) => (operator (f1 m1), operator (f2 m2))
                   >= n => (operand (f1 m1) (fst n), operand (f2 m2) (snd n)).

  Local Infix "*" := fmap : hom_scope.

  Proposition fmap_id {E1 E2} :
    id E1 * id E2 = id (E1 * E2).
  Proof.
    apply functional_extensionality_dep. intros [m1 m2]. cbn.
    unfold id. f_equal.
    apply functional_extensionality. intros [n1 n2]. cbn.
    reflexivity.
  Qed.

  Proposition fmap_compose {E1 E2 F1 F2 G1 G2} :
    forall (g1 : F1 ~~> G1) (g2 : F2 ~~> G2)
           (f1 : E1 ~~> F1) (f2 : E2 ~~> F2),
      (g1 @ f1) * (g2 @ f2) = (g1 * g2) @ (f1 * f2).
  Proof.
    intros.
    apply functional_extensionality_dep. intros [m1 m2].
    reflexivity.
  Qed.

  Include BifunctorTheory B B B.

  Canonical Structure unit :=
    {|
      op := unit;
      ar _ := unit;
    |}.

  (** Structural isomorphisms *)

  Program Definition assoc E F G : iso (E * (F * G)) ((E * F) * G) :=
    {|
      fw '(m1, (m2, m3)) := ((m1, m2), m3) >= '((n1, n2), n3) => (n1, (n2, n3));
      bw '((m1, m2), m3) := (m1, (m2, m3)) >= '(n1, (n2, n3)) => ((n1, n2), n3);
    |}.
  Next Obligation.
    unfold compose, hmap, amap, id.
    apply functional_extensionality_dep. intros [m1 [m2 m3]]. cbn. f_equal.
    apply functional_extensionality. intros [n1 [n2 n3]]. auto.
  Qed.
  Next Obligation.
    unfold compose, hmap, amap, id.
    apply functional_extensionality_dep. intros [[m1 m2] m3]. cbn. f_equal.
    apply functional_extensionality. intros [[n1 n2] n3]. auto.
  Qed.

  Program Definition lunit E : iso (unit * E) E :=
    {|
      fw '(_, m) := m >= n => (tt, n);
      bw m := (tt, m) >= '(_, n) => n;
    |}.
  Next Obligation.
    unfold compose, hmap, amap, id.
    apply functional_extensionality_dep. intros [[ ] m]. cbn. f_equal.
    apply functional_extensionality. intros [[ ] n]. auto.
  Qed.

  Program Definition runit E : iso (E * unit) E :=
    {|
      fw '(m, _) := m >= n => (n, tt);
      bw m := (m, tt) >= '(n, _) => n;
    |}.
  Next Obligation.
    unfold compose, hmap, amap, id.
    apply functional_extensionality_dep. intros [m [ ]]. cbn. f_equal.
    apply functional_extensionality. intros [n [ ]]. auto.
  Qed.

  (** Naturality properties *)

  Proposition assoc_nat {A1 B1 C1 A2 B2 C2} :
    forall (f : A1 ~~> A2) (g : B1 ~~> B2) (h : C1 ~~> C2),
      ((f * g) * h) @ assoc A1 B1 C1 = assoc A2 B2 C2 @ (f * (g * h)).
  Proof.
    intros f g h. unfold compose, hmap, amap.
    apply functional_extensionality_dep. intros [m1 [m2 m3]]. cbn. f_equal.
    apply functional_extensionality. intros [[n1 n2] n3]. cbn. auto.
  Qed.

  Proposition lunit_nat {A1 A2} (f : A1 ~~> A2) :
    f @ lunit A1 = lunit A2 @ (id unit * f).
  Proof.
    apply functional_extensionality_dep. intros [[ ] m]. cbn.
    destruct (f m) as [m' k]. reflexivity.
  Qed.

  Proposition runit_nat {A1 A2} (f : A1 ~~> A2) :
    f @ runit A1 = runit A2 @ (f * id unit).
  Proof.
    apply functional_extensionality_dep. intros [m [ ]]. cbn.
    destruct (f m) as [m' k]. reflexivity.
  Qed.

  (** Pentagon identity *)

  Proposition assoc_coh E F G H :
    assoc E F G * id H @ assoc E (F * G) H @ id E * assoc F G H =
    assoc (E * F) G H @ assoc E F (G * H).
  Proof.
    unfold compose, hmap, amap.
    apply functional_extensionality_dep. intros [e [f [g h]]]. cbn. f_equal.
    apply functional_extensionality. intros [[[p q] r] s]. cbn. auto.
  Qed.

  (** Triangle identity *)

  Proposition unit_coh E F :
    (runit E * id F) @ assoc E unit F = id E * lunit F.
  Proof.
    apply functional_extensionality_dep. intros [e [[ ] f]]. cbn. auto.
  Qed.

  End Tens.
End SigTens.

(** Some notable properties we should formalize:
  - the tensor product distrubutes over coproducts
  - we could provide tensors for arbitrary arities
  - there is a closed monoidal structure associated with it.
  - morphism I ~~> E is an operation of E
 *)

(*
    Definition omap E F :=
      {|
        op := E ~~> F;
        ar ϕ := {e : op E & ar (operator (ϕ e))};
      |}.
*)

(** ** Composition product *)

(** This monoidal structure corresponds to the composition of
  polynomial endofunctors. *)

Module SigComp (B : SigTensReq).
  Import B.

  Module Comp <: MonoidalStructure B.

    (** Although they are just special cases of dependent sums,
      declaring the specialized types below makes things easier. *)

    Set Primitive Projections.

    Record op {E F : t} :=
      mkop {
        op_first : B.op E;
        op_next : ar op_first -> B.op F;
      }.

    Arguments op : clear implicits.
    Arguments mkop {_ _}.

    Record ar {E F : t} {m : B.op E} {q : B.ar m -> B.op F} :=
      mkar {
        ar_first : B.ar m;
        ar_next : B.ar (q ar_first);
      }.

    Arguments ar {_ _}.
    Arguments mkar {_ _ _ _}.

    Canonical Structure omap E F :=
      {|
        B.op := op E F;
        B.ar m := ar (op_first m) (op_next m);
      |}.

    Local Infix "⊳" := omap (at level 40) : obj_scope.

    Definition fmap {E1 E2 F1 F2}: E1~~>F1 -> E2~~>F2 -> E1 ⊳ E2 ~~> F1 ⊳ F2 :=
      fun f1 f2 m =>
        let x1 := f1 (op_first m) in
        let x2 n1' := f2 (op_next m (operand x1 n1')) in
        mkop (operator x1) (fun n1' => operator (x2 n1')) >= n =>
        mkar (operand x1 (ar_first n)) (operand (x2 (ar_first n)) (ar_next n)).

    Local Infix "⊳" := fmap (at level 40) : hom_scope.

    Proposition fmap_id {E1 E2} :
      id E1 ⊳ id E2 = id (E1 ⊳ E2).
    Proof.
      reflexivity.
    Qed.

    Proposition fmap_compose {E1 E2 F1 F2 G1 G2} :
      forall (g1 : F1 ~~> G1) (g2 : F2 ~~> G2) (f1 : E1 ~~> F1) (f2 : E2 ~~> F2),
        (g1 @ f1) ⊳ (g2 @ f2) = (g1 ⊳ g2) @ (f1 ⊳ f2).
    Proof.
      reflexivity.
    Qed.

    Include BifunctorTheory B B B.

    (** Structural isomorphisms *)

    Lemma aeq {E X} (m1 m2 : B.op E) (k1 k2 : _ -> X) :
      m1 = m2 ->
      (forall (H : m1 = m2) n, k1 n = k2 (eq_rect m1 B.ar n m2 H)) ->
      apply m1 k1 = apply m2 k2.
    Proof.
      intros Hm Hk.
      specialize (Hk Hm).
      destruct Hm. cbn in *. f_equal.
      apply functional_extensionality. auto.
    Qed.

    Require Import JMeq.

    Lemma aeq' {E X} (m1 m2 : B.op E) (k1 k2 : _ -> X) :
      m1 = m2 ->
      (forall n1 n2, JMeq n1 n2 -> JMeq (k1 n1) (k2 n2)) ->
      apply m1 k1 = apply m2 k2.
    Proof.
      intros Hm Hk. subst. f_equal.
      apply functional_extensionality. intros n.
      apply JMeq_eq. auto.
    Qed.

    Canonical Structure unit := 
      {|
        B.op := unit;
        B.ar _ := unit;
      |}.

    Program Definition assoc E F G : iso (E ⊳ (F ⊳ G)) ((E ⊳ F) ⊳ G) :=
      {|
        fw x := mkop (mkop (op_first x) (fun n => op_first (op_next x n)))
                     (fun n => op_next (op_next x (ar_first n)) (ar_next n))
        >= r => mkar (ar_first (ar_first r))
                     (mkar (ar_next (ar_first r)) (ar_next r));
        bw x := mkop (op_first (op_first x))
                     (fun n => mkop (op_next (op_first x) n)
                                    (fun r => op_next x (mkar n r)))
        >= r => mkar (mkar (ar_first r) (ar_first (ar_next r)))
                     (ar_next (ar_next r))
      |}.

    Program Definition lunit E : iso (unit ⊳ E) E :=
      {|
        fw x := op_next x tt >= n => mkar tt n;
        bw m := mkop tt (fun _ => m) >= y => ar_next y;
      |}.
    Next Obligation.
      unfold compose, hmap, amap, id. cbn.
      apply functional_extensionality_dep. intros [[ ] m]. cbn.
      f_equal.
      apply aeq.
    Admitted.

    Program Definition runit E : iso (E ⊳ unit) E :=
      {|
        fw x := op_first x >= n => mkar n tt;
        bw m := mkop m (fun _ => tt) >= y => ar_first y;
      |}.
    Next Obligation.
      unfold compose, hmap, amap, id. cbn.
      apply functional_extensionality_dep. intros [m k]. cbn.
      cbn in *.
    Admitted.

    (** Naturality properties *)

    Proposition assoc_nat {A1 B1 C1 A2 B2 C2} :
      forall (f : A1 ~~> A2) (g : B1 ~~> B2) (h : C1 ~~> C2),
        ((f ⊳ g) ⊳ h) @ assoc A1 B1 C1 = assoc A2 B2 C2 @ (f ⊳ (g ⊳ h)).
    Proof.
      reflexivity.
    Qed.

    Proposition lunit_nat {A1 A2} (f : A1 ~~> A2) :
      f @ lunit A1 = lunit A2 @ (id unit ⊳ f).
    Proof.
      reflexivity.
    Qed.

    Proposition runit_nat {A1 A2} (f : A1 ~~> A2) :
      f @ runit A1 = runit A2 @ (f ⊳ id unit).
    Proof.
      reflexivity.
    Qed.

    (** Pentagon identity *)

    Proposition assoc_coh E F G H :
      assoc E F G ⊳ id H @ assoc E (F ⊳ G) H @ id E ⊳ assoc F G H =
        assoc (E ⊳ F) G H @ assoc E F (G ⊳ H).
    Proof.
      reflexivity.
    Qed.

    (** Triangle identity *)

    Proposition unit_coh E F :
      (runit E ⊳ id F) @ assoc E unit F = id E ⊳ lunit F.
    Proof.
      reflexivity.
    Qed.

  End Comp.
End SigComp.

(** ** Putting everything together *)

Module Type SigSpec :=
  Category.Category <+
  Products <+
  Monoidal <+
  Cartesian.

Module Sig <: SigSpec :=
  SigBase <+
  SigTens <+
  SigComp.

(** TODO:
    - composition product / before
    - dual
 *)


(** * Interpretation in [SET] endofunctors *)

Module SigEnd <: FullAndFaithfulFunctor Sig (SET.End).
  Import (notations) Sig.
  Import (coercions) SET.End.

  (** As mentioned above, effect signatures can be interpreted
    as polynomial endofunctors on [SET]. Here we formalize this
    interpretation as an official functor. *)

  Program Definition omap (E : Sig.t) : SET.End.t :=
    {|
      SET.End.oapply := Sig.application E;
      SET.End.fapply X Y f := Sig.amap f;
    |}.
  Next Obligation.
    apply functional_extensionality. intro a.
    apply Sig.amap_id.
  Qed.

  Program Definition fmap {E F} (f : Sig.m E F) : SET.End.m (omap E) (omap F) :=
    {|
      SET.End.comp := Sig.hmap f;
    |}.

  Proposition fmap_id E :
    fmap (Sig.id E) = SET.End.id (omap E).
  Proof.
    apply SET.End.meq. intro X. cbn.
    apply functional_extensionality. intro x.
    apply Sig.hmap_id.
  Qed.

  Proposition fmap_compose {A B C} (g : Sig.m B C) (f : Sig.m A B) :
    fmap (Sig.compose g f) = SET.End.compose (fmap g) (fmap f).
  Proof.
    apply SET.End.meq. intro X. cbn.
    apply functional_extensionality. intro x.
    apply Sig.hmap_compose.
  Qed.

  (** Every natural transformation between endofunctors derived from
    signatures is completely determined by its action on the terms
    [m >= n => n], so the functor is full and faithful. *)

  Proposition full {E F} (η : SET.End.m (omap E) (omap F)) :
    exists f, fmap f = η.
  Proof.
    exists (fun m => η (Sig.ar m) (m >= n => n)).
    apply SET.End.meq. intros X. cbn.
    apply functional_extensionality. intros u.
    destruct u as [m k]. cbn. symmetry.
    apply (SET.natural η k (m >= n => n)).
  Qed.

  Proposition faithful {E F} (f g : Sig.m E F) :
    fmap f = fmap g -> f = g.
  Proof.
    intros H.
    apply functional_extensionality_dep. intros m.
    assert (Hm : fmap f _ (m >= n => n) = fmap g _ (m >= n => n)) by congruence.
    cbn in Hm. unfold Sig.hmap in Hm. cbn in Hm.
    destruct (f m), (g m). assumption.
  Qed.

  (** TODO:
    - preservation of products and coproducts
    - preservation of tensor
   *)

End SigEnd.
