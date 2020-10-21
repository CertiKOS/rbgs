Require Import ProofIrrelevance.
Require Import FunctionalExtensionality.
Require Import PropExtensionality.
Require Import Relations.
Require Import RelationClasses.
Require Import List.

Unset Program Cases.
Local Obligation Tactic := cbn.


(** * Preliminaries *)

Inductive rcomp {A B C} (R: A-> B-> Prop) (S: B-> C-> Prop) a c: Prop :=
  rcomp_intro (b : B) : R a b -> S b c -> rcomp R S a c.


(** * Coherence spaces *)

(** First we formalize coherence spaces as webs. *)

Record space :=
  {
    token : Type;
    coh: relation token;
    coh_refl: Reflexive coh;
    coh_symm: Symmetric coh;
  }.

Arguments coh {_}.
Existing Instance coh_refl.
Existing Instance coh_symm.
Bind Scope coh_scope with space.
Delimit Scope coh_scope with coh.

(** A point in a coherence space is a set of pairwise coherent tokens. *)

Record clique (A : space) :=
  {
    has : token A -> Prop;
    has_coh a b : has a -> has b -> coh a b;
  }.
    
Arguments has {A}.

(* Points are ordered by inclusion and form a DCPPO. *)

Definition ref {A} : relation (clique A) :=
  fun x y => forall a, has x a -> has y a.

Instance ref_preo A :
  PreOrder (@ref A).
Proof.
  firstorder.
Qed.

Instance ref_po A :
  Antisymmetric (clique A) eq (@ref A).
Proof.
  intros [x Hx] [y Hy] Hxy Hyx. red in Hxy, Hyx. cbn in *.
  assert (x = y).
  {
    apply functional_extensionality. intros a.
    apply propositional_extensionality. split; eauto.
  }
  subst. f_equal.
  apply proof_irrelevance.
Qed.

Program Definition bot A : clique A :=
  {|
    has a := False;
  |}.
Next Obligation.
  contradiction.
Qed.

Lemma bot_ref A :
  forall x, ref (bot A) x.
Proof.
  intros x a [ ].
Qed.

(** Directed supremum *)

Definition directed {A I} (x : I -> clique A) :=
  forall i j, exists y, forall z, ref (x i) z /\ ref (x j) z <-> ref y z.

Program Definition lim {A I} (x : I -> clique A) (Hx : directed x) :=
  {|
    has a := exists i, has (x i) a;
  |}.
Next Obligation.
  intros A I x Hx a b [i Ha] [j Hb].
  specialize (Hx i j) as [y Hy].
  specialize (Hy y) as [_ Hy].
  destruct Hy as [Hyi Hyj]; try reflexivity.
  eapply (has_coh _ y); auto.
Qed.

Lemma lim_sup {A I} (x : I -> clique A) (Hx : directed x) (y : clique A) :
  (forall i, ref (x i) y) <-> ref (lim x Hx) y.
Proof.
  split.
  - intros Hy a [i Ha]. eapply Hy; eauto.
  - intros Hy i a Ha. apply Hy. exists i. auto.
Qed.


(** * Basic categorical structure *)

(** ** Linear maps *)

Record lmap (A B : space) : Type :=
  {
    lmaps :> token A -> token B -> Prop;
    lmaps_coh a1 a2 b1 b2 :
      coh a1 a2 -> lmaps a1 b1 -> lmaps a2 b2 -> coh b1 b2;
    lmaps_det a1 a2 b1 b2 :
      coh a1 a2 -> lmaps a1 b1 -> lmaps a2 b2 -> b1 = b2 -> a1 = a2;
  }.

Arguments lmaps {A B}.
Arguments lmaps_coh {A B}.
Infix "--o" := lmap (at level 55, right associativity) : type_scope.
Delimit Scope lmap_scope with lmap.
Bind Scope lmap_scope with lmap.
Open Scope lmap_scope.

Local Obligation Tactic :=
  cbn; try firstorder (eauto using lmaps_coh, lmaps_det; congruence).

Lemma lmap_ext {A B} (f g : A --o B):
  (forall x y, f x y <-> g x y) -> f = g.
Proof.
  destruct f as [f Hf], g as [g Hg]; cbn. intro H.
  assert (f=g) by auto using functional_extensionality, propositional_extensionality.
  subst; f_equal; apply proof_irrelevance.
Qed.

(** ** Identity and composition *)

Program Definition lmap_id {A : space} : A --o A :=
  {|
    lmaps := eq;
  |}.

Program Definition lmap_compose {A B C : space} (f : B --o C) (g : A --o B) :=
  {|
    lmaps := rcomp (lmaps g) (lmaps f);
  |}.

Infix "@" := lmap_compose (at level 30, right associativity) : lmap_scope.

Lemma lmap_compose_id_left {A B} (f : A --o B) :
  f @ lmap_id = f.
Proof.
  apply lmap_ext; intros x y; cbn.
  split; eauto using rcomp_intro.
  intros [_ [ ] H]. auto.
Qed.

Lemma lmap_compose_id_right {A B} (f : A --o B) :
   lmap_id @ f = f.
Proof.
  apply lmap_ext; intros x y; cbn.
  split; eauto using rcomp_intro.
  intros [? H [ ]]. auto.
Qed.

Lemma lmap_compose_assoc {A B C D}:
  forall (h : C --o D) (g : B --o C) (f : A --o B),
    (h @ g) @ f = h @ (g @ f).
Proof.
  intros. apply lmap_ext; intros; cbn.
  split.
  - intros [b Hxb [c Hbc Hcy]]. eauto using rcomp_intro.
  - intros [c [b Hxb Hbc] Hcy]. eauto using rcomp_intro.
Qed.

(** ** Linear isomorphisms *)

(*
Record liso (A B : space) :=
  {
    liso_of :> A -> B -> Prop;
    liso_coh a1 a2 b1 b2 :
      liso_of a1 b1 ->
      liso_of a2 b2 ->
      (coh a1 a2 <-> coh b1 b2) /\
      (a1 = a2 <-> b1 = b2)
  }.

Arguments liso_of {A B}.
Infix "~=" := liso (at level 70, right associativity) : type_scope.

Program Definition li_fw {A B} (f : A ~= B) :=
  {|
    lmaps := liso_of f;
  |}.
Next Obligation.
  destruct f as [f Hf]; cbn in *.
  destruct (Hf a1 a2 b1 b2) as [? ?]; auto.
  firstorder.
Qed.

Program Definition li_bw {A B} (f : A ~= B) :=
  {|
    lmaps x y := liso_of f y x;
  |}.
Next Obligation.
  destruct f as [f Hf]; cbn in *.
  destruct (Hf b1 b2 a1 a2) as [? ?]; auto.
  firstorder.
Qed.

Lemma li_bw_fw {A B} (f : A ~= B) :
  li_fw f @ li_bw f = lmap_id.
Proof.
  apply lmap_ext; intros x y.
  destruct f as [f Hf]; cbn in *.
  split.
  - intros (b & Hxb & Hby). cbn in *.
    destruct (Hf b b x y); auto. firstorder.
  - intros [ ]. exists x. 
 apply liso_coh.
*)


(** * Simple constructions *)

(** ** Output *)

(** The covariant functor from [Set]. *)

Program Definition output (X : Type) :=
  {|
    token := X;
    coh := eq;
  |}.

Program Definition omap {X Y} (f : X -> Y) : output X --o output Y :=
  {|
    lmaps x y := f x = y;
  |}.

Lemma omap_id X :
  omap (fun x:X => x) = lmap_id.
Proof.
  apply lmap_ext. cbn. tauto.
Qed.

Lemma omap_compose {X Y Z} (f : X -> Y) (g : Y -> Z) :
  omap (fun x:X => g (f x)) = omap g @ omap f.
Proof.
  apply lmap_ext. cbn. split.
  - intros [ ]. exists (f x); auto.
  - intros [_ [ ] [ ]]. auto.
Qed.

(** Here we could prove that the functor preserves products, coproducts, etc. *)

(** ** Input *)

(** The contravariant functor from [Set]. *)

Program Definition input (X : Type) :=
  {|
    token := X;
    coh x1 x2 := True;
  |}.

Program Definition imap {X Y} (f : X -> Y) : input Y --o input X :=
  {|
    lmaps y x := f x = y;
  |}.

Lemma imap_id X :
  imap (fun x:X => x) = lmap_id.
Proof.
  apply lmap_ext. cbn. firstorder.
Qed.

Lemma imap_compose {X Y Z} (f : X -> Y) (g : Y -> Z) :
  imap (fun x:X => g (f x)) = imap f @ imap g.
Proof.
  apply lmap_ext. cbn. split.
  - intros [ ]. eexists; eauto.
  - intros [_ [ ] [ ]]. auto.
Qed.


(** * Cartesian structure *)

(** ** Binary product *)

(** *** Definition *)

Inductive csprod_coh {A B} (RA : relation A) (RB : relation B) : relation (A + B) :=
  | inl_coh x y : RA x y -> csprod_coh RA RB (inl x) (inl y)
  | inr_coh x y : RB x y -> csprod_coh RA RB (inr x) (inr y)
  | inl_inr_coh x y : csprod_coh RA RB (inl x) (inr y)
  | inr_inl_coh x y : csprod_coh RA RB (inr x) (inl y).

Program Definition csprod (A B : space) : space :=
  {|
    token := token A + token B;
    coh := csprod_coh coh coh;
  |}.
Next Obligation.
  intros A B [ | ]; constructor; reflexivity.
Qed.
Next Obligation.
  destruct 1; constructor; symmetry; auto.
Qed.

Infix "&&" := csprod : coh_scope.

Program Definition csp1 {A B : space} : A && B --o A :=
  {|
    lmaps x a := inl a = x;
  |}.
Next Obligation.
  inversion 1; subst; firstorder congruence.
Qed.

Program Definition csp2 {A B : space} : A && B --o B :=
  {|
    lmaps x b := inr b = x;
  |}.
Next Obligation.
  inversion 1; subst; firstorder congruence.
Qed.

Program Definition cspair {X A B : space} (f : X --o A) (g : X --o B) : X --o A && B :=
  {|
    lmaps x y :=
      match y with
        | inl a => lmaps f x a
        | inr b => lmaps g x b
      end;
  |}.
Next Obligation.
  destruct b1, b2; cbn; constructor; eauto using lmaps_coh.
Qed.
Next Obligation.
  destruct b1, b2; cbn; inversion 4; eauto using lmaps_det.
Qed.

Notation "{ x , y }" := (cspair x y) (x at level 99) : lmap_scope.

(** *** Universal property *)

Lemma cspair_csp1 {X A B} (f : X --o A) (g : X --o B) :
  csp1 @ {f, g} = f.
Proof.
  apply lmap_ext; intros x a.
  split.
  - intros [y Hxy Hya]. destruct y; cbn in *; congruence.
  - intros Hxa. exists (inl a); cbn; auto.
Qed.

Lemma cspair_csp2 {X A B} (f : X --o A) (g : X --o B) :
  csp2 @ {f, g} = g.
Proof.
  apply lmap_ext; intros x b.
  split.
  - intros [y Hxy Hyb]. destruct y; cbn in *; congruence.
  - intros Hxb. exists (inr b); cbn; auto.
Qed.

Lemma cspair_uniq {X A B} (h : X --o A && B) :
  {csp1 @ h, csp2 @ h} = h.
Proof.
  apply lmap_ext.
  intros x [a | b]; cbn; split; eauto using rcomp_intro;
  inversion 1; congruence.
Qed.

(** ** Binary coproducts *)

(** *** Definition *)

Inductive cssum_coh {A B} (RA : relation A) (RB : relation B) : relation (A + B) :=
  | sum_inl_coh x y : RA x y -> cssum_coh RA RB (inl x) (inl y)
  | sum_inr_coh x y : RB x y -> cssum_coh RA RB (inr x) (inr y).

Program Definition cssum (A B : space) : space :=
  {|
    token := token A + token B;
    coh := cssum_coh coh coh;
  |}.
Next Obligation.
  intros A B [ | ]; constructor; reflexivity.
Qed.
Next Obligation.
  destruct 1; constructor; symmetry; auto.
Qed.

Infix "+" := cssum : coh_scope.

Program Definition csi1 {A B : space} : A --o A + B :=
  {|
    lmaps a x := inl a = x;
  |}.
Next Obligation.
  intros A B a1 a2 _ _ Ha [ ] [ ].
  constructor; auto.
Qed.

Program Definition csi2 {A B : space} : B --o A + B :=
  {|
    lmaps b x := inr b = x;
  |}.
Next Obligation.
  intros A B a1 a2 _ _ Ha [ ] [ ].
  constructor; auto.
Qed.

Program Definition copair {A B X : space} (f : A --o X) (g : B --o X) : A + B --o X :=
  {|
    lmaps x y :=
      match x with
        | inl a => lmaps f a y
        | inr b => lmaps g b y
      end;
  |}.
Next Obligation.
  intros A B X f g ab1 ab2 x1 x2 H H1 H2.
  destruct H; eauto using lmaps_coh.
Qed.
Next Obligation.
  intros A B X f g ab1 ab2 x1 x2 H H1 H2 Hx.
  destruct H; f_equal; eauto using lmaps_det.
Qed.

Notation "[ x , y ]" := (copair x y) (x at level 99) : lmap_scope.

(** *** Universal property *)

Lemma copair_csi1 {A B X} (f : A --o X) (g : B --o X) :
  [f, g] @ csi1 = f.
Proof.
  apply lmap_ext. cbn. intros a x. split.
  - intros [_ [ ] H]. auto.
  - intros H. exists (inl a); auto.
Qed.

Lemma copair_csi2 {A B X} (f : A --o X) (g : B --o X) :
  [f, g] @ csi2 = g.
Proof.
  apply lmap_ext. cbn. intros b x. split.
  - intros [_ [ ] H]. auto.
  - intros H. exists (inr b); auto.
Qed.

Lemma copair_uniq {A B X} (h : A + B --o X) :
  [h @ csi1, h @ csi2] = h.
Proof.
  apply lmap_ext. intros [a | b] x; cbn; split.
  - intros [_ [ ] H]; auto.
  - eexists; eauto.
  - intros [_ [ ] H]; auto.
  - eexists; eauto.
Qed.

(** ** Terminal object *)

(** *** Definition *)

Program Definition csterm :=
  {|
    token := Empty_set;
    coh x y := True;
  |}.

(** *** Universal property *)

Program Definition discard A : A --o csterm :=
  {|
    lmaps x y := False;
  |}.

Lemma discard_uniq {A} (f : A --o csterm) :
  f = discard A.
Proof.
  apply lmap_ext. contradiction.
Qed.


(** * Tensor product *)

(** ** Definition *)

Program Definition cstens (A B : space) : space :=
  {|
    token := token A * token B;
    coh '(a1, b1) '(a2, b2) := coh a1 a2 /\ coh b1 b2;
  |}.
Next Obligation.
  intros A B [a b]. split; reflexivity.
Qed.
Next Obligation.
  intros A B [a1 b1] [a2 b2] [Ha Hb]. split; symmetry; auto.
Qed.

Infix "*" := cstens : coh_scope.

(** ** Functoriality *)

Program Definition cstens_lmap {A B C D} (f : A --o B) (g : C --o D) : A*C --o B*D :=
  {|
    lmaps '(a, c) '(b, d) := f a b /\ g c d;
  |}.
Next Obligation.
  intros A B C D f g [a1 c1] [a2 c2] [b1 d1] [b2 d2] [Ha Hc] [Hab1 Hcd1] [Hab2 Hcd2].
  cbn; eauto using lmaps_coh.
Qed.
Next Obligation.
  intros A B C D f g [a1 c1] [a2 c2] [b1 d1] [b2 d2] [Ha Hc] [Hab1 Hcd1] [Hab2 Hcd2].
  inversion 1; f_equal; eauto using lmaps_det.
Qed.

Infix "*" := cstens_lmap : lmap_scope.

Lemma cstens_id {A B} :
  (@lmap_id A) * (@lmap_id B) = lmap_id.
Proof.
  apply lmap_ext.
  intros [a1 b1] [a2 b2]. cbn.
  split; inversion 1; cbn in *; subst; auto.
Qed.

Lemma cstens_compose {A1 B1 C1} {A2 B2 C2} :
  forall (f1 : A1 --o B1) (g1 : B1 --o C1) (f2 : A2 --o B2) (g2 : B2 --o C2),
    (g1 @ f1) * (g2 @ f2) = (g1 * g2) @ (f1 * f2).
Proof.
  intros. apply lmap_ext. intros [a1 a2] [c1 c2]. cbn.
  split.
  - intros [[? ? ?] [? ? ?]]. eexists (_, _); eauto.
  - intros [[? ?] [? ?] [? ?]]. eauto using rcomp_intro.
Qed.

(** ** Unit *)

Program Definition csunit : space :=
  {|
    token := unit;
    coh x y := True;
  |}.

Notation "1" := csunit : coh_scope.

(*
(** Left unitor *)

Program Definition lam A : 1 * A --o A :=
  {|
Next Obligation.
  destruct H; auto.
Qed.

(** Right unitor *)

Program Definition rho A : A * 1 --o A :=
  {|
    lmap_apply a := (a, tt);
  |}.
Next Obligation.
  destruct H; auto.
Qed.
*)

(* etc.. *)

(** ** Negation *)

(** To avoid confusion between the [coh] relation associated with [A]
  and [lneg A], we introduce this singleton type. *)

Variant lneg_token A :=
  | ln (a : token A).

Arguments ln {A}.

Variant lneg_coh (A : space) : relation (lneg_token A) :=
  lneg_coh_intro x y :
    (coh x y -> x = y) -> lneg_coh A (ln x) (ln y).

Program Definition lneg (A : space) : space :=
  {|
    token := lneg_token A;
    coh := lneg_coh A;
  |}.
Next Obligation.
  intros A [x]. constructor. reflexivity.
Qed.
Next Obligation.
  intros A _ _ [x y Hxy]. constructor.
  intros. symmetry. apply Hxy. symmetry. auto.
Qed.

Program Definition lmap_flip {A B} (f : A --o B) : lneg B --o lneg A :=
  {|
    lmaps '(ln x) '(ln y) := f y x;
  |}.
Next Obligation.
  intros A B f _ _ [b1] [b2] [a1 a2 Ha12] Hba1 Hba2. constructor. intro.
  eauto using lmaps_coh, lmaps_det.
Qed.
Next Obligation.
  intros A B f _ _ [b1] [b2] [a1 a2 Ha12] Hba1 Hba2.
  inversion 1; clear H; subst.
  f_equal; eauto using lmaps_coh, lmaps_det, (reflexivity (R := coh)).
Qed.


(** * Sequential constructions *)

(** ** Composition *)

Program Definition seq (A B : space) : space :=
  {|
    token := token A * token B;
    coh '(a1, b1) '(a2, b2) := coh a1 a2 /\ (a1 = a2 -> coh b1 b2);
  |}.
Next Obligation.
  intros A B [a b].
  split; reflexivity.
Qed.
Next Obligation.
  intros A B [a1 b1] [a2 b2] [Ha Hb].
  split; symmetry; auto.
Qed.

Infix ";;" := seq (at level 40, left associativity) : coh_scope.

Program Definition seq_lmap {A B C D} (f g : _ --o _) : (A ;; C) --o (B ;; D) :=
  {|
    lmaps '(a, c) '(b, d) := f a b /\ g c d;
  |}.
Next Obligation.
  intros A B C D f g [a1 c1] [a2 c2] [b1 d1] [b2 d2]. cbn.
  intros [Ha Hc] [Hab1 Hab2] [Hcd1 Hcd2].
  split; eauto 10 using lmaps_coh, lmaps_det.
Qed.
Next Obligation.
  intros A B C D f g [a1 c1] [a2 c2] [b1 d1] [b2 d2]. cbn.
  intros [Ha Hc] [Hab1 Hab2] [Hcd1 Hcd2]. inversion 1; clear H.
  f_equal; eauto using lmaps_coh, lmaps_det.
Qed.

Infix ";;" := seq_lmap : lmap_scope.

(** ** Exponential *)

Inductive list_coh (A : space) : relation (list (token A)) :=
  | nil_coh_l s :
      list_coh A nil s
  | nil_coh_r s :
      list_coh A s nil
  | cons_coh a b x y :
      coh a b ->
      (a = b -> list_coh A x y) ->
      list_coh A (a :: x) (b :: y).

Program Definition dag (A : space) : space :=
  {|
    token := list (token A);
    coh := list_coh A;
  |}.
Next Obligation.
  intros A l.
  induction l; constructor; auto.
  reflexivity.
Qed.
Next Obligation.
  intros A s t Hst.
  induction Hst; constructor; auto.
  symmetry; auto.
Qed.

Notation "! A" := (dag A) (at level 8, right associativity, format "'!' A") : coh_scope.

(** *** Comonad structure *)

Lemma prefix_coh {A} s1 s2 t1 t2 :
  list_coh A (s1 ++ t1) (s2 ++ t2) ->
  list_coh A s1 s2.
Proof.
  intros H.
  remember (s1 ++ t1) as v1 eqn:Hv1.
  remember (s2 ++ t2) as v2 eqn:Hv2.
  revert s1 s2 t1 t2 Hv1 Hv2.
  induction H; intros.
  - destruct s1; inversion Hv1. constructor.
  - destruct s2; inversion Hv2. constructor.
  - destruct s1; inversion Hv1; clear Hv1; subst;
    destruct s2; inversion Hv2; clear Hv2; subst;
      constructor; auto.
    destruct 1; eauto.
Qed.

Lemma suffix_coh {A} s t1 t2 :
  list_coh A (s ++ t1) (s ++ t2) ->
  list_coh A t1 t2.
Proof.
  induction s; auto. cbn.
  inversion 1; clear H; subst.
  auto.
Qed.

Lemma app_coh {A} s t1 t2 :
  list_coh A t1 t2 ->
  list_coh A (s ++ t1) (s ++ t2).
Proof.
  intros Ht.
  induction s; auto.
  cbn. constructor.
  - reflexivity.
  - auto.
Qed.

(** Action on linear maps *)

Inductive dag_lmaps {A B} (f : A --o B) : token !A -> token !B -> Prop :=
  | dag_lmaps_nil :
      dag_lmaps f nil nil
  | dag_lmaps_cons a b aa bb :
      lmaps f a b ->
      dag_lmaps f aa bb ->
      dag_lmaps f (a :: aa) (b :: bb).

Program Definition dag_lmap {A B} (f : A --o B) : !A --o !B :=
  {|
    lmaps := dag_lmaps f;
  |}.
Next Obligation.
  intros A B f aa1 aa2 bb1 bb2 Hxx H1 H2.
  revert bb1 bb2 H1 H2.
  induction Hxx.
  - inversion 1. constructor.
  - inversion 2. constructor.
  - intros.
    inversion H2; clear H2; subst.
    inversion H3; clear H3; subst.
    constructor; eauto using lmaps_coh.
    intros. apply H1; eauto. eapply lmaps_det; eauto.
Qed.
Next Obligation.
  intros A B f aa1 aa2 bb1 bb2 Hxx H1 H2.
  revert bb1 bb2 H1 H2.
  induction Hxx.
  - intros.
    inversion H1; clear H1; subst.
    inversion H2; clear H2; subst.
    auto.
  - intros.
    inversion H2; clear H2; subst.
    inversion H1; clear H1; subst.
    auto.
  - intros.
    inversion H2; clear H2; subst.
    inversion H3; clear H3; subst.
    f_equal; eauto using lmaps_det.
Qed.

Notation "! f" := (dag_lmap f) (at level 8, right associativity, format "'!' f") : lmap_scope.

Lemma dag_id {A} :
  !(@lmap_id A) = @lmap_id !A.
Proof.
  apply lmap_ext. split.
  - induction 1. constructor.
    cbn in *. congruence.
  - intros [ ].
    induction x; constructor; cbn; auto.
Qed.

Lemma dag_compose {A B C} (f : A --o B) (g : B --o C) :
  !(g @ f) = !g @ !f.
Proof.
  apply lmap_ext. split.
  - induction 1.
    + exists nil; constructor.
    + destruct H, IHdag_lmaps.
      eexists; constructor; eauto.
  - intros [u Hxu Huy]. revert y Huy.
    induction Hxu.
    + inversion 1. constructor.
    + inversion 1; subst.
      constructor; auto.
      * eexists; eauto.
      * eapply IHHxu; eauto.
Qed.

(** Counit *)

Inductive dag_counit_lmaps A : token !A -> token A -> Prop :=
  dag_counit_intro a : dag_counit_lmaps A (a :: nil) a.

Program Definition dag_counit A : !A --o A :=
  {|
    lmaps := dag_counit_lmaps A;
  |}.
Next Obligation.
  intros A x1 x2 a1 a2 Hx Hx1 Hx2.
  destruct Hx1, Hx2. inversion Hx; auto.
Qed.
Next Obligation.
  intros A x1 x2 a1 a2 Hx Hx1 Hx2 H.
  destruct Hx1, Hx2; congruence.
Qed.

Lemma dag_counit_natural {A B} (f : A --o B) :
   f @ dag_counit A = dag_counit B @ !f.
Proof.
  apply lmap_ext. split.
  - intros [a Ha1 Ha2].
    inversion Ha1. subst.
    eexists; repeat constructor; eauto.
  - intros [a Ha1 Ha2].
    inversion Ha2. subst.
    inversion Ha1 as [ | ? ? ? ? ? H]. subst.
    inversion H. subst.
    eexists; eauto; constructor.
Qed.

(** Comultiplication *)

Inductive dag_comult_lmaps {A} : token !A -> token !!A -> Prop :=
  | dag_comult_nil :
      dag_comult_lmaps nil nil
  | dag_comult_cons s a aa :
      dag_comult_lmaps a aa ->
      dag_comult_lmaps (s ++ a) (s :: aa).

Program Definition dag_comult A : !A --o !!A :=
  {|
    lmaps := dag_comult_lmaps;
  |}.
Next Obligation.
  intros A a1 a2 aa1 aa2 Ha H1 H2.
  revert a2 aa2 Ha H2.
  induction H1 as [ | s1 a1 aa1 H1].
  - constructor.
  - intros a2 aa2 Ha H2.
    induction H2 as [ | s2 a2 aa2 H2].
    + constructor.
    + constructor.
      * eapply prefix_coh; eauto.
      * destruct 1.
        eapply IHH1; eauto.
        eapply suffix_coh; eauto.
Qed.
Next Obligation.
  intros A a1 a2 aa1 aa2 Ha H1 H2.
  revert a2 aa2 Ha H2.
  induction H1 as [ | s1 a1 aa1 H1].
  - intros. subst. inversion H2. auto.
  - intros a2 aa2 Ha H2.
    induction H2 as [ | s2 a2 aa2 H2].
    + discriminate.
    + inversion 1; subst. f_equal.
      eapply IHH1; eauto.
      eapply suffix_coh; eauto.
Qed.

Lemma dag_lmaps_app {A B} (f : A --o B) a1 a2 b1 b2:
  !f a1 b1 -> !f a2 b2 -> !f (a1 ++ a2) (b1 ++ b2).
Proof.
  induction 1.
  - intuition.
  - intros Hx.
    apply IHdag_lmaps in Hx.
    repeat rewrite <- app_comm_cons.
    constructor; assumption.
Qed.

Lemma dag_lmaps_app_inv {A B} (f : A --o B) a b1 b2:
  !f a (b1 ++ b2) -> exists a1 a2, a = a1 ++ a2 /\ !f a1 b1 /\ !f a2 b2.
Proof.
  revert a b2. induction b1 as [ | b1x b1xs].
  - intros a ? ?.
    exists nil. exists a.
    split. reflexivity.
    split. constructor.
    exact H.
  - intros a ? Ha.
    rewrite <- app_comm_cons in Ha.
    inversion Ha as [ | xa ? ? ? ? Hxa]. subst.
    apply IHb1xs in Hxa as [xa1 [xa2 [app_eq [Hxa1 Hxa2]]]].
    exists (xa::xa1). exists xa2.
    split. subst. apply app_comm_cons.
    split; try constructor; assumption.
Qed.

Lemma dag_comult_natural {A B} (f : A --o B) :
  !!f @ dag_comult A = dag_comult B @ !f. 
Proof.
  apply lmap_ext. split.
  - intros [a Ha1 Ha2].
    revert y Ha2. induction Ha1 as [ | s a aa Ha IHaa].
    + inversion 1. eexists; constructor.
    + inversion 1 as [ | ? b ? ys Hy Hys]. subst.
      eapply IHaa in Hys as [bs Hb1 Hb2].
      inversion Ha2. subst.
      exists (b ++ bs). apply dag_lmaps_app; assumption.
      constructor. assumption.
  - intros [b Hb1 Hb2].
    revert x Hb1. induction Hb2 as [ | s b bb Hb IHbb].
    + inversion 1. eexists; constructor.
    + intros x Hx.
      apply dag_lmaps_app_inv in Hx as [a1 [a2 [? [Ha1 Ha2]]]].
      subst x. apply IHbb in Ha2 as [xa ? ?].
      exists (a1 :: xa). constructor. assumption.
      constructor; assumption.
Qed.

(** Properties *)

Lemma dag_comult_counit {A} :
  !(dag_counit A) @ (dag_comult A) = @lmap_id !A.
Proof.
  apply lmap_ext. split.
  - cbn. intros [a Ha1 Ha2].
    revert y Ha2. induction Ha1.
    + inversion 1. reflexivity.
    + inversion 1 as [ | ? ? ? ? Hsb Hab]. subst.
      apply IHHa1 in Hab.
      inversion Hsb. subst. reflexivity.
  - cbn. intros <-.
    exists (map (fun x => x::nil) x).
    + induction x.
      * constructor.
      * replace (a :: x) with ((a :: nil) ++ x) by reflexivity.
        constructor. assumption.
    + induction x; cbn; constructor.
      constructor. assumption.
Qed.

Lemma dag_counit_comult {A} :
  (dag_counit !A) @ (dag_comult A) = @lmap_id !A.
Proof.
  apply lmap_ext. split.
  - cbn. intros [a Ha1 Ha2].
    inversion Ha2. subst.
    inversion Ha1 as [ | ? ? ? H]. subst.
    inversion H. apply app_nil_r.
  - cbn. intros <-.
    exists (x::nil).
    replace x with (x ++ nil) at 1 by apply app_nil_r; repeat constructor.
    constructor.
Qed.

Lemma dag_comult_app {A} x y xs ys:
  (dag_comult A) x xs ->
  (dag_comult A) y ys ->
  (dag_comult A) (x ++ y) (xs ++ ys).
Proof.
  revert y ys.
  induction 1 as [ | s a aa H IH].
  - trivial.
  - intros Hy.
    apply IH in Hy.
    replace ((s++a)++y) with (s++(a++y)) by apply app_assoc.
    rewrite <- app_comm_cons.
    constructor. assumption.
Qed.

Lemma dag_comult_app_inv {A} a xs ys:
  (dag_comult A) a (xs ++ ys) ->
  exists x y, a = x ++ y /\ (dag_comult A) x xs /\ (dag_comult A) y ys.
Proof.
  revert a ys.
  induction xs as [| x ? IHxs].
  - intros a ys Hys.
    exists nil. exists a.
    split. reflexivity.
    split. constructor.
    apply Hys.
  - intros a ys Hys.
    rewrite <- app_comm_cons in Hys.
    inversion Hys as [ | a1 a2 aa Haa]. subst.
    apply IHxs in Haa as [xxs [yys [app_eq [x_comult y_comult]]]].
    exists (x ++ xxs).
    exists yys.
    split. subst. apply app_assoc.
    split; try constructor; assumption.
Qed.

Lemma dag_comult_comult {A} :
  !(dag_comult A) @ (dag_comult A) = (dag_comult !A) @ (dag_comult A).
Proof.
  apply lmap_ext. split.
  - cbn. intros [aa Haa1 Haa2].
    revert y Haa2.
    induction Haa1 as [ | s a aa ? IH].
    + inversion 1. eexists; constructor.
    + intros y Hsaa.
      inversion Hsaa as [ | ? b ? bb Hb Hbb]. subst.
      apply IH in Hbb as [xaa Hxaa1 Hxaa2].
      exists (b++xaa).
      apply dag_comult_app; assumption.
      constructor. assumption.
  - cbn. intros [aa Haa1 Haa2].
    revert x Haa1.
    induction Haa2 as [ | s a aa ? IH].
    + inversion 1. eexists; constructor.
    + intros xa Hxa.
      apply dag_comult_app_inv in Hxa as [xa1 [xa2 [app_eq [xa1_comult xa2_comult]]]].
      apply IH in xa2_comult as [b Hb1 Hb2].
      exists (xa1::b); subst; constructor; assumption.
Qed.

(** Kleisli extension *)

Definition dag_ext {A B} (f : !A --o B) : !A --o !B :=
  dag_lmap f @ dag_comult A.

Lemma dag_ext_counit A :
  dag_ext (dag_counit A) = @lmap_id !A.
Proof.
  unfold dag_ext.
  apply dag_comult_counit.
Qed.

Lemma dag_counit_ext {A B} (f : !A --o B) :
  dag_counit B @ dag_ext f = f.
Proof.
  unfold dag_ext.
  rewrite <- lmap_compose_assoc.
  rewrite <- dag_counit_natural.
  rewrite lmap_compose_assoc.
  rewrite dag_counit_comult.
  rewrite lmap_compose_id_left.
  reflexivity.
Qed.

Lemma dag_ext_compose {A B C} (f : !A --o B) (g : !B --o C) :
  dag_ext (g @ dag_ext f) = dag_ext g @ dag_ext f.
Proof.
  unfold dag_ext.
  rewrite !lmap_compose_assoc.
  rewrite <- (lmap_compose_assoc (dag_comult B)).
  rewrite <- dag_comult_natural.
  rewrite !dag_compose, !lmap_compose_assoc.
  rewrite dag_comult_comult.
  reflexivity.
Qed.
