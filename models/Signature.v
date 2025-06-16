(** Effect signatures and their homomorphisms. *)

Require Import FunctionalExtensionality.
Require Import Effects.


(** * Signatures *)

(** ** Definition *)

(** A signature is just a set of operations with arities. *)

Record sig :=
  {
    op : Type;
    ar : op -> Type;
  }.

Arguments ar {_} m.

(** ** Dependent type presentation *)

(** Signatures can also be represented as dependent types.
  This is the approach taken in the interaction trees library.
  In that case [E N] is the set of operations of arity [N].

  We prefer to avoid using [esig] as our working version
  and dealing with the associated issues of dependent elimination.
  However this form is very convenient for declaring signatures
  as dependent types, as illustrated by the examples below. *)

Inductive Ebq : esig :=
  | enq : bool -> Ebq unit
  | deq : Ebq bool.

Inductive Erb : esig :=
  | set : nat -> bool -> Erb unit
  | get : nat -> Erb bool
  | inc1 : Erb nat
  | inc2 : Erb nat.

(** Hence we define the following conversion. *)

Record esig_op (E : esig) :=
  {
    esig_ar : Type;
    eop : E esig_ar
  }.

Canonical Structure esig_sig (E : esig) : sig :=
  {|
    op := esig_op E;
    ar := esig_ar E;
  |}.

Coercion esig_sig : esig >-> sig.
Notation "# m" := {| eop := m |} (at level 35, format "# m").


(** * Endofunctors *)

(** Signatures are the same thing as polynomial endofunctors on Set.
  Below I define the endofunctor associated with a given signature. *)

(** ** Simple terms *)

(** For a set of variables [X], we define [E X] to be the set of
  simple terms of the form $m(x_n)_{n \in ar(m)}$. *)

Record application (E : sig) (X : Type) :=
  apply {
    operator : op E;
    operand : ar operator -> X;
  }.

Coercion application : sig >-> Funclass.
Arguments apply {E X}.
Arguments operator {E X}.
Arguments operand {E X}.

(** We will sometimes use the following notation for simple terms,
  which evokes the game/effects interpretation of signatures. *)

Notation "m >= n => x" := {| operator := m; operand n := x |}
  (at level 70, n at next level).

(** [application E] is in fact the endofunctor on [Set] associated with [E].
  The action on functions is defined as follows. *)

Definition amap {E : sig} {X Y} (f : X -> Y) : E X -> E Y :=
  fun '(apply m x) => (m >= n => f (x n)).

Lemma amap_id {E : sig} {X} (t : E X) :
  amap (fun x => x) t = t.
Proof.
  destruct t; reflexivity.
Qed.

Lemma amap_compose {E : sig} {X Y Z} (g : Y -> Z) (f : X -> Y) (t : E X) :
  amap g (amap f t) = amap (fun x => g (f x)) t.
Proof.
  destruct t; reflexivity.
Qed.

(** ** Examples *)

Check #deq >= r => (match r with true => 42 | false => 0%nat end).
Eval cbn in amap (mult 2) (#deq >= r => (match r with true => 42 | false => 0%nat end)).


(** * Homomorphisms *)

(** ** Definition *)

(** A signature homomorphism from [E] to [F] is a simple strategy which
  uses exactly one operation of [F] to interpret each operation of [E]. *)

Definition sighom (E F : sig) :=
  forall (m : op E), F (ar m).

(** It can be used to transform the simple terms of the signature [E]
  into simple terms of the signature [F]. *)

Definition hmap {E F} (ϕ : sighom E F) X : E X -> F X :=
  fun '(apply m x) => amap x (ϕ m).

(** In fact, [application], [amap] and [hmap] together define a
  functor from the category of signatures and signature homomorphisms
  to the category of endofunctors on Set and natural transformations. *)

Lemma hmap_natural {E F} (ϕ : sighom E F) {X Y} (f : X -> Y) (t : E X) :
  amap f (hmap ϕ X t) = hmap ϕ Y (amap f t).
Proof.
  destruct t as [m x]; cbn.
  apply amap_compose.
Qed.

(** Every natural transformation between endofunctors associated to
  signatures is completely determined by its action on the terms
  [m >= n => n], so the functor is full and faithful. *)

Definition basis {E F : sig} (η : forall X, E X -> F X) : sighom E F :=
  fun m => η (ar m) (m >= n => n).

Lemma hmap_basis {E F : sig} (η : forall X, E X -> F X) :
  (forall X Y f t, η Y (amap f t) = amap f (η X t)) ->
  (forall X t, hmap (basis η) X t = η X t).
Proof.
  destruct t as [m x]; cbn. unfold basis.
  rewrite <- H. reflexivity.
Qed.

Lemma basis_hmap {E F : sig} (ϕ : sighom E F) :
  forall m, basis (hmap ϕ) m = ϕ m.
Proof.
  intro. cbn.
  apply amap_id.
Qed.

(** ** Identity *)

Definition sigid {E} : sighom E E :=
  basis (fun X t => t).

Lemma hmap_id {E : sig} :
  forall X t, hmap (@sigid E) X t = t.
Proof.
  apply hmap_basis; auto.
Qed.

(** ** Composition *)

Definition sigcomp {E F G} (ψ : sighom F G) (ϕ : sighom E F) : sighom E G :=
  fun m => hmap ψ _ (ϕ m).

Lemma hmap_compose {E F G} (ψ : sighom F G) (ϕ : sighom E F) :
  forall X t, hmap (sigcomp ψ ϕ) X t = hmap ψ X (hmap ϕ X t).
Proof.
  intros X [m x]; cbn.
  apply hmap_natural.
Qed.

Lemma sigcomp_id_l {E F} (ϕ : sighom E F) :
  sigcomp sigid ϕ = ϕ.
Proof.
  apply functional_extensionality_dep; intros m.
  unfold sigcomp.
  apply hmap_id.
Qed.

Lemma sigcomp_id_r {E F} (ϕ : sighom E F) :
  sigcomp ϕ sigid = ϕ.
Proof.
  apply functional_extensionality_dep; intros m.
  unfold sigcomp; cbn.
  apply amap_id.
Qed.

Lemma sigcomp_assoc {E F G H} (θ: sighom G H) (ψ: sighom F G) (ϕ: sighom E F) :
  sigcomp (sigcomp θ ψ) ϕ = sigcomp θ (sigcomp ψ ϕ).
Proof.
  apply functional_extensionality_dep; intros m.
  unfold sigcomp.
  apply hmap_compose.
Qed.

(** ** Example *)

Definition ex1 : sighom Ebq Erb :=
  fun '#m =>
    match m with
      | enq v => #set 0 v >= _ => tt
      | deq => #inc2 >= n => Nat.eqb n 0
    end.

Definition ex2 : sighom Ebq Ebq :=
  fun '#m =>
    match m with
      | enq v => #deq >= _ => tt
      | deq => #enq true >= _ => false
    end.


(** * Operations on signatures *)

(** ** Sum *)

(** The simplest way to compose signatures is to take the sum of their
  operations. *)

Canonical Structure sigsum (E F : sig) :=
  {|
    op := op E + op F;
    ar m := match m with inl me => ar me | inr mf => ar mf end;
  |}.

Bind Scope sig_scope with sig.
Delimit Scope sig_scope with sig.
Infix "+" := sigsum : sig_scope.

Definition siginl {E F} : sighom E (E + F) :=
  fun m => inl m >= n => n.

Definition siginr {E F} : sighom F (E + F) :=
  fun m => inr m >= n => n.

Definition sigtup {E F G} (ϕ1 : sighom E G) (ϕ2 : sighom F G) : sighom (E + F) G :=
  fun m =>
    match m with
      | inl me => ϕ1 me
      | inr mf => ϕ2 mf
    end.

Lemma sigtup_inl {E F G} (ϕ1 : sighom E G) (ϕ2 : sighom F G) :
  sigcomp (sigtup ϕ1 ϕ2) siginl = ϕ1.
Proof.
  apply functional_extensionality_dep; intros m. cbn.
  apply amap_id.
Qed.

Lemma sigtup_inr {E F G} (ϕ1 : sighom E G) (ϕ2 : sighom F G) :
  sigcomp (sigtup ϕ1 ϕ2) siginr = ϕ2.
Proof.
  apply functional_extensionality_dep; intros m. cbn.
  apply amap_id.
Qed.

Lemma sigtup_uniq {E F G} (ϕ : sighom (E + F) G) :
  sigtup (sigcomp ϕ siginl) (sigcomp ϕ siginr) = ϕ.
Proof.
  apply functional_extensionality_dep; intros [m | m]; cbn;
  apply amap_id.
Qed.

(** ** Tensor *)

Local Open Scope type_scope.

Definition sigtens (E F : sig) : sig :=
  {|
    op := op E * op F;
    ar '(me, mf) := ar me * ar mf;
  |}.

(** ** Composition *)

Canonical Structure sigi : sig :=
  {|
    op := unit;
    ar _ := unit;
  |}.

Canonical Structure sigo (E F : sig) :=
  {|
    op := E (op F);
    ar '(apply m mi) := {n : ar m & ar (mi n)};
  |}.


(** * Embeddings of Set *)

(** ** Covariant embedding *)

Definition discrete (A : Type) : sig :=
  {|
    op := A;
    ar _ := unit;
  |}.

Definition dmor {A B} (f : A -> B) : sighom (discrete A) (discrete B) :=
  fun m => (f m : op (discrete B)) >= tt => tt.

