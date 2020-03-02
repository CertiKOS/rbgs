Require Import coqrel.LogicalRelations.
Require Import FunctionalExtensionality.
Require Import List.
Require Import PeanoNat.
Require Import Lattice.
Require Import FCD.
Require Import Effects.
Require Import IntSpec.

Import ISpec.


(** * Preliminaries *)

Infix "~>" := ISpec.subst (at level 99).

Notation "v <- x ; M" := (ISpec.bind (fun v => M) x)
  (at level 65, right associativity).

Definition assert {E : esig} (P : Prop) : ispec E unit :=
  ⋁ H : P; ISpec.ret tt.


(** * Effect signatures *)

(** Ring buffer *)

Parameter val : Type.  (* type of values *)
Parameter N : nat.     (* capacity *)

Inductive rb_sig : esig :=
  | set (i : nat) (v : val) : rb_sig unit
  | get (i : nat) : rb_sig val
  | inc1 : rb_sig nat
  | inc2 : rb_sig nat.

(** Bounded queue *)

Inductive bq_sig : esig :=
  | enq (v : val) : bq_sig unit
  | deq : bq_sig val.

(** Empty signature *)

Inductive empty_sig : esig := .

Notation "1" := empty_sig.


(** * Example program (or interpretation thereof) *)

Definition M_bq : rb_sig ~> bq_sig :=
  fun _ m =>
    match m with
      | enq v => i <- ISpec.int inc2; ISpec.int (set i v)
      | deq   => i <- ISpec.int inc1; ISpec.int (get i)
    end.


(** * Layer interfaces *)

Definition CALspec E S :=
  forall ar, E ar -> S -> ispec 1 (ar * S).

Definition update (f : nat -> val) (i : nat) (v : val) :=
  fun j => if Nat.eq_dec i j then v else f j.

Definition L_bq : CALspec bq_sig (list val) :=
  fun ar m vs =>
    match m with
      | enq v => ISpec.ret (tt, v::vs)
      | deq =>
        match vs with
          | v::vs' => ISpec.ret (v, vs')
          | nil => bot
        end
    end.

Definition L_rb : CALspec rb_sig ((nat -> val) * nat * nat) :=
  fun ar m '(f, c1, c2) =>
    match m with
      | set i v =>
        _ <- assert (E:=1) (i < N);
        ISpec.ret (tt, (update f i v, c1, c2))

      | get i =>
        _ <- assert (E:=1) (i < N);
        ISpec.ret (f i, (f, c1, c2))

      | inc1 =>
        ISpec.ret (c1, (f, (S c1) mod N, c2))

      | inc2 =>
        ISpec.ret (c2, (f, c1, (S c2) mod N))
    end.


(** * Interpretation of layer interfaces *)

Inductive state_sig (E : Type -> Type) (S : Type) : Type -> Type :=
  | st {ar} (m : E ar) (k : S) : state_sig E S (ar * S).

Arguments st {E S ar} m k.
Infix "#" := state_sig (at level 40, left associativity).

Coercion CALspec_mor {E S} (L : CALspec E S) : (1 ~> E # S) :=
  fun _ '(st m s) => L _ m s.

Fixpoint stateful_play {E S A} (k: S) (s: ISpec.play E A): ispec (E#S) (A*S) :=
  match s with
    | ISpec.pret v => FCD.emb (ISpec.pret (v, k))
    | ISpec.pmove m => FCD.emb (ISpec.pmove (st m k))
    | ISpec.pcons m n t =>
      ⋁ x : option S;
      match x with
      | Some k' => FCD.map (ISpec.pcons (st m k) (n, k')) (stateful_play k' t)
      | None => FCD.emb (ISpec.pmove (st m k))
      end
  end.

Instance stateful_play_mor E S A k :
  PosetMorphism (@stateful_play E S A k).
Proof.
  constructor. intros s t Hst. revert k.
  induction Hst; cbn; intro.
  - reflexivity.
  - reflexivity.
  - apply (sup_at None).
    reflexivity.
  - apply sup_lub. intro x. apply (sup_at x). repeat rstep.
    unfold FCD.map. repeat rstep. auto.
Qed.

Definition srun {E S A} (k : S) (x : ispec E A) : ispec (E # S) (prod A S) :=
  FCD.ext (stateful_play k) x.

Definition slift {E F S} (σ : E ~> F) : E#S ~> F#S :=
  fun ar m =>
    match m with st m k => srun k (σ _ m) end.

Notation "x / f" := (ISpec.apply f x).
Infix "@" := ISpec.compose (at level 40, left associativity).


Definition layer {E F S} (M : E ~> F) (L : 1 ~> E#S) : 1 ~> F#S :=
  ISpec.compose (slift M) L.


Lemma srun_slift {E F S A} (k : S) (x : ispec F A) (σ : E ~> F) :
  srun k x / slift σ = srun k (x / σ).
Proof.
  unfold srun, ISpec.apply.
  rewrite !@FCD.ext_ext by typeclasses eauto. f_equal.
  apply functional_extensionality. intros s.
  induction s; cbn.
  - rewrite !FCD.ext_ana. cbn.
    reflexivity.
  - rewrite !FCD.ext_ana. cbn.
    unfold srun, ISpec.bind.
    rewrite !@FCD.ext_ext by typeclasses eauto. f_equal.
    apply functional_extensionality. intros s.
    induction s; cbn.
    + rewrite FCD.ext_ana. cbn.
      admit. (* rewrite Downset.Sup.mor_bot *)
    + rewrite !FCD.ext_ana. cbn. reflexivity.
    + rewrite Downset.Sup.mor.
      rewrite Downset.Sup.mor_join.
      apply antisymmetry.
      * apply sup_lub. intros [k' | ].
        -- apply join_r. unfold FCD.map.
           rewrite !@FCD.ext_ext; try typeclasses eauto.
           ++ repeat setoid_rewrite FCD.ext_ana. cbn.
Admitted.

Lemma srun_bind {E S A B} (k : S) (f : A -> ispec E B) (x : ispec E A) :
  srun k (ISpec.bind f x) = ISpec.bind (fun '(a, k') => srun k' (f a)) (srun k x).
Admitted.

Lemma srun_int {E S ar} (k : S) (m : E ar) :
  srun k (ISpec.int m) = ISpec.int (st m k).
Admitted.

Lemma apply_bind {E F A B} (f : A -> ispec F B) (x : ispec F A) (σ : E ~> F) :
  ISpec.bind f x / σ = a <- (x / σ); (f a / σ).
Admitted.
  
Lemma apply_int {E F ar} (m : F ar) (σ : E ~> F) :
  ISpec.int m / σ = σ ar m.
Admitted.

Lemma assert_true {E} {P : Prop} (H : P) :
  @assert E P = ISpec.ret tt.
Proof.
  unfold assert.
  apply antisymmetry.
  - apply sup_lub. reflexivity.
  - apply (sup_at H). reflexivity.
Qed.

Goal
  forall f,
    srun (f, 2, 5) (ISpec.int deq) / layer M_bq L_rb =
    ISpec.ret (f 2, (f, 3, 5)).
Proof.
  intros f. unfold layer.
  rewrite <- ISpec.apply_assoc.
  rewrite srun_slift.
  rewrite ISpec.apply_int_r. cbn.
  rewrite srun_bind.
  rewrite srun_int.
  rewrite apply_bind.
  rewrite apply_int. cbn.
  rewrite ISpec.bind_ret_r.
  rewrite srun_int.
  rewrite apply_int. cbn.
  rewrite assert_true by admit.
  rewrite ISpec.bind_ret_r.
  rewrite Nat.mod_small by admit.
  reflexivity.
Admitted.
