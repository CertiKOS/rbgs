Require Import FunctionalExtensionality.
Require Import List.
Require Import PeanoNat.
Require Import coqrel.LogicalRelations.
Require Import structures.Lattice.
Require Import structures.Effects.
Require Import lattices.FCD.
Require Import models.IntSpec.

Import ISpec.

(** * Effect signatures *)

(** ** Ring buffer *)

(** We will use the global parameters [val] for the type of values,
  and [N] for the capacity of the ring buffer. *)

Parameter val : Type.
Parameter N : nat.

(** The signature for the ring buffer includes operations [set], [get]
  to access the element at a given index, and two counters to keep
  track of the index of the first element ([inc1]) and the index of
  the first free position in the buffer ([inc2]). The [inc1], [inc2]
  primitives both increment the corresponding counter and return their
  previous value. *)

Inductive rb_sig : esig :=
  | set (i : nat) (v : val) : rb_sig unit
  | get (i : nat) : rb_sig val
  | inc1 : rb_sig nat
  | inc2 : rb_sig nat.

(** ** Bounded queue *)

(** We will use the ring buffer data structure to implement a bounded
  queue of size [N]. The corresponding operations are self-explanatory. *)

Inductive bq_sig : esig :=
  | enq (v : val) : bq_sig unit
  | deq : bq_sig val.


(** * Layer implementation *)

(** Code implementing an overlay interface with signature [F] on top
  of an underlay with signature [E] can be represented as a morphism
  [E ~> F]. The following example implements a bounded queue in terms
  a ring buffer. *)

Definition M_bq : rb_sig ~> bq_sig :=
  fun _ m =>
    match m with
      | enq v => i <- ISpec.int inc2; ISpec.int (set i v)
      | deq   => i <- ISpec.int inc1; ISpec.int (get i)
    end.


(** * Layer interfaces *)

(** A layer interface with a signature [E] and abstract states in [S]
  gives for each operation in [E] and start state in [S] an
  interaction-free specification of the possible choices of return
  value and next state. *)

Definition CALspec E S :=
  forall ar, E ar -> S -> ispec 0 (ar * S).

(** To formulate the specifications for the ring buffer layer
  interface, we will use the following helper function. *)

Definition update (f : nat -> val) (i : nat) (v : val) : nat -> val :=
  fun j => if Nat.eq_dec i j then v else f j.

(** Then our layer interfaces can be defined as follows. *)

Definition bq_state : Type :=
  list val.

Definition L_bq : CALspec bq_sig bq_state :=
  fun ar m vs =>
    match m with
      | enq v =>
        _ <- assert (length vs < N);
        ISpec.ret (tt, vs ++ v :: nil)
      | deq =>
        match vs with
          | v::vs' => ISpec.ret (v, vs')
          | nil => bot
        end
    end.

Definition rb_state : Type :=
  (nat -> val) * nat * nat.

Definition L_rb : CALspec rb_sig rb_state :=
  fun ar m '(f, c1, c2) =>
    match m with
      | set i v =>
        _ <- assert (E:=0) (i < N);
        ISpec.ret (tt, (update f i v, c1, c2))

      | get i =>
        _ <- assert (E:=0) (i < N);
        ISpec.ret (f i, (f, c1, c2))

      | inc1 =>
        ISpec.ret (c1, (f, (S c1) mod N, c2))

      | inc2 =>
        ISpec.ret (c2, (f, c1, (S c2) mod N))
    end.


(** * Layer interfaces and implementations as morphisms *)

(** ** Keeping track of state *)

(** To interpret layer interfaces as morphisms in our category of
  effect signatures and substitution specifications, we use the
  following signature which adjoins a state in [S] to the operations
  and arities of the signature [E]. This is written [E@S] in the paper
  but since I plan on using [@] for composition I use [E#S] here. *)

Inductive state_sig (E : Type -> Type) (S : Type) : Type -> Type :=
  | st {ar} (m : E ar) (k : S) : state_sig E S (ar * S).

Arguments st {E S ar} m k.

Infix "#" := state_sig (at level 40, left associativity).

(** A layer interface can then be promoted to a morphism as follows. *)

Coercion CALspec_mor {E S} (L : CALspec E S) : (0 ~> E # S) :=
  fun _ '(st m s) => L _ m s.

(** To connect this with layer implementations, we must lift a
  state-free morphism [M : E ~> F] to a corresponding stateful
  morphism [E#S ~> F#S] which passes the state around unchanged. *)

Fixpoint stateful_play {E S A} (k: S) (s: ISpec.play E A): ispec (E#S) (A*S) :=
  match s with
    | ISpec.pret v => FCD.emb (ISpec.pret (v, k))
    | ISpec.pmove m => FCD.emb (ISpec.pmove (st m k))
    | ISpec.pcons m n t =>
      sup x : option S,
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

(** Then the behavior of [M : E ~> F] running on top of [L : 0 ~> E#S]
  can be computed as follows. *)

Definition layer {E F S} (M : E ~> F) (L : 0 ~> E#S) : 0 ~> F#S :=
  ISpec.compose (slift M) L.

(** ** Properties *)

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

Instance slift_proper_ref {E F S}:
  Proper (ref ==> ref) (@slift E F S).
Proof.
  intros x y Hxy. intros ? mk. destruct mk as [? m k]. cbn.
  unfold srun. rstep. apply Hxy.
Qed.

Lemma slift_identity {E S}:
  slift (S:=S) (identity (E:=E)) = identity.
Proof.
  unfold identity.
  apply antisymmetry; intros ? mk; destruct mk as [? m k];
    cbn; rewrite srun_int; reflexivity.
Qed.

Lemma assert_true {E} {P : Prop} (H : P) :
  @assert E P = ISpec.ret tt.
Proof.
  unfold assert.
  apply antisymmetry.
  - apply sup_lub. reflexivity.
  - apply (sup_at H). reflexivity.
Qed.

(** ** Rewriting tactic *)

Hint Rewrite
  @srun_bind
  @srun_int
  : intm.

Hint Rewrite @assert_true using solve [auto] : intm.

(** ** Example *)

(** The following example shows the effect of running the "deq"
  function as implemented by [M_bq] in terms of the abstract state of
  the underlay [L_rb]. *)

Goal
  forall f,
    srun (f, 2, 5) (ISpec.int deq) / layer M_bq L_rb =
    ISpec.ret (f 2, (f, 3, 5)).
Proof.
  intros f. unfold layer.
  rewrite <- ISpec.apply_assoc. intm.
  rewrite assert_true by admit. intm.
  rewrite Nat.mod_small by admit.
  reflexivity.
Admitted.

(** The next step will be to show that [layer M_bq L_rb] implements
  [L_bq] with a particular simulation relation between the abstract
  states of the overlay and underlay. Stay tuned... *)

(** * Data refinement *)

(** ** Simulation relations as morphisms *)

Definition srel_push {E S1 S2} (R : rel S1 S2) : E#S2 ~> E#S1 :=
  fun _ '(st m k1) =>
    sup {k2 | R k1 k2}, ISpec.int (st m k2) >>= fun '(n, k2') =>
    inf {k1' | R k1' k2'}, ISpec.ret (n, k1').

Definition srel_pull {E S1 S2} (R : rel S1 S2) : E#S1 ~> E#S2 :=
  fun _ '(st m k2) =>
    inf {k1 | R k1 k2}, ISpec.int (st m k1) >>= fun '(n, k1') =>
    sup {k2' | R k1' k2'}, ISpec.ret (n, k2').

Lemma srel_push_pull {E S1 S2} (R : rel S1 S2) (σ : 0 ~> E#S2) (τ : 0 ~> E#S1) :
  srel_push R @ σ [= τ <-> σ [= srel_pull R @ τ.
Proof.
  split.
  - intros H _ [ar m k2]. unfold srel_pull, compose.
    unfold finf. rewrite Upset.Inf.mor. eapply inf_glb. intros [k1 Hk]. intm.
    specialize (H _ (st m k1)). unfold srel_push, compose in H. rewrite <- H.
    unfold fsup. rewrite !Downset.Sup.mor. apply (sup_at (exist _ k2 Hk)). intm.
    destruct (FCD.meet_join_dense (σ _ (st m k2))) as (I & J & c & Hc).
    rewrite Hc. clear.
    rewrite !Upset.Inf.mor. apply inf_glb. intros i. apply (inf_at i).
    rewrite !Downset.Sup.mor. apply sup_lub. intros j. apply (sup_at j).
    destruct (c i j) as [[v k2'] | | ] eqn:Hcij; try tauto.
    setoid_rewrite bind_ret_r.
    unfold finf. rewrite !Upset.Inf.mor. apply inf_glb. intros [k1' Hk']. intm.
    rewrite Downset.Sup.mor. apply (sup_at (exist _ k2' Hk')). intm.
    reflexivity.
  - intros H _ [ar m k1]. unfold srel_push, compose.
    unfold fsup. rewrite Downset.Sup.mor. eapply sup_lub. intros [k2 Hk]. intm.
    specialize (H _ (st m k2)). unfold srel_pull, compose in H. rewrite H.
    unfold finf. rewrite !Upset.Inf.mor. apply (inf_at (exist _ k1 Hk)). intm.
    destruct (FCD.join_meet_dense (τ _ (st m k1))) as (I & J & c & Hc).
    rewrite Hc. clear.
    rewrite !Downset.Sup.mor. apply sup_lub. intros i. apply (sup_at i).
    rewrite !Upset.Inf.mor. apply inf_glb. intros j. apply (inf_at j).
    destruct (c i j) as [[v k1'] | | ] eqn: Hcij; try tauto.
    setoid_rewrite bind_ret_r.
    unfold fsup. rewrite !Downset.Sup.mor. apply sup_lub. intros [k2' Hk']. intm.
    rewrite Upset.Inf.mor. apply (inf_at (exist _ k1' Hk')). intm.
    reflexivity.
Qed.

(** ** Correctness of [M_bq] *)

(** To express the relationship between the ring buffer and the
  corresponding bounded queue, we use the following auxiliary
  functions. [slice] reads a slice of the ring buffer and returns a
  list of elements. *)

Fixpoint slice (f : nat -> val) (i : nat) (n : nat) : list val :=
  match n with
    | O => nil
    | S n' => f i :: slice f (S i mod N) n'
  end.

(** Then we can define the simulation relation as follows. *)

Inductive rb_bq : rb_state -> bq_state -> Prop :=
  bq_rb_intro f c1 c2 n q :
    c1 < N ->
    n <= N ->
    q = slice f c1 n ->
    c2 = (c1 + n) mod N ->
    rb_bq (f, c1, c2) q.

(** This allows us to establish the correctness of [M_bq] as the
  following refinement property. *)

Lemma slice_length f c1 n :
  length (slice f c1 n) = n.
Proof.
  revert c1. induction n; cbn; auto.
Qed.

Lemma assert_l {E A} (P : Prop) (x y : ispec E A) :
  (P -> x [= y) ->
  _ <- assert P; x [= y.
Proof.
  intros H. unfold assert.
  rewrite Downset.Sup.mor. apply sup_lub. intros HP.
  intm. auto.
Qed.

Lemma assert_r {E A} (P : Prop) (x y : ispec E A) :
  x [= y -> P ->
  x [= _ <- assert P; y.
Proof.
  intros Hxy HP.
  rewrite assert_true; intm; auto.
Qed.

Lemma bq_rb_correct :
  L_bq [= srel_pull rb_bq @ slift M_bq @ L_rb.
Proof.
  intros _ [ar m q]. unfold compose, srel_pull, finf. cbn.
  rewrite !Upset.Inf.mor. apply inf_glb. intros [[[f c1] c2] H]. intm.
  inversion H; clear H; subst.
  destruct m; intm.
  - (* enq *)
    apply assert_l. intros HN.
    rewrite assert_true. 2: eapply Nat.mod_upper_bound; admit. intm.
    unfold fsup. rewrite !Downset.Sup.mor. eapply (sup_at (exist _ _ _)). intm.
    reflexivity.
    Unshelve. cbn.
    rewrite slice_length in HN.
    apply bq_rb_intro with (n := S n); auto.
    + revert c1 H3.
      induction n; cbn; intros.
      * rewrite Nat.add_0_r.
        rewrite Nat.mod_small by auto.
        f_equal. unfold update. destruct Nat.eq_dec; congruence.
      * rewrite IHn; auto.
        -- unfold update at 2.
           destruct Nat.eq_dec. admit. cbn. f_equal. f_equal.
           ++ f_equal. rewrite Nat.add_mod_idemp_l by admit. f_equal.
              induction c1; cbn in *; auto.
           ++ f_equal. f_equal. rewrite Nat.add_mod_idemp_l by admit. f_equal.
              induction c1; cbn in *; auto.
        -- apply Le.le_Sn_le; auto.
        -- apply Nat.mod_upper_bound. admit.
    + change (S ?x) with (1 + x).
      rewrite Nat.add_mod_idemp_r by admit. f_equal.
      induction c1; cbn in *; auto.
  - (* deq *)
    destruct n; cbn; auto using bot_lb.
    unfold fsup. rewrite !Downset.Sup.mor.
    eapply (sup_at (exist _ _ _)). intm. reflexivity.
    Unshelve. cbn. apply bq_rb_intro with (n := n); eauto.
    + apply Nat.mod_upper_bound. admit.
    + apply Le.le_Sn_le. auto.
    + rewrite Nat.add_mod_idemp_l by admit. f_equal.
      induction c1; cbn in *; auto.
Admitted.
