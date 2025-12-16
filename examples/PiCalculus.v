(** A minimal formalization of the π-calculus using the existing
    infrastructure.  We keep to a lightweight labelled transition
    semantics and package it so it can be reused as an LTS. *)

Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Operators.

Module Pi.

  (** * Names and actions *)

  Definition name := nat.

  Inductive action :=
  | tau
  | in_act (c : name) (v : name)
  | out_act (c : name) (v : name).

  Definition action_uses (x : name) (a : action) : bool :=
    match a with
    | tau => false
    | in_act c v => (x =? c) || (x =? v)
    | out_act c v => (x =? c) || (x =? v)
    end.

  (** * Syntax *)

  Inductive proc :=
  | zero
  | tau_prefix (p : proc)
  | send (c v : name) (p : proc)
  | recv (c x : name) (p : proc)          (* input binds [x] in [p] *)
  | par (p q : proc)
  | choice (p q : proc)
  | nu (x : name) (p : proc)              (* restriction of [x] in [p] *)
  | rep (p : proc).

  (** Capture-avoiding substitution of channel [x] by [y]. *)
  Fixpoint subst (x y : name) (p : proc) : proc :=
    match p with
    | zero => zero
    | tau_prefix p1 => tau_prefix (subst x y p1)
    | send c v p1 =>
        send (if c =? x then y else c) (if v =? x then y else v) (subst x y p1)
    | recv c x' p1 =>
        let c' := if c =? x then y else c in
        if x' =? x then recv c' x' p1 else recv c' x' (subst x y p1)
    | par p1 p2 => par (subst x y p1) (subst x y p2)
    | choice p1 p2 => choice (subst x y p1) (subst x y p2)
    | nu x' p1 => if x' =? x then nu x' p1 else nu x' (subst x y p1)
    | rep p1 => rep (subst x y p1)
    end.

  (** Free-name test used for α-conversion side-conditions. *)
  Fixpoint occurs (x : name) (p : proc) : bool :=
    match p with
    | zero => false
    | tau_prefix p1 => occurs x p1
    | send c v p1 => (x =? c) || (x =? v) || occurs x p1
    | recv c x' p1 => (x =? c) || if x' =? x then false else occurs x p1
    | par p1 p2 => occurs x p1 || occurs x p2
    | choice p1 p2 => occurs x p1 || occurs x p2
    | nu x' p1 => if x' =? x then false else occurs x p1
    | rep p1 => occurs x p1
    end.

  (** * Structural congruence *)

  Inductive cong : proc -> proc -> Prop :=
  | cong_refl p : cong p p
  | cong_sym p q : cong p q -> cong q p
  | cong_trans p q r : cong p q -> cong q r -> cong p r
  | cong_par_comm p q : cong (par p q) (par q p)
  | cong_par_assoc p q r : cong (par (par p q) r) (par p (par q r))
  | cong_par_zero p : cong (par p zero) p
  | cong_choice_comm p q : cong (choice p q) (choice q p)
  | cong_choice_assoc p q r : cong (choice (choice p q) r) (choice p (choice q r))
  | cong_choice_zero p : cong (choice p zero) p
  | cong_nu_alpha x y p :
      x <> y ->
      occurs y p = false ->
      cong (nu x p) (nu y (subst x y p))
  | cong_rep_unfold p : cong (rep p) (par p (rep p)).

  #[export] Instance cong_equiv : Equivalence cong.
  Proof.
    constructor.
    - intro p. apply cong_refl.
    - intros x y Hxy. apply cong_sym. exact Hxy.
    - intros x y z Hxy Hyz. eapply cong_trans; eauto.
  Qed.

  (** * One-step transitions *)

  Inductive step : action -> proc -> proc -> Prop :=
  | step_tau p :
      step tau (tau_prefix p) p
  | step_out c v p :
      step (out_act c v) (send c v p) p
  | step_in c x p v :
      step (in_act c v) (recv c x p) (subst x v p)
  | step_choice_l a p p' q :
      step a p p' ->
      step a (choice p q) (choice p' q)
  | step_choice_r a p q q' :
      step a q q' ->
      step a (choice p q) (choice p q')
  | step_par_l a p p' q :
      step a p p' ->
      step a (par p q) (par p' q)
  | step_par_r a p q q' :
      step a q q' ->
      step a (par p q) (par p q')
  | step_comm c v p p' q q' :
      step (out_act c v) p p' ->
      step (in_act c v) q q' ->
      step tau (par p q) (par p' q')
  | step_nu a x p p' :
      step a p p' ->
      action_uses x a = false ->
      step a (nu x p) (nu x p')
  | step_rep a p p' :
      step a (par p (rep p)) p' ->
      step a (rep p) p'.

  Definition transition (a : action) (p q : proc) : Prop :=
    exists p1 p2, cong p p1 /\ step a p1 p2 /\ cong p2 q.

  Notation "p -[ a ]-> q" := (transition a p q) (at level 40).

  Lemma step_transition a p q :
    step a p q -> p -[ a ]-> q.
  Proof.
    intro Hs. exists p, q. split; [apply cong_refl|].
    split; auto. apply cong_refl.
  Qed.

  (** * Observable semantics: strong and weak bisimulations *)

  Definition is_tau (a : action) : bool :=
    match a with tau => true | _ => false end.

  Inductive tau_star : proc -> proc -> Prop :=
  | tau_refl p : tau_star p p
  | tau_step p q r :
      p -[ tau ]-> q ->
      tau_star q r ->
      tau_star p r.

  Inductive weak_step (a : action) : proc -> proc -> Prop :=
  | weak_step_silent p q :
      tau_star p q ->
      is_tau a = true ->
      weak_step a p q
  | weak_step_obs p p1 p2 q :
      tau_star p p1 ->
      is_tau a = false ->
      p1 -[ a ]-> p2 ->
      tau_star p2 q ->
      weak_step a p q.

  Notation "p ==[ a ]=> q" := (weak_step a p q) (at level 40).

  Lemma tau_star_trans p q r :
    tau_star p q -> tau_star q r -> tau_star p r.
  Proof.
    intros H1 H2. induction H1; eauto using tau_star.
  Qed.

  Lemma weak_step_tau_closure p q :
    tau_star p q -> weak_step tau p q.
  Proof.
    intro Htau. constructor; [exact Htau|reflexivity].
  Qed.

  Module Notations.
    Notation "p || q" := (par p q) (at level 50, left associativity).
    Notation "p [+] q" := (choice p q) (at level 50, left associativity).
    Notation "'tau.' p" := (tau_prefix p) (at level 40).
  End Notations.

  Definition handshake (c v : name) : proc :=
    par (send c v zero) (recv c v zero).

  Lemma handshake_tau (c v : name) :
    handshake c v -[ tau ]-> par zero zero.
  Proof.
    unfold handshake.
    apply step_transition.
    eapply step_comm.
    - constructor.
    - cbn. replace (subst v v zero) with zero by reflexivity. constructor.
  Qed.

  CoInductive bisim : proc -> proc -> Prop :=
  | bisim_intro p q :
      (forall a p', p -[ a ]-> p' -> exists q', q -[ a ]-> q' /\ bisim p' q') ->
      (forall a q', q -[ a ]-> q' -> exists p', p -[ a ]-> p' /\ bisim p' q') ->
      bisim p q.

  CoInductive weak_bisim : proc -> proc -> Prop :=
  | weak_bisim_intro p q :
      (forall a p', p ==[ a ]=> p' -> exists q', q ==[ a ]=> q' /\ weak_bisim p' q') ->
      (forall a q', q ==[ a ]=> q' -> exists p', p ==[ a ]=> p' /\ weak_bisim p' q') ->
      weak_bisim p q.

  CoFixpoint bisim_refl (p : proc) : bisim p p :=
    bisim_intro p p
      (fun (a : action) (p1 : proc) (Hp : p -[ a ]-> p1) =>
         ex_intro _ p1 (conj Hp (bisim_refl p1)))
      (fun (a : action) (p1 : proc) (Hp : p -[ a ]-> p1) =>
         ex_intro _ p1 (conj Hp (bisim_refl p1))).

  CoFixpoint weak_bisim_refl (p : proc) : weak_bisim p p :=
    weak_bisim_intro p p
      (fun (a : action) (p1 : proc) (Hp : p ==[ a ]=> p1) =>
         ex_intro _ p1 (conj Hp (weak_bisim_refl p1)))
      (fun (a : action) (p1 : proc) (Hp : p ==[ a ]=> p1) =>
         ex_intro _ p1 (conj Hp (weak_bisim_refl p1))).

End Pi.
