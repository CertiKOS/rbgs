Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import RBGS.
Require Import models.Pi.Syntax.

(** RBGS-compatible semantics for the locally-nameless π-calculus.
    Behaviors are finite traces of observable actions encoded as
    polynomial terms over the π signature. Refinement is inclusion of
    trace sets, and parallel composition is compositional. *)

Module PiSemantics.
  Module Syn := PiSyntax.
  Import Syn.

  Module Sig := EffectSignatures.Sig.
  Import (coercions, canonicals) Sig.
  Open Scope list_scope.
  Open Scope term_scope.

  (** * Actions and small-step semantics *)

  Definition name := atom.

  Inductive action :=
  | tau
  | in_act (c v : name)
  | out_act (c v : name).

  Definition action_uses (x : name) (a : action) : bool :=
    match a with
    | tau => false
    | in_act c v => (x =? c) || (x =? v)
    | out_act c v => (x =? c) || (x =? v)
    end.

  (** A lightweight operational semantics that respects binding via
      [open]/[close] from the locally-nameless syntax. *)
  Inductive step : action -> proc -> proc -> Prop :=
  | step_tau p :
      step tau (tau_prefix p) p
  | step_out c v p :
      step (out_act c v) (send (FVar c) (FVar v) p) p
  | step_in c p v :
      step (in_act c v) (recv (FVar c) p) (open v p)
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
  | step_nu a p p' x :
      step a (open x p) p' ->
      action_uses x a = false ->
      step a (nu p) (nu (close x p'))
  | step_rep a p p' :
      step a (par p (rep p)) p' ->
      step a (rep p) p'.

  (** * Traces and RBGS signature view *)

  Inductive trace : proc -> list action -> Prop :=
  | trace_nil p :
      trace p []
  | trace_cons a p q tr :
      step a p q ->
      trace q tr ->
      trace p (a :: tr).

  Variant pi_op :=
  | op_tau
  | op_in (c v : name)
  | op_out (c v : name).

  Canonical Structure PiSig :=
    {|
      Sig.op := pi_op;
      Sig.ar _ := unit;
    |}.

  Definition op_of_action (a : action) : pi_op :=
    match a with
    | tau => op_tau
    | in_act c v => op_in c v
    | out_act c v => op_out c v
    end.

  Definition trace_term (tr : list action) : Sig.term PiSig unit :=
    fold_right (fun a acc => Sig.cons (op_of_action a) (fun _ => acc))
               (Sig.var tt) tr.

  (** Interaction-structure view to plug into the RBGS refinement tower. *)
  Module IS := IntStrat.

  Definition Pi_esig : IS.esig :=
    {|
      IS.op := pi_op;
      IS.ar _ := unit;
    |}.

  Definition action_app (a : action) : IS.application Pi_esig unit :=
    IS.econs (E:=Pi_esig) (op_of_action a) (fun _ => tt).

  (** * Semantics as trace sets and refinement *)

  Definition sem_proc (p : proc) (t : Sig.term PiSig unit) : Prop :=
    exists tr, trace p tr /\ t = trace_term tr.

  Definition refines (p q : proc) : Prop :=
    forall t, sem_proc p t -> sem_proc q t.

  Lemma refines_refl p : refines p p.
  Proof. firstorder. Qed.

  Lemma refines_trans p q r :
    refines p q -> refines q r -> refines p r.
  Proof. firstorder. Qed.

  Lemma trace_term_injective tr1 tr2 :
    trace_term tr1 = trace_term tr2 ->
    tr1 = tr2.
  Proof.
    revert tr2. induction tr1 as [|a1 tr1 IH]; intros [|a2 tr2]; cbn; intro H.
    - reflexivity.
    - inversion H.
    - inversion H.
    - injection H as _ Hk.
      apply (f_equal (fun k => k tt)) in Hk.
      cbn in Hk.
      apply IH in Hk.
      f_equal; assumption.
  Qed.

  (** * Compositionality of parallel composition *)

  Inductive sync_interleave : list action -> list action -> list action -> Prop :=
  | sync_nil :
      sync_interleave [] [] []
  | sync_left a trl trr tr :
      sync_interleave trl trr tr ->
      sync_interleave (a :: trl) trr (a :: tr)
  | sync_right a trl trr tr :
      sync_interleave trl trr tr ->
      sync_interleave trl (a :: trr) (a :: tr)
  | sync_comm_out_in c v trl trr tr :
      sync_interleave trl trr tr ->
      sync_interleave (out_act c v :: trl) (in_act c v :: trr) (tau :: tr)
  | sync_comm_in_out c v trl trr tr :
      sync_interleave trl trr tr ->
      sync_interleave (in_act c v :: trl) (out_act c v :: trr) (tau :: tr).

  Lemma trace_par_split p q tr :
    trace (par p q) tr ->
    exists trp trq,
      trace p trp /\
      trace q trq /\
      sync_interleave trp trq tr.
  Proof.
    revert p q.
    induction tr as [|a tr IH]; intros p q Htr.
    - inversion Htr; subst. exists [], []. repeat constructor.
    - inversion Htr as [a' pq r Hstep Hrest]; subst.
      inversion Hstep; subst.
      + specialize (IH _ _ Hrest) as (trp & trq & Hp & Hq & Hinter).
        exists (a :: trp), trq. repeat split; try constructor; auto.
        constructor; auto.
      + specialize (IH _ _ Hrest) as (trp & trq & Hp & Hq & Hinter).
        exists trp, (a :: trq). repeat split; try constructor; auto.
        constructor; auto.
      + specialize (IH _ _ Hrest) as (trp & trq & Hp & Hq & Hinter).
        exists (out_act c v :: trp), (in_act c v :: trq).
        repeat split; try constructor; auto.
        constructor; auto.
      + specialize (IH _ _ Hrest) as (trp & trq & Hp & Hq & Hinter).
        exists (in_act c v :: trp), (out_act c v :: trq).
        repeat split; try constructor; auto.
        constructor; auto.
      + specialize (IH _ _ Hrest) as (trp & trq & Hp & Hq & Hinter).
        exists (a :: trp), trq. repeat split; try constructor; auto.
        constructor; auto.
      + specialize (IH _ _ Hrest) as (trp & trq & Hp & Hq & Hinter).
        exists (a :: trp), trq. repeat split; try constructor; auto.
        constructor; auto.
  Qed.

  Lemma trace_par_combine p q trp trq tr :
    trace p trp ->
    trace q trq ->
    sync_interleave trp trq tr ->
    trace (par p q) tr.
  Proof.
    revert p q trp trq.
    induction tr; intros p q trp trq Hp Hq Hinter; inversion Hinter; subst; clear Hinter.
    - inversion Hp; inversion Hq; subst. constructor.
    - inversion Hp as [ ? ? ? Hpstep Hp' ]; subst.
      econstructor; [eapply step_par_l; eauto|].
      apply IHtr; auto.
    - inversion Hq as [ ? ? ? Hqstep Hq' ]; subst.
      econstructor; [eapply step_par_r; eauto|].
      apply IHtr; auto.
    - inversion Hp as [ ? ? ? Hpstep Hp' ]; subst.
      inversion Hq as [ ? ? ? Hqstep Hq' ]; subst.
      econstructor; [eapply step_comm; eauto|].
      apply IHtr; auto.
    - inversion Hp as [ ? ? ? Hpstep Hp' ]; subst.
      inversion Hq as [ ? ? ? Hqstep Hq' ]; subst.
      econstructor; [eapply step_comm; eauto|].
      apply IHtr; auto.
  Qed.

  Theorem par_refines p1 q1 p2 q2 :
    refines p1 q1 ->
    refines p2 q2 ->
    refines (par p1 p2) (par q1 q2).
  Proof.
    intros H1 H2 t [tr [Htr Ht]].
    apply trace_par_split in Htr as (trp & trq & Hp & Hq & Hinter).
    assert (sem_proc q1 (trace_term trp)) as Hsem1 by (apply H1; eauto).
    assert (sem_proc q2 (trace_term trq)) as Hsem2 by (apply H2; eauto).
    destruct Hsem1 as [trp' [Hp' Heqp]].
    destruct Hsem2 as [trq' [Hq' Heqq]].
    apply trace_term_injective in Heqp; subst.
    apply trace_term_injective in Heqq; subst.
    exists tr. split.
    - eapply trace_par_combine; eauto.
    - assumption.
  Qed.

End PiSemantics.

