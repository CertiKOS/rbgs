Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Data.Monads.StateMonad.
Require Import ITree.Simple.
Require Import coqrel.LogicalRelations.
Require Import structures.DCPOSLs.
Require Import models.EffectSignatures.

Module NDCAL.

  (** ** Layer specifications *)

  Module Spec.

    (** *** Definition *)

    Definition lts E A :=
      A -> forall (m : Sig.op E), FDSL.omap (Sig.ar m * A).

    Record t {E : Sig.t} :=
      {
        state : Type;
        next :> lts E state;
      }.

    Arguments t : clear implicits.

    (** Tentative notion of simulation for demonic nondeterminism. *)

    Variant outcome_rel {A B} (R : rel A B) : rel (outcome A) (outcome B) :=
      | val_rel : Monotonic val (R ++> outcome_rel R)
      | div_rel : Monotonic div (outcome_rel R).

    Definition sim {E A B} (R : A -> B -> Prop) (α : lts E A) (β : lts E B) :=
      Related α β (R ++> forallr -, set_ge (outcome_rel (eq * R))).

    (** Refinement defined as the existence of a simluation relations. *)

    Definition ref {E} (x y : t E) : Prop :=
      exists R : rel (state x) (state y), sim R (next x) (next y).

    (** *** As handlers *)

    (** To evaluate an implementation running on top of an underlay
      specification, we present our coalgebraic specs in terms of a
      monad recognized by the itree library. *)

    Definition handler {E} (σ : t E) X (e: Sig.sig_esig E X):
      stateT (state σ) FDSL.omap X :=
        let '(Sig.sig_esig_op _ m) := e in
          {| runStateT a := next σ a m |}.

  End Spec.

  Notation spec := Spec.t.

  (** ** Implementations *)

  (** Our layer implementations give an [itree] for each method. *)

  Definition impl (E F : Sig.t) :=
    forall m : Sig.op F, itree (Sig.sig_esig E) (Sig.ar m).

  (** We use [Spec.handler] to interpret these [itree]s in terms of
    a given underlay specification. *)

  Local Existing Instance Monad_stateT.

  Definition eval {E F} (M : impl E F) (Σ : spec E) :=
    {|
      Spec.next s q := runStateT (interp (Spec.handler Σ) (M q)) s;
    |}.

  (** ** Layer correctness *)

  Definition cal {E F} (Σ : spec E) (M : impl E F) (Δ : spec F) :=
    Spec.ref Δ (eval M Σ).

  (** ** Bundled definitions *)

  Record layer_interface :=
    {
      li_sig : Sig.t;
      li_spec : spec li_sig;
    }.

  Record layer_implementation {L L' : layer_interface} :=
    {
      li_impl : impl (li_sig L) (li_sig L');
      li_correct : cal (li_spec L) li_impl (li_spec L');
    }.

  Arguments layer_implementation : clear implicits.

End NDCAL.
