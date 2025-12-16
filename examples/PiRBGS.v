Require Import Coq.Lists.List.
Import ListNotations.
Require Import models.IntStrat.
Require Import models.EffectSignatures.
Require Import examples.PiCalculus.

(** Bridge the lightweight π-calculus LTS to the RBGS signature/interaction
    structures. We keep this as a thin wiring layer: a signature, a trace
    embedding as polynomial terms, and an interaction-structure view. *)

Module PiRBGS.
  Module P := Pi.
  Module Sig := EffectSignatures.Sig.
  Import (coercions, canonicals) Sig.
  Open Scope term_scope.

  (** Signature for observable π actions as a polynomial signature. *)
  Variant pi_op :=
  | op_tau
  | op_in (c v : P.name)
  | op_out (c v : P.name).

  Canonical Structure PiSig :=
    {|
      Sig.op := pi_op;
      Sig.ar _ := unit;
    |}.

  Definition op_of_action (a : P.action) : pi_op :=
    match a with
    | P.tau => op_tau
    | P.in_act c v => op_in c v
    | P.out_act c v => op_out c v
    end.

  (** Encode a finite trace of actions as a term over the signature. *)
  Definition trace_term (tr : list P.action) : Sig.term PiSig unit :=
    fold_right (fun a acc => Sig.cons (op_of_action a) (fun _ => acc))
               (Sig.var tt) tr.

  (** Basic interaction-structure view using [IntStrat.esig/application]. *)
  Module IS := IntStrat.

  Definition Pi_esig : IS.esig :=
    {|
      IS.op := pi_op;
      IS.ar _ := unit;
    |}.

  Definition action_app (a : P.action) : IS.application Pi_esig unit :=
    IS.econs (E:=Pi_esig) (op_of_action a) (fun _ => tt).

  (** A simple stateful handler that records the trace as a list of [pi_op]. *)
  Definition pi_state := list pi_op.

  Definition handle_action (s : pi_state) (a : P.action) : pi_state :=
    s ++ [op_of_action a].

  Definition run_trace (tr : list P.action) : pi_state :=
    fold_left handle_action tr [].

End PiRBGS.
