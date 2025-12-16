Require Import Coq.Arith.PeanoNat.
Require Import models.EffectSignatures.
Require Import models.IntStrat.

(** A light PFPL-inspired parallel fragment expressed with the
    polynomial signature machinery. *)

Module PFPLParallel.
  Module Sig := EffectSignatures.Sig.
  Import (coercions, canonicals) Sig.
  Open Scope term_scope.

  Variant par_op :=
  | op_tick
  | op_fork
  | op_join.

  Canonical Structure ParSig :=
    {|
      Sig.op := par_op;
      Sig.ar _ := unit;
    |}.

  Definition par_term (X : Type) := Sig.term ParSig X.

  Definition tick {X} (k : unit -> par_term X) : par_term X :=
    Sig.cons op_tick k.

  Definition fork {X} (k : unit -> par_term X) : par_term X :=
    Sig.cons op_fork k.

  Definition join {X} (k : unit -> par_term X) : par_term X :=
    Sig.cons op_join k.

  Fixpoint op_count {X} (t : par_term X) : nat :=
    match t with
    | Sig.var _ => 0
    | Sig.cons _ k => S (op_count (k tt))
    end.

  Definition two_ticks : par_term nat :=
    tick (fun _ => tick (fun _ => Sig.var 0)).

  Lemma two_ticks_count : op_count two_ticks = 2.
  Proof. reflexivity. Qed.

  Definition fork_join : par_term nat :=
    fork (fun _ => join (fun _ => Sig.var 0)).

  Lemma fork_join_count : op_count fork_join = 2.
  Proof. reflexivity. Qed.

  (** Interaction-structure view of the same signature. *)
  Module IS := IntStrat.

  Definition Par_esig : IS.esig :=
    {|
      IS.op := par_op;
      IS.ar _ := unit;
    |}.

  Definition par_app (o : par_op) : IS.application Par_esig unit :=
    IS.econs (E:=Par_esig) o (fun _ => tt).

End PFPLParallel.
