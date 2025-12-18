Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.

(** Locally-nameless π-calculus syntax with explicit open/close and
    substitution operations. Bound names are de Bruijn indices; free
    names are natural numbers. *)

Module PiSyntax.

  Definition atom := nat.

  Inductive nvar :=
  | BVar : nat -> nvar
  | FVar : atom -> nvar.

  Inductive proc :=
  | zero
  | tau_prefix (p : proc)
  | send (c v : nvar) (p : proc)
  | recv (c : nvar) (p : proc)      (* binds one name in [p] *)
  | par (p q : proc)
  | choice (p q : proc)
  | nu (p : proc)                   (* binds one name in [p] *)
  | rep (p : proc).

  (** Opening replaces the bound index [k] by a free name [x]. *)
  Definition open_name_rec (k : nat) (x : atom) (n : nvar) : nvar :=
    match n with
    | BVar i => if Nat.eqb i k then FVar x else n
    | FVar _ => n
    end.

  Fixpoint open_rec (k : nat) (x : atom) (p : proc) : proc :=
    match p with
    | zero => zero
    | tau_prefix p1 => tau_prefix (open_rec k x p1)
    | send c v p1 => send (open_name_rec k x c) (open_name_rec k x v) (open_rec k x p1)
    | recv c p1 => recv (open_name_rec k x c) (open_rec (S k) x p1)
    | par p1 p2 => par (open_rec k x p1) (open_rec k x p2)
    | choice p1 p2 => choice (open_rec k x p1) (open_rec k x p2)
    | nu p1 => nu (open_rec (S k) x p1)
    | rep p1 => rep (open_rec k x p1)
    end.

  Definition open (x : atom) (p : proc) : proc := open_rec 0 x p.

  (** Closing turns a free name [x] into the bound index [k]. *)
  Definition close_name_rec (k : nat) (x : atom) (n : nvar) : nvar :=
    match n with
    | BVar i => BVar i
    | FVar y => if Nat.eqb y x then BVar k else FVar y
    end.

  Fixpoint close_rec (k : nat) (x : atom) (p : proc) : proc :=
    match p with
    | zero => zero
    | tau_prefix p1 => tau_prefix (close_rec k x p1)
    | send c v p1 => send (close_name_rec k x c) (close_name_rec k x v) (close_rec k x p1)
    | recv c p1 => recv (close_name_rec k x c) (close_rec (S k) x p1)
    | par p1 p2 => par (close_rec k x p1) (close_rec k x p2)
    | choice p1 p2 => choice (close_rec k x p1) (close_rec k x p2)
    | nu p1 => nu (close_rec (S k) x p1)
    | rep p1 => rep (close_rec k x p1)
    end.

  Definition close (x : atom) (p : proc) : proc := close_rec 0 x p.

  (** Capture-avoiding substitution on free names. *)
  Definition subst_name (x y : atom) (n : nvar) : nvar :=
    match n with
    | BVar i => BVar i
    | FVar z => if Nat.eqb z x then FVar y else FVar z
    end.

  Fixpoint subst (x y : atom) (p : proc) : proc :=
    match p with
    | zero => zero
    | tau_prefix p1 => tau_prefix (subst x y p1)
    | send c v p1 => send (subst_name x y c) (subst_name x y v) (subst x y p1)
    | recv c p1 => recv (subst_name x y c) (subst x y p1)
    | par p1 p2 => par (subst x y p1) (subst x y p2)
    | choice p1 p2 => choice (subst x y p1) (subst x y p2)
    | nu p1 => nu (subst x y p1)
    | rep p1 => rep (subst x y p1)
    end.

  (** Local closure: [k] counts how many surrounding binders are in scope. *)
  Definition lc_name (k : nat) (n : nvar) : Prop :=
    match n with
    | BVar i => i < k
    | FVar _ => True
    end.

  Fixpoint lc_rec (k : nat) (p : proc) : Prop :=
    match p with
    | zero => True
    | tau_prefix p1 => lc_rec k p1
    | send c v p1 => lc_name k c /\ lc_name k v /\ lc_rec k p1
    | recv c p1 => lc_name k c /\ lc_rec (S k) p1
    | par p1 p2 => lc_rec k p1 /\ lc_rec k p2
    | choice p1 p2 => lc_rec k p1 /\ lc_rec k p2
    | nu p1 => lc_rec (S k) p1
    | rep p1 => lc_rec k p1
    end.

  Definition lc (p : proc) : Prop := lc_rec 0 p.

End PiSyntax.

