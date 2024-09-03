Require Import Classical.
Require Import Program.Equality.
From coqrel Require Import LogicalRelations.
Require Import Poset.
Require Import Lattice.
Require Import Downset.

Record esig :=
  {
    op :> Type;
    ar : op -> Type;
  }.

Arguments ar {_}.

Section Strat.

  Context {E F: esig}.

  Inductive play :=
  | ready_nil
  | oq (q: op F) (s: running q)
  with running: op F -> Type :=
  | pq q (m: op E) (s: suspended q m): running q 
  | pr q (r: ar q) (s: play): running q
  with suspended: op F -> op E -> Type :=
  | suspended_nil (q: op F) (m: op E): suspended q m
  | or (q: op F) (m: op E) (n: ar m) (s: running q): suspended q m.

  Scheme play_mut := Induction for play Sort Prop
  with running_mut := Induction for running Sort Prop
  with suspended_mut := Induction for suspended Sort Prop.

End Strat.
