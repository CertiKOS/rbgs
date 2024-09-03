Require Import FunctionalExtensionality.
From structures Require Import Poset.
From lattices Require Import LatticeProduct.

Record suplat :=
  {
    sup_poset :> poset;
    lsup : forall {I}, (I -> sup_poset) -> sup_poset;
    sup_ub {I} (i : I) (x : I -> sup_poset) :
      ref (x i) (lsup x);
    sup_lub {I} (x : I -> sup_poset) (y : sup_poset) :
      (forall i, ref (x i) y) ->
      ref (lsup x) y;
  }.
Arguments lsup {_ _}.
Arguments sup_ub {_ _}.
Arguments sup_lub {_ _}.

Program Definition suplat_prod {K : Type} (L : K -> suplat) : suplat :=
  {|
    sup_poset := poset_prod L;
    lsup I x k := lsup (fun i => x i k);

    sup_ub I i x k := sup_ub i (fun i => x i k);
    sup_lub I x y H k := sup_lub (fun i => x i k) (y k) (fun i => H i k);
  |}.

Delimit Scope suplat_scope with suplat.
Bind Scope suplat_scope with suplat.
Notation "'pi' i .. j , M" :=
  (suplat_prod (fun i => .. (suplat_prod (fun j => M%suplat)) .. ))
  (at level 65, i binder, j binder, right associativity) : suplat_scope.

Notation "L ^ K" := (pi k : K, L)%suplat : suplat_scope.

From structures Require Import Effects.

Inductive effect (E: esig) (A: suplat) : Type :=
  | run : forall {X: Type}, E X -> (X -> A) -> effect E A.
Arguments run {_ _ _} _ _.
