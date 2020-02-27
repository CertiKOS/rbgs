Require Import Category.
Require Import Lattice.
Require Import Upset.
Require Import LatticeProduct.
Require Import FCD.


(** * Effect signatures *)

Definition esig := Type -> Type.

Delimit Scope esig_scope with esig.
Bind Scope esig_scope with esig.

Inductive esum {E F : esig} : esig :=
  | einl {X} : E X -> esum X
  | einr {X} : F X -> esum X.

Arguments esum : clear implicits.

Infix "+" := esum : esig_scope.


(** * Interpretations *)

Class LazyMorphism {A B} `{!CDLattice A} `{CDLattice B} (f : A -> B) :=
  {
    lcdlm_inf :> Inf.Morphism f;
    lcdlm_sup {I} (x : I -> A) :
      inhabited I -> f (sup x) = sup (f @ x);
  }.

Class Interp (E : esig) (A : Type) :=
  {
    int_lat :> CDLattice A;
    op {ar} (m : E ar) : (ar -> A) -> A;
    op_lm {ar} (m : E ar) :> LazyMorphism (op m);
  }.

Class InterpMorphism E {A B} `{!Interp E A} `{!Interp E B} (f : A -> B) :=
  {
    intm_lmor {ar} (m : E ar) :> CDL.Morphism (op m);
    op_mor {ar} (m : E ar) (k : ar -> A) : f (op m k) = op m (f @ k);
  }.
