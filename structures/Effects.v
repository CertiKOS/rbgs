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

Class LazyMorphism {A B : cdlattice} (f : A -> B) :=
  {
    lcdlm_inf :> Inf.Morphism f;
    lcdlm_sup {I} (x : I -> A) :
      inhabited I -> f (sup x) = sup (f @ x);
  }.

Record interp {E : esig} {A : cdlattice} :=
  {
    op {ar} (m : E ar) :> (A ^ ar)%cdlat -> A;
    op_lm {ar} (m : E ar) : LazyMorphism (op m);
  }.

Arguments interp : clear implicits.
Existing Instance op_lm.

Class InterpMorphism {E A B} (α : interp E A) (β : interp E B) (f : A -> B) :=
  {
    intm_lmor {ar} (m : E ar) :> CDL.Morphism f;
    op_mor {ar} (m : E ar) (k : ar -> A) : f (op α m k) = op β m (f @ k)%mor;
  }.
