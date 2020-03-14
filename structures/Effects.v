Require Import structures.Category.
Require Import structures.Lattice.
Require Import lattices.Upset.
Require Import lattices.LatticeProduct.
Require Import lattices.FCD.


(** * Effect signatures *)

Definition esig := Type -> Type.

Delimit Scope esig_scope with esig.
Bind Scope esig_scope with esig.

(** ** Direct sum *)

Inductive esum {E F : esig} : esig :=
  | einl {X} : E X -> esum X
  | einr {X} : F X -> esum X.

Arguments esum : clear implicits.

Infix "+" := esum : esig_scope.

(** ** Empty signature *)

Inductive empty_sig : esig := .

Notation "0" := empty_sig.


(** * Interpretations *)

Class LazyMorphism {A B : cdlattice} (f : A -> B) :=
  {
    lcdlm_inf :> Inf.Morphism f;
    lcdlm_sup {I} (x : I -> A) :
      inhabited I -> f (lsup x) = lsup (f @ x);
  }.

Record interp {E : esig} {A : cdlattice} :=
  {
    op {ar} (m : E ar) :> (A ^ ar)%cdlat -> A;
    op_lm {ar} (m : E ar) : LazyMorphism (op m);
  }.

Arguments interp : clear implicits.
Existing Instance op_lm.

Typeclasses eauto := debug.
Class InterpMorphism {E A B} (α : interp E A) (β : interp E B) (f : A -> B) :=
  {
    intm_lmor {ar} (m : E ar) :> CDL.Morphism f;
    op_mor {ar} (m : E ar) (k : ar -> A) : f (op α m k) = op β m (*(f @ k)%mor;*) (fun x => f ( k x));
  }.
