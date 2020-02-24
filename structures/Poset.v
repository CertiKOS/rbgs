Require Import coqrel.LogicalRelations.


(** * Partially ordered sets *)

Class Poset (C : Type) :=
  {
    ref : relation C;
    ref_preo :> PreOrder ref;
    ref_po :> Antisymmetric C eq ref;
  }.

Class PosetMorphism {A B} `{!Poset A} `{!Poset B} (f : A -> B) :=
  {
    mor_monotonic :>
      Monotonic f (ref ++> ref);
  }.

Notation "(⊑)" := ref.
Infix "⊑" := ref (at level 70).
