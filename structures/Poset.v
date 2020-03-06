Require Export coqrel.LogicalRelations.


(** * Partially ordered sets *)

Record poset :=
  {
    poset_carrier :> Type;
    ref : relation poset_carrier;
    ref_preo : PreOrder ref;
    ref_po : Antisymmetric poset_carrier eq ref;
  }.

Arguments ref {_}.
Existing Instance ref_preo.
Existing Instance ref_po.

Class PosetMorphism {A B : poset} (f : A -> B) :=
  {
    mor_monotonic :>
      Monotonic f (ref ++> ref);
  }.

Notation "(⊑)" := ref.
Infix "⊑" := ref (at level 70).
