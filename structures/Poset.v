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

Delimit Scope poset_scope with poset.
Bind Scope poset_scope with poset.

Class PosetMorphism {A B : poset} (f : A -> B) :=
  {
    mor_monotonic :>
      Monotonic f (ref ++> ref);
  }.

Delimit Scope poselt_scope with poselt.
Bind Scope poselt_scope with poset_carrier.

Notation "x [=  y" := (ref x%poselt y%poselt) (at level 70).
