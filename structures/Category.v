Require Import Lattice.
Require Import FCD.


(** * Categories *)

Class Category (V : Type) (E : V -> V -> Type) :=
  {
    id {A} : E A A;
    compose {A B C} : E B C -> E A B -> E A C;

    id_compose {A B} (f : E A B) :
      compose id f = f;
    compose_id {A B} (f : E A B) :
      compose f id = f;
    compose_assoc {A B C D} (f : E C D) (g : E B C) (h : E A B) :
      compose f (compose g h) = compose (compose f g) h;
  }.

Delimit Scope obj_scope with obj.
Delimit Scope mor_scope with mor.

Notation "(@)" := compose.
Notation "( f @)" := (compose f).
Notation "(@  g )" := (fun f => compose f g).
Infix "@" := compose (at level 40, left associativity) : mor_scope.


(** * Monoidal structure *)

Class SMCat (V : Type) (E : V -> V -> Type) :=
  {
    tens : V -> V -> V;
    mtens {A1 A2 B1 B2} : E A1 B1 -> E A2 B2 -> E (tens A1 A2) (tens B1 B2);
  }.

Infix "*" := tens : obj_scope.
Infix "*" := mtens : mor_scope.


(** * CDLat-enriched categories *)

Class CDCat (V : Type) (E : V -> V -> cdlattice) :=
  {
    cdcat_cat : Category V E;

    compose_mor_r {A B C} (f : E B C) :>
      CDL.Morphism (compose (A:=A) f);
    compose_mor_l {A B C} (g : E A B) :>
      CDL.Morphism (fun f => compose (C:=C) f g);
  }.


(** * Sets and functions *)

Program Instance SET : Category Type (fun A B => A -> B) :=
  {
    id A := fun a => a;
    compose A B C f g := fun a => f (g a);
  }.

Instance SET_prod : SMCat Type (fun A B => A -> B) :=
  {
    tens := prod;
    mtens A1 A2 B1 B2 f1 f2 x := (f1 (fst x), f2 (snd x));
  }.

Bind Scope obj_scope with Sortclass.
Bind Scope mor_scope with Funclass.
