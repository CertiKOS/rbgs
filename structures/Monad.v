Require Import coqrel.LogicalRelations.
Require Import structures.Lattice.

Class CDMonad (M : Type -> cdlattice) :=
  {
    ret {A} : A -> M A;
    bind {A} {L : cdlattice} : (A -> L) -> (M A -> L);

    ret_bind {A} :
      forall (x : M A),
        bind ret x = x;
    bind_ret {A B} :
      forall (f : A -> M B) (v : A),
        bind f (ret v) = f v;
    bind_bind {A B C} :
      forall (f : A -> M B) (g : B -> M C) (x : M A),
        bind g (bind f x) = bind (fun v => bind g (f v)) x;

    bind_sup {A} {L : cdlattice} {I} :
      forall (f : A -> L) (x : I -> M A),
        bind f (sup x) = sup (fun i => bind f (x i));
    bind_inf {A} {L : cdlattice} {I} :
      forall (f : A -> L) (x : I -> M A),
        bind f (inf x) = inf (fun i => bind f (x i));
  }.
