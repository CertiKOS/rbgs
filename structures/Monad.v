Require Import coqrel.LogicalRelations.
Require Import Lattice.

Class CDMonad (M : Type -> Type) :=
  {
    cdm_lattice :> forall A, Poset A -> CDLattice (M A);

    ret {A} `{Aref : Poset A} : A -> M A;
    bind {A L} `{Apo : Poset A} `{Lcdl : CDLattice L} : (A -> L) -> (M A -> L);

    ret_bind {A} `{Apo : Poset A} :
      forall (x : M A),
        bind ret x = x;
    bind_ret {A B} `{Apo : Poset A} `{Bpo : Poset B} :
      forall (f : A -> M B) (v : A),
        bind f (ret v) = f v;
    bind_bind {A B C} `{Apo : Poset A} `{Bpo : Poset B} `{Cpo : Poset C} :
      forall (f : A -> M B) (g : B -> M C) (x : M A),
        bind g (bind f x) = bind (fun v => bind g (f v)) x;

    bind_sup {A L I} `{Apo : Poset A} `{Lcd : CDLattice L} :
      forall (f : A -> L) (x : I -> M A),
        bind f (sup x) = sup (fun i => bind f (x i));
    bind_inf {A L I} `{Poset A} `{Lcd : CDLattice L} :
      forall (f : A -> L) (x : I -> M A),
        bind f (inf x) = inf (fun i => bind f (x i));
  }.
