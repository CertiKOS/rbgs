Require Import coqrel.LogicalRelations.
Require Import Lattice.

(** We construct various kinds of strategy models by defining the
  plays they use and a corresponding prefix ordering, then choosing
  a free completion corresponding to the kind of nondeterminism we
  wish to consider.

  In particular, the traditional construction of strategies as
  prefix-closed sets of plays corresponds to the downset completion,
  which is initial in the category of distributive lattices and
  join-distributive morphisms. This introduces angelic nondeterminism,
  which lets us consider all possible choices of the environment.
  We go one step further and consider the free completely distributive
  lattice over plays, which is initial wrt. complete morphisms. This
  models demonic as well as angelic nondeterminism and allows us to
  model strategy specifications permitting several possible system
  behaviors.

  This library captures the general pattern poset completions
  definitions as a module type and proves general properties which
  hold in all of them. This allows parts of our development to be
  carried out in a modular way and be instantiated for arbitrary
  lattice completions. *)


(** * Poset completions *)

(** Each of the completions we will consider is a free completion for
  a specific category of completely distributive lattices. Hence, the
  first step when constructing a completion procedure is to specify
  the kind of morphisms used in that category. *)

Module Type LatticeCategory.

  Parameter Morphism :
    forall {L M} `{Lcd : CDLattice L} `{Mcd : CDLattice M}, (L -> M) -> Prop.

  (*Axiom mor_ref : forall f, Morphism f -> Monotonic f ((⊑) ++> (⊑)).*)

  Existing Class Morphism.
  (*Existing Instance mor_ref.*)

End LatticeCategory.

(** Then a free completion has the following interface. Note that the
  type of morphism used fully characterizes the completion, so that we
  can always use an opaque implementation. *)

Module Type LatticeCompletion (LC : LatticeCategory).

  Parameter F : forall C `{Cpo : Poset C}, Type.
  Parameter lattice : forall `{Cpo : Poset}, CDLattice (F C).
  Existing Instance lattice.

  Parameter emb : forall `{Cpo : Poset}, C -> F C.
  Parameter ext : forall `{Cpo : Poset} `{Lcd : CDLattice}, (C -> L) -> F C -> L.

  Section DEFS.
    Context `{Cpo : Poset}.
    Axiom emb_mor : forall c1 c2, emb c1 ⊑ emb c2 <-> c1 ⊑ c2.

    Context `{Lcd : CDLattice} {f : C -> L}.
    Axiom ext_mor : LC.Morphism (ext f).
    Axiom ext_ana : forall `{Hf : Monotonic f ((⊑) ++> (⊑))} x, ext f (emb x) = f x.
    Axiom ext_unique :
      forall `{Hf : Monotonic f ((⊑) ++> (⊑))} (g : F C -> L) `{Hg : !LC.Morphism g},
        (forall x, g (emb x) = f x) ->
        (forall x, g x = ext f x).
  End DEFS.

  Existing Instance ext_mor.

End LatticeCompletion.
