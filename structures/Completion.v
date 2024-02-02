Require Import coqrel.LogicalRelations.
Require Import structures.Lattice.

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
    forall {L M : cdlattice}, (L -> M) -> Prop.

  Axiom mor_ref :
    forall {L M : cdlattice} (f : L -> M), Morphism f -> PosetMorphism f.

  Axiom id_mor :
    forall {L : cdlattice}, @Morphism L L (fun l => l).

  Axiom compose_mor :
    forall {A B C : cdlattice} (g : B -> C) (f : A -> B),
      Morphism f -> Morphism g -> Morphism (fun a => g (f a)).

  Existing Class Morphism.
  Existing Instance mor_ref.
  Existing Instance id_mor.
  Existing Instance compose_mor.

End LatticeCategory.

(** Then a free completion has the following interface. Note that the
  type of morphism used fully characterizes the completion, so that we
  can always use an opaque implementation. *)

Module Type LatticeCompletionSpec (LC : LatticeCategory).

  Parameter F : poset -> cdlattice.
  Parameter emb : forall {C : poset}, C -> F C.
  Parameter ext : forall {C : poset} {L : cdlattice}, (C -> L) -> F C -> L.

  Section DEFS.
    Context {C : poset} {L : cdlattice} {f : C -> L}.

    Axiom emb_mor : forall c1 c2 : C, emb c1 [= emb c2 <-> c1 [= c2.
    Axiom ext_mor : LC.Morphism (ext f).
    Axiom ext_ana : forall `{Hf : !PosetMorphism f} x, ext f (emb x) = f x.
    Axiom ext_unique :
      forall `{Hf : !PosetMorphism f} (g : F C -> L) `{Hg : !LC.Morphism g},
        (forall x, g (emb x) = f x) ->
        (forall x, g x = ext f x).
  End DEFS.

  Hint Extern 1 (LC.Morphism (ext _)) =>
    apply @ext_mor : typeclass_instances.

End LatticeCompletionSpec.

Module LatticeCompletionDefs (LC : LatticeCategory) (CS : LatticeCompletionSpec LC).

  Definition map {A B : poset} (f : A -> B) : CS.F A -> CS.F B :=
    CS.ext (fun a => CS.emb (f a)).

  Instance map_mor {A B : poset} (f : A -> B) :
    PosetMorphism f ->
    LC.Morphism (map f).
  Proof.
    unfold map.
    typeclasses eauto.
  Qed.

  Instance emb_mor' {C : poset} :
    PosetMorphism (CS.emb (C:=C)).
  Proof.
    constructor. intros x y Hxy.
    apply CS.emb_mor. auto.
  Qed.

  Lemma ext_emb {A : poset} (x : CS.F A) :
    CS.ext CS.emb x = x.
  Proof.
  Admitted.

  Lemma ext_ext {A B : poset} {L : cdlattice} :
    forall {f : A -> CS.F B} `{!PosetMorphism f},
    forall {g : B -> L} `{!PosetMorphism g},
    forall (x : CS.F A), CS.ext g (CS.ext f x) = CS.ext (fun a => CS.ext g (f a)) x.
  Proof.
  Admitted.

  Global Instance emb_params : Params (@CS.emb) 1.
  Defined.
  Global Instance ext_params : Params (@CS.ext) 1.
  Defined.
  Global Instance map_params : Params (@map) 1.
  Defined.

End LatticeCompletionDefs.

Module Type LatticeCompletion (LC : LatticeCategory) :=
  LatticeCompletionSpec LC <+ LatticeCompletionDefs LC.
