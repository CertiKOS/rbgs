Require Import coqrel.LogicalRelations.
Require Import Lattice.
Require Import Completion.
Require Import Downset.
Require Import Upset.


(** * Interface *)

(** The free completely distributive lattice over a poset is the
  completion with respect to complete morphisms. *)

Module CDL <: LatticeCategory.
  Section DEF.
    Context {L M} `{Lcd : CDLattice L} `{Mcd : CDLattice M} (f : L -> M).
    Class Morphism := mor : Sup.Morphism f /\ Inf.Morphism f.
    Global Instance cmor_sup : Morphism -> Sup.Morphism f := @proj1 _ _.
    Global Instance cmor_inf : Morphism -> Inf.Morphism f := @proj2 _ _.
  End DEF.
End CDL.


(** * Construction *)

Module FCD : LatticeCompletion CDL.

  Definition F C `{Poset C} := upset (downset C).

  Section DEF.
    Context `{Cpo : Poset}.

    Instance lattice : CDLattice (F C) := _.
    Definition emb (c : C) := up (down c).

    Lemma emb_mor c1 c2 :
      emb c1 ⊑ emb c2 <-> c1 ⊑ c2.
    Proof.
      unfold emb.
      rewrite Upset.emb_mor.
      rewrite Downset.emb_mor.
      reflexivity.
    Qed.

    Context `{Lcd : CDLattice}.

    Definition ext (f : C -> L) (x : F C) :=
      Upset.ext (Downset.ext f) x.

    Context {f : C -> L} `{Hf : Monotonic f ((⊑) ++> (⊑))}.

    Instance ext_mor :
      CDL.Morphism (ext f).
    Proof.
      clear Hf.
    Admitted.

    Lemma ext_ana :
      (forall x, ext f (emb x) = f x).
    Proof.
      intros x. unfold ext, emb.
      rewrite @Upset.ext_ana.
      apply Downset.ext_ana.
    Admitted.

    Lemma ext_unique (g : F C -> L) `{!CDL.Morphism g} :
      (forall x, g (emb x) = f x) -> forall x, g x = ext f x.
    Proof.
      unfold emb, ext. intros Hg x.
      apply @Upset.ext_unique. admit. typeclasses eauto.
      apply Downset.ext_unique. admit. auto.
    Admitted.

  End DEF.
End FCD.
