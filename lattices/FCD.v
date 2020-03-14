Require Import coqrel.LogicalRelations.
Require Import structures.Lattice.
Require Import structures.Completion.
Require Import lattices.Downset.
Require Import lattices.Upset.


(** * Interface *)

(** The free completely distributive lattice over a poset is the
  completion with respect to complete morphisms. *)

Module CDL <: LatticeCategory.
  Section DEF.
    Context {L M : cdlattice} (f : L -> M).

    Class Morphism := mor : Sup.Morphism f /\ Inf.Morphism f.
    Global Instance cmor_sup : Morphism -> Sup.Morphism f := @proj1 _ _.
    Global Instance cmor_inf : Morphism -> Inf.Morphism f := @proj2 _ _.

    Instance mor_ref :
      Morphism -> PosetMorphism f.
    Proof.
      intros [H _].
      apply Sup.mor_ref; auto.
    Qed.
  End DEF.

  Lemma id_mor (L : cdlattice) :
    Morphism (fun x:L => x).
  Proof.
    split.
    - apply Sup.id_mor.
    - apply Inf.id_mor.
  Qed.

  Lemma compose_mor {A B C : cdlattice} (g : B -> C) (f : A -> B) :
    Morphism f ->
    Morphism g ->
    Morphism (fun a => g (f a)).
  Proof.
    split.
    - apply Sup.compose_mor; typeclasses eauto.
    - apply Inf.compose_mor; typeclasses eauto.
  Qed.

  Existing Instance mor_ref.

End CDL.


(** * Specification *)

Module Type JoinMeetDense (LC : LatticeCompletion CDL).

  Axiom join_meet_dense :
    forall {C : poset} (x : LC.F C),
      exists I J (c : forall i:I, J i -> C), x = sup i, inf j, LC.emb (c i j).

  Axiom meet_join_dense :
    forall {C : poset} (x : LC.F C),
      exists I J (c : forall i:I, J i -> C), x = inf i, sup j, LC.emb (c i j).

End JoinMeetDense.

Module Type FCDSpec := LatticeCompletion CDL <+ JoinMeetDense.


(** * Construction *)

Module FCD : FCDSpec.

  Definition F (C : poset) := upset (downset C).

  Section DEF.
    Context {C : poset}.

    Definition emb (c : C) := up (down c).

    Lemma emb_mor c1 c2 :
      emb c1 [= emb c2 <-> c1 [= c2.
    Proof.
      unfold emb.
      rewrite Upset.emb_mor.
      rewrite Downset.emb_mor.
      reflexivity.
    Qed.

    Context {L : cdlattice}.

    Definition ext (f : C -> L) (x : F C) :=
      Upset.ext (Downset.ext f) x.

    Context {f : C -> L} `{Hf : !PosetMorphism f}.

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

  Include (LatticeCompletionDefs CDL).

  Lemma meet_join_dense {C : poset} (x : F C) :
    exists I J c, x = inf i : I, sup j : J i, emb (c i j).
  Proof.
    exists {S : downset C | up S [= x}.
    exists (fun i => {c : C | down c [= proj1_sig i}).
    exists (fun i j => proj1_sig j).
    apply antisymmetry.
    - apply inf_glb. intros [S HS].
  Admitted.

  Lemma join_meet_dense {C : poset} (x : F C) :
    exists I J c, x = sup i : I, inf j : J i, emb (c i j).
  Proof.
    destruct (meet_join_dense x) as (I & J & c & Hx).
    rewrite inf_sup in Hx.
    exists (forall i, J i), (fun _ => I), (fun f i => c i (f i)).
    assumption.
  Qed.

End FCD.
