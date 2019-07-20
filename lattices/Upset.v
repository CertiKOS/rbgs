Require Import coqrel.LogicalRelations.
Require Import Lattice.
Require Import Downset.
Require Import FunctionalExtensionality.


(** * Interface *)

(** The upset lattice over a poset is a completely distributive
  completion that is meet dense and completely meet prime. We use it
  as an intermediate step in the construction of the free completely
  distributive lattice (see [Morris, 2005]). *)

Module Inf <: LatticeCategory.
  Class Morphism {L M} `{CDLattice L} `{CDLattice M} (f : L -> M) :=
    mor : forall {I} (x : I -> L), f (inf x) = ⋀ i; f (x i).
End Inf.


(** * Construction *)

Module Upset : LatticeCompletion Inf.

  (** ** Opposite order *)

  (** To avoid redundancies, we define the opposite order and lattice,
    and construct upsets by dualizing the [Downset] completion. This
    may or may not result in a lower complexity than copy-and-pasting,
    so we should evaluate once the [Downset] proofs are completed. *)

  Inductive opp (A : Type) := opp_in (a : A).
  Arguments opp_in {A} _.

  Definition opp_out {A} : opp A -> A :=
    fun '(opp_in a) => a.

  Lemma opp_in_out_eq {A} (x : A) (y : opp A) :
    opp_in x = y -> x = opp_out y.
  Proof.
    destruct y. cbn. congruence.
  Qed.

  Program Instance opp_poset `(Poset) : Poset (opp C) | 5 :=
    {
      ref x y := opp_out y ⊑ opp_out x;
    }.
  Next Obligation.
    split.
    - intros [x]. reflexivity.
    - intros [x] [y] [z] Hyz Hxy. etransitivity; eauto.
  Qed.
  Next Obligation.
    intros [x] [y] Hxy Hyx.
    f_equal. apply antisymmetry; auto.
  Qed.

  Program Instance opp_lattice `(CDLattice) : CDLattice (opp L) :=
    {
      sup I x := opp_in (inf (fun i => opp_out (x i)));
      inf I x := opp_in (sup (fun i => opp_out (x i)));
    }.
  Next Obligation. apply (inf_lb (fun i => opp_out (x i))). Qed.
  Next Obligation. apply inf_glb; auto. Qed.
  Next Obligation. apply (sup_ub (fun i => opp_out (x i))). Qed.
  Next Obligation. apply sup_lub; auto. Qed.
  Next Obligation. f_equal. apply inf_sup. Qed.

  Definition opp_map {A B} (f : A -> B) : opp A -> opp B :=
    fun '(opp_in a) => opp_in (f a).

  Instance opp_map_ref {A B} `{Poset A} `{Poset B} (f : A -> B) :
    Monotonic f ((⊑) ++> (⊑)) ->
    Monotonic (opp_map f) ((⊑) ++> (⊑)).
  Proof.
    intros Hf [x] [y] Hxy. cbn in *. rauto.
  Qed.

  (** ** Upsets *)

  Definition F C `{Cpo : Poset C} := opp (downset (opp C)).
  Instance lattice : forall `{Poset}, CDLattice (F C) := _.

  Section DEFS.
    Context `{Poset}.

    Definition emb (c : C) : F C :=
      opp_in (Downset.down (opp_in c)).

    Lemma emb_mor c1 c2 : emb c1 ⊑ emb c2 <-> c1 ⊑ c2.
    Proof.
      split; intro Hc; cbn in *.
      - rewrite Downset.emb_mor in Hc. assumption.
      - rewrite Downset.emb_mor. assumption.
    Qed.

    Context `{CDLattice} (f : C -> L).

    Definition ext (x : F C) : L :=
      opp_out (Downset.ext (opp_map f) (opp_out x)).

    Instance ext_mor :
      Monotonic f ((⊑) ++> (⊑)) ->
      Inf.Morphism ext.
    Proof.
      intros Hf I x. unfold ext. cbn.
      rewrite Sup.mor. cbn. auto.
    Qed.

    Lemma ext_ana :
      Monotonic f ((⊑) ++> (⊑)) ->
      (forall x, ext (emb x) = f x).
    Proof.
      intros Hf x. unfold ext. cbn.
      rewrite Downset.ext_ana. cbn. auto.
      typeclasses eauto.
    Qed.

    Lemma ext_unique (g : F C -> L) :
      Monotonic f ((⊑) ++> (⊑)) ->
      Inf.Morphism g ->
      (forall x, g (emb x) = f x) ->
      g = ext.
    Proof.
      intros Hf Hg Hgf. apply functional_extensionality. intros [x].
      unfold emb, ext in *. cbn in *. apply opp_in_out_eq.
      rewrite <- Downset.ext_unique with (g0 := fun x => opp_in (g (opp_in x))); auto.
      - typeclasses eauto.
      - clear - Hg. intros I x. cbn.
        rewrite <- Inf.mor. cbn. reflexivity.
      - intros [y]. cbn. congruence.
    Qed.
  End DEFS.

End Upset.

Notation upset := Upset.F.
Notation up := Upset.emb.
