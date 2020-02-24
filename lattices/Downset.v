Require Import coqrel.LogicalRelations.
Require Import Classical.
Require Import ClassicalChoice.
Require Import FunctionalExtensionality.
Require Import PropExtensionality.

Require Import Lattice.
Require Import Completion.


(** * Interface *)

(** The downset lattice over a poset is a free distributive completion
  with respect to join-distributive morphisms. We use it as an
  intermediate step in the construction of the free completely
  distributive lattice (see [Morris, 2005]), and it could be used to
  construct traditional strategy models defined as prefix-closed sets
  of plays (which only feature angelic nondeterminism). *)

Module Sup <: LatticeCategory.
  Class Morphism {L M} `{CDLattice L} `{CDLattice M} (f : L -> M) :=
    mor : forall {I} (x : I -> L), f (sup x) = ⋁ i; f (x i).
End Sup.


(** * Construction *)

(** Our construction is straightforward. We use predicate
  extensionality to prove antisymmetry, and the axiom of choice to
  prove distributivity. *)

Module Downset : LatticeCompletion Sup.

  Record downset {C} `{Cpo : Poset C} :=
    {
      has : C -> Prop;
      closed x y : x ⊑ y -> has y -> has x;
    }.

  Arguments downset C {Cpo}.
  Definition F C `{Poset C} := downset C.

  Local Obligation Tactic :=
    cbn; try solve [firstorder].

  Section DOWNSETS.
    Context {C} `{Cpo : Poset C}.

    (** ** Partial order *)

    Program Instance poset : Poset (downset C) | 5 :=
      {
        ref x y := forall c, has x c -> has y c;
      }.

    Next Obligation.
      intros [x Hx] [y Hy]. unfold ref. cbn. intros Hxy Hyz.
      assert (x = y).
      {
        apply functional_extensionality. intros c.
        apply propositional_extensionality. firstorder.
      }
      subst. f_equal. apply proof_irrelevance.
    Qed.

    (** ** Distributive lattice *)

    Program Instance lattice : CDLattice (downset C) :=
      {
        sup I x := {| has c := exists i, has (x i) c |};
        inf I x := {| has c := forall i, has (x i) c |};
      }.

    (** [sup] is downward closed. *)
    Next Obligation.
      intros I x c1 c2 Hc [i H2].
      eauto using @closed.
    Qed.

    (** [inf] is downward closed. *)
    Next Obligation.
      intros I x c1 c2 Hc H2 i.
      eauto using @closed.
    Qed.

    (** Distributivity. *)
    Next Obligation.
      intros.
      apply antisymmetry; cbn.
      - firstorder.
      - admit.
    Admitted.

    (** ** Embedding *)

    Program Definition emb (c : C) :=
      {|
        has x := x ⊑ c;
      |}.
    Next Obligation.
      intros c x y Hxy Hyc.
      etransitivity; eauto.
    Qed.

    Lemma emb_mor c1 c2 :
      emb c1 ⊑ emb c2 <-> c1 ⊑ c2.
    Proof.
      cbn. firstorder.
      etransitivity; eauto.
    Qed.

    Lemma emb_join_dense :
      forall x, x = ⋁{c : C | emb c ⊑ x}; emb c.
    Admitted.

    Lemma emb_join_prime {I} c (x : I -> downset C) :
      emb c ⊑ sup x <-> exists i, emb c ⊑ x i.
    Admitted.

    (** ** Simulator *)

    Context `{Lcd : CDLattice}.

    Definition ext (f : C -> L) (x : downset C) : L :=
      ⋁{ c | emb c ⊑ x }; f c.

    Context {f : C -> L} `{Hf : Monotonic f ((⊑) ++> (⊑))}.

    Instance ext_mor :
      Sup.Morphism (ext f).
    Proof.
      intros I x.
      apply antisymmetry.
      - apply sup_lub. intros [c Hc].
        edestruct Hc as [i Hi]; cbn; try reflexivity.
        apply emb_join_prime in Hc as [j Hc].
        apply (sup_at j). unfold ext.
        apply (psup_at c); auto.
        reflexivity.
      - apply sup_lub. intros i. unfold ext.
        apply psup_lub. intros c Hc.
        apply (psup_ub c). eauto using @sup_at.
    Qed.

    Lemma ext_ana :
      (forall x, ext f (emb x) = f x).
    Proof.
      intros x. unfold ext.
      apply antisymmetry.
      - apply sup_lub. intros [c Hc].
        rstep. apply emb_mor. assumption.
      - admit. (* version of sup_ub with predicate *)
    Admitted.

    Lemma ext_unique (g : F C -> L) `{Hg : !Sup.Morphism g} :
      (forall x, g (emb x) = f x) -> forall x, g x = ext f x.
    Proof.
      intros Hgf x.
      rewrite (emb_join_dense x), Sup.mor.
      unfold ext.
      (* maybe use emb_join_prime *)
    Admitted.

  End DOWNSETS.

  Include (LatticeCompletionDefs Sup).

End Downset.

Notation downset := Downset.F.
Notation down := Downset.emb.
