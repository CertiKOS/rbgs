Require Import Lattice.
Require Import Downset.
Require Import Dual.


(** * Interface *)

(** The upset lattice over a poset is a completely distributive
  completion that is meet dense and completely meet prime. We use it
  as an intermediate step in the construction of the free completely
  distributive lattice (see [Morris, 2005]). *)

Module Type UpsetSig.
  Include LatticeCompletion.

  Axiom emb_meet_dense :
    forall `{Poset} x, x = ⋀ {c | x ⊑ emb c}; emb c.

  Axiom emb_meet_prime :
    forall `{Poset} {I} c x, inf x ⊑ emb c <-> exists i:I, x i ⊑ emb c.

End UpsetSig.


(** * Construction *)

(** Instead of duplicating the [Downset] construction, we dualize it.
  XXX: we should finish the proofs in [Downset] first, and depending
  on their complexity either follow this approach, or copy-and-paste
  and remove Dual.v *)

Module Upset : UpsetSig.

  Definition F C `{Cpo : Poset C} := opp (downset (opp C)).
  Instance lattice : forall `{Poset}, CDLattice (F C) := _.
  Definition emb `{Poset} (c : C) := oin (Downset.down (oin c)).

  Lemma ref_emb `{Poset} c1 c2 : emb c1 ⊑ emb c2 <-> c1 ⊑ c2.
  Proof.
    split; intro Hc.
    - rewrite <- ref_oin. apply Downset.ref_emb. apply Hc.
    - rewrite <- ref_oin. apply Downset.ref_emb. apply Hc.
  Qed.

  Lemma emb_meet_dense :
    forall `{Poset} x, x = ⋀ {c | x ⊑ emb c}; emb c.
  Proof.
  Admitted.

  Lemma emb_meet_prime :
    forall `{Poset} {I} c x, inf x ⊑ emb c <-> exists i:I, x i ⊑ emb c.
  Proof.
  Admitted.

End Upset.

Notation upset := Upset.F.
Notation up := Upset.emb.
