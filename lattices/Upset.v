Require Import Lattice.
Require Import Downset.
Require Import Dual.


(** * Interface *)

(** The upset lattice over a poset is a completely distributive
  completion that is meet dense and completely meet prime. We use it
  as an intermediate step in the construction of the free completely
  distributive lattice (see [Morris, 2005]). *)

Module Type UpsetSig.

  Parameter F : forall C `{Cpo : Poset C}, Type.
  Parameter lattice : forall `{Poset}, CDLattice (F C).
  Parameter up : forall `{Poset}, C -> F C.
  Existing Instance lattice.

  Axiom up_ref_emb :
    forall `{Poset} c1 c2, up c1 ⊑ up c2 <-> c1 ⊑ c2.

  Axiom up_dense :
    forall `{Poset} x, x = ⋀ {c | x ⊑ up c}; up c.

  Axiom up_prime :
    forall `{Poset} {I} c x, inf x ⊑ up c <-> exists i:I, x i ⊑ up c.

End UpsetSig.


(** * Construction *)

(** Instead of duplicating the [Downset] construction, we dualize it.
  XXX: we should finish the proofs in [Downset] first, and depending
  on their complexity either follow this approach, or copy-and-paste
  and remove Dual.v *)

Module Upset : UpsetSig.

  Definition F C `{Cpo : Poset C} := opp (downset (opp C)).
  Instance lattice : forall `{Poset}, CDLattice (F C) := _.
  Definition up `{Poset} (c : C) := oin (Downset.down (oin c)).

  Lemma up_ref_emb `{Poset} c1 c2 : up c1 ⊑ up c2 <-> c1 ⊑ c2.
  Proof.
    split; intro Hc.
    - rewrite <- ref_oin. apply Downset.down_ref_emb. apply Hc.
    - rewrite <- ref_oin. apply Downset.down_ref_emb. apply Hc.
  Qed.

  Lemma up_dense :
    forall `{Poset} x, x = ⋀ {c | x ⊑ up c}; up c.
  Proof.
  Admitted.

  Lemma up_prime :
    forall `{Poset} {I} c x, inf x ⊑ up c <-> exists i:I, x i ⊑ up c.
  Proof.
  Admitted.

End Upset.

Notation upset := Upset.F.
