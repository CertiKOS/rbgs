Require Import RelationClasses.
Require Import Lattice.

(** Below we define the opposite poset and opposite lattice, which we
  use to avoid redundancy and define the upset lattice as the dual of
  the downset lattice. *)

Inductive opp (A : Type) := oin { oout : A }.
Arguments oout {A} _.
Arguments oin {A} _.

Program Instance opp_poset `(Poset) : Poset (opp C) | 5 :=
  {
    ref x y := oout y ⊑ oout x
  }.

Next Obligation.
  split.
  - intros x. reflexivity.
  - intros x y z Hxy Hyz. etransitivity; eauto.
Qed.

Next Obligation.
  intros [x] [y] Hxy Hyx.
  f_equal. apply antisymmetry; auto.
Qed.

Lemma ref_oout `{Poset} (x y : opp C) :
  oout x ⊑ oout y <-> y ⊑ x.
Proof.
  destruct x, y. reflexivity.
Qed.

Lemma ref_oin `{Poset} (x y : C) :
  oin x ⊑ oin y <-> y ⊑ x.
Proof.
  reflexivity.
Qed.

Program Instance opp_lattice `(CDLattice) : CDLattice (opp L) :=
  {
    sup I x := oin (inf (fun i => oout (x i)));
    inf I x := oin (sup (fun i => oout (x i)));
  }.

Next Obligation.
  apply (inf_lb (fun i => oout (x i))).
Qed.

Next Obligation.
  apply inf_glb; auto.
Qed.

Next Obligation.
  apply (sup_ub (fun i => oout (x i))).
Qed.

Next Obligation.
  apply sup_lub; auto.
Qed.

Next Obligation.
  f_equal. apply inf_sup.
Qed.
