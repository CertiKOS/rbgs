Require Import FunctionalExtensionality.
Require Import Lattice.

Section PPROD.
  Context {I : Type} `{Poset}.

  Program Instance prod_poset : Poset (I -> C) :=
    {
      ref x y := forall i, ref (x i) (y i);
    }.

  Next Obligation.
    split.
    - intros x i. reflexivity.
    - intros x y z Hxy Hyz i. etransitivity; eauto.
  Qed.

  Next Obligation.
    intros x y Hxy Hyx.
    apply functional_extensionality. intros i.
    apply antisymmetry; eauto.
  Qed.
End PPROD.

Section LPROD.
  Context {K : Type} `{Ls : CDLattice}.

  Program Instance prod_lattice : CDLattice (K -> L) :=
    {
      cdl_poset := prod_poset;
      sup I x k := sup (fun i => x i k);
      inf I x k := inf (fun i => x i k);

      sup_ub I i x k := sup_ub i (fun i => x i k);
      sup_lub I x y H k := sup_lub (fun i => x i k) (y k) (fun i => H i k);
      inf_lb I i x k := inf_lb i (fun i => x i k);
      inf_glb I x y H k := inf_glb (x k) (fun i => y i k) (fun i => H i k);
    }.

  Next Obligation.
    apply functional_extensionality. intros k.
    apply sup_inf.
  Qed.
End LPROD.

Hint Extern 1 (CDLattice (_ -> _)) =>
  apply @prod_lattice : typeclass_instances.
