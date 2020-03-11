Require Import FunctionalExtensionality.
Require Import structures.Lattice.

Program Definition poset_prod (K : Type) (C : poset) : poset :=
  {|
    poset_carrier := K -> C;
    ref x y := forall k, ref (x k) (y k);
  |}.

Next Obligation.
  split.
  - intros x k. reflexivity.
  - intros x y z Hxy Hyz k. etransitivity; eauto.
Qed.

Next Obligation.
  intros x y Hxy Hyx.
  apply functional_extensionality. intros k.
  apply antisymmetry; eauto.
Qed.

Notation "C ^ K" := (poset_prod K C) : poset_scope.

Program Definition cdlat_prod (K : Type) (L : cdlattice) : cdlattice :=
  {|
    cdl_poset := poset_prod K L;
    lsup I x k := lsup (fun i => x i k);
    linf I x k := linf (fun i => x i k);

    sup_ub I i x k := sup_ub i (fun i => x i k);
    sup_lub I x y H k := sup_lub (fun i => x i k) (y k) (fun i => H i k);
    inf_lb I i x k := inf_lb i (fun i => x i k);
    inf_glb I x y H k := inf_glb (x k) (fun i => y i k) (fun i => H i k);
  |}.

Next Obligation.
  apply functional_extensionality. intros k.
  apply sup_inf.
Qed.

Notation "L ^ K" := (cdlat_prod K L) : cdlat_scope.
