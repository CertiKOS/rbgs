Require Import FunctionalExtensionality.
Require Import structures.Lattice.

Program Definition poset_prod {K : Type} (C : K -> poset) : poset :=
  {|
    poset_carrier := forall k, C k;
    ref x y := forall k, ref (x k) (y k);
  |}.

Next Obligation.
  split.
  - intros x k. reflexivity.
  - intros x y z Hxy Hyz k. etransitivity; eauto.
Qed.

Next Obligation.
  intros x y Hxy Hyx.
  apply functional_extensionality_dep. intros k.
  apply antisymmetry; eauto.
Qed.

Notation "'pi' i .. j , M" :=
  (poset_prod (fun i => .. (poset_prod (fun j => M%poset)) .. ))
  (at level 65, i binder, j binder, right associativity) : poset_scope.

Notation "C ^ K" := (pi k : K, C)%poset : poset_scope.

Program Definition cdlat_prod {K : Type} (L : K -> cdlattice) : cdlattice :=
  {|
    cdl_poset := poset_prod L;
    lsup I x k := lsup (fun i => x i k);
    linf I x k := linf (fun i => x i k);

    sup_ub I i x k := sup_ub i (fun i => x i k);
    sup_lub I x y H k := sup_lub (fun i => x i k) (y k) (fun i => H i k);
    inf_lb I i x k := inf_lb i (fun i => x i k);
    inf_glb I x y H k := inf_glb (x k) (fun i => y i k) (fun i => H i k);
  |}.

Next Obligation.
  apply functional_extensionality_dep. intros k.
  apply sup_inf.
Qed.

Notation "'pi' i .. j , M" :=
  (cdlat_prod (fun i => .. (cdlat_prod (fun j => M%cdlat)) .. ))
  (at level 65, i binder, j binder, right associativity) : cdlat_scope.

Notation "L ^ K" := (pi k : K, L)%cdlat : cdlat_scope.
