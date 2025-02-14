From coqrel Require Import LogicalRelations.
From structures Require Import Lattice Completion.
From lattices Require Import Downset Upset.


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

Import FunctionalExtensionality.

(* FIXME: there is a duplicate one in IntSpec.v *)
Instance bigop_eq {I A B} (f : (I -> A) -> B) :
  Proper (pointwise_relation I eq ==> eq) f.
Proof.
  intros x y Hxy.
  apply functional_extensionality in Hxy.
  congruence.
Qed.

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
      unfold ext. split.
      - set (df := Downset.ext f).
        set (udf := Upset.ext df).
        intros I x.
        (* FIXME: is there a way to avoid manual eta-expansion? *)
        replace x with (fun i => x i) by reflexivity.
        setoid_rewrite (fun i => (Upset.emb_meet_dense (x i))) at 1.
        unfold finf. rewrite sup_inf.
        unfold udf. rewrite @Upset.ext_mor. fold udf.
        (* Lemma 3 in the FCD paper *)
        assert (forall (x: I -> downset C), udf (sup i, up (x i)) = sup i, udf (up (x i))).
        {
          intros y. unfold udf, df.
          rewrite <- Upset.emb_join_complete.
          setoid_rewrite Upset.ext_ana.
          rewrite <- Downset.ext_mor. reflexivity.
        }
        setoid_rewrite H. clear H.
        setoid_rewrite <- sup_inf with (x:=fun (i: I) p => udf (up (proj1_sig p))).
        unfold udf. setoid_rewrite <- @Upset.ext_mor. fold udf.
        setoid_rewrite <- Upset.emb_meet_dense.
        reflexivity.
      - apply Upset.ext_mor.
      Qed.

    Lemma ext_ana :
      (forall x, ext f (emb x) = f x).
    Proof.
      intros x. unfold ext, emb.
      rewrite @Upset.ext_ana.
      apply Downset.ext_ana.
      typeclasses eauto.
    Qed.

    Lemma ext_unique (g : F C -> L) `{!CDL.Morphism g} :
      (forall x, g (emb x) = f x) -> forall x, g x = ext f x.
    Proof.
      unfold emb, ext. intros Hg x.
      apply @Upset.ext_unique. typeclasses eauto. typeclasses eauto.
      apply @Downset.ext_unique. typeclasses eauto. 2: auto.
      destruct H. intros I p.
      rewrite Upset.emb_join_complete.
      rewrite H. reflexivity.
    Qed.

  End DEF.

  Include (LatticeCompletionDefs CDL).

  Lemma meet_join_dense {C : poset} (x : F C) :
    exists I J c, x = inf i : I, sup j : J i, emb (c i j).
  Proof.
    Local Opaque downset.
    exists {S : downset C | x [= up S}.
    exists (fun i => {c : C | down c [= proj1_sig i}).
    exists (fun i j => proj1_sig j).
    rewrite (Upset.emb_meet_dense x) at 1.
    unfold finf. apply bigop_eq. intros [S HS]. cbn.
    unfold emb. rewrite <- Upset.emb_join_complete. f_equal.
    rewrite (Downset.emb_join_dense S) at 1.
    unfold fsup. apply bigop_eq. intros [c Hc]. cbn. reflexivity.
  Qed.

  Lemma join_meet_dense {C : poset} (x : F C) :
    exists I J c, x = sup i : I, inf j : J i, emb (c i j).
  Proof.
    destruct (meet_join_dense x) as (I & J & c & Hx).
    rewrite inf_sup in Hx.
    exists (forall i, J i), (fun _ => I), (fun f i => c i (f i)).
    assumption.
  Qed.

End FCD.

(** Theorems from the paper: Dually Nondeterministic Functions [Morris, 08]  *)

Lemma theorem_5_2_1 {C: poset} (t: FCD.F C):
  t = sup I, sup { c | inf (i: I), FCD.emb (c i) [= t }, inf i, FCD.emb (c i).
Proof.
  edestruct (FCD.join_meet_dense t) as (I' & J & x & Ht).
  rewrite Ht. apply antisymmetry.
  - apply sup_iff. intros i'.
    apply (sup_at {i: unit & J i'}).
    eapply (fsup_at (fun '(existT _ i j) => x i' j)).
    + apply (sup_at i').
      apply inf_iff. intros j.
      apply (inf_at (existT _ tt j)).
      reflexivity.
    + apply inf_iff. intros (? & j).
      apply (inf_at j). reflexivity.
  - apply sup_iff. intros I.
    apply sup_iff. intros (c & Hc). apply Hc.
Qed.

Lemma theorem_5_2_2 {C: poset} (t: FCD.F C):
  t = inf I, inf { c | t [= sup (i: I), FCD.emb (c i) }, sup i, FCD.emb (c i).
Proof.
  edestruct (FCD.meet_join_dense t) as (I' & J & x & Ht).
  rewrite Ht. apply antisymmetry.
  - apply inf_iff. intros I.
    apply inf_iff. intros (c & Hc). apply Hc.
  - apply inf_iff. intros i'.
    apply (inf_at {i: unit & J i'}).
    eapply (finf_at (fun '(existT _ i j) => x i' j)).
    + apply (inf_at i').
      apply sup_iff. intros j.
      apply (sup_at (existT _ tt j)).
      reflexivity.
    + apply sup_iff. intros (? & j).
      apply (sup_at j). reflexivity.
Qed.

Lemma theorem_5_3_1 {C: poset} {t u: FCD.F C}:
  t [= u <-> forall { I } (c: I -> C), inf i , FCD.emb (c i) [= t -> inf i, FCD.emb (c i) [= u.
Proof.
  split; intros.
  - etransitivity; eauto.
  - rewrite (theorem_5_2_1 t).
    rewrite (theorem_5_2_1 u).
    apply sup_iff. intros I. apply (sup_at I).
    apply sup_iff. intros (c & Hc). cbn.
    eapply (fsup_at c); eauto. reflexivity.
Qed.

Lemma theorem_5_3_2 {C: poset} {t u: FCD.F C}:
  t [= u <-> forall { I } (c: I -> C), u [= sup i, FCD.emb (c i) -> t [= sup i, FCD.emb (c i).
Proof.
  split; intros.
  - etransitivity; eauto.
  - rewrite (theorem_5_2_2 t).
    rewrite (theorem_5_2_2 u).
    apply inf_iff. intros I. apply (inf_at I).
    apply inf_iff. intros (c & Hc). cbn.
    eapply (finf_at c); eauto. reflexivity.
Qed.
