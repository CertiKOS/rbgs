Require Import FunctionalExtensionality.
From coqrel Require Import LogicalRelations.
From structures Require Import Lattice Completion.
From lattices Require Import Downset.


(** * Interface *)

(** The upset lattice over a poset is a completely distributive
  completion that is meet dense and completely meet prime. We use it
  as an intermediate step in the construction of the free completely
  distributive lattice (see [Morris, 2005]). *)

Module Inf <: LatticeCategory.

  Class Morphism {L M : cdlattice} (f : L -> M) :=
    mor : forall {I} (x : I -> L), f (linf x) = inf i, f (x i).

  Lemma mor_meet `{Morphism} x y :
    f (x && y) = f x && f y.
  Proof.
    Local Transparent meet. unfold meet.
    rewrite (mor (f := f)). f_equal.
    apply functional_extensionality. intros b.
    destruct b; auto.
  Qed.

  Lemma mor_ref {L M : cdlattice} (f : L -> M) :
    Morphism f ->
    PosetMorphism f.
  Proof.
    intros Hf. split.
    intros x y Hxy.
    apply ref_meet in Hxy.
    rewrite <- Hxy, mor_meet.
    apply meet_lb_r.
  Qed.

  Lemma id_mor {L : cdlattice} :
    Morphism (fun x:L => x).
  Proof.
    red. auto.
  Qed.

  Lemma compose_mor {A B C : cdlattice} (g : B -> C) (f : A -> B) :
    Morphism f ->
    Morphism g ->
    Morphism (fun a => g (f a)).
  Proof.
    intros Hf Hg I x.
    rewrite (mor (f:=f)), (mor (f:=g)).
    reflexivity.
  Qed.

  Hint Immediate mor_ref : typeclass_instances.

End Inf.

Module Type MeetDensePrimeCompletion (LC: LatticeCategory) (CS: LatticeCompletionSpec LC).

  Axiom emb_meet_dense:
    forall {C: poset} (x: CS.F C), x = inf {c : C | x [= CS.emb c}, CS.emb c.

  Axiom emb_meet_prime:
    forall {C: poset} {I} c (x: I -> CS.F C), linf x [= CS.emb c <-> exists i, x i [= CS.emb c.

End MeetDensePrimeCompletion.

Module JoinCompleteCompletion (LC: LatticeCategory) (CS: LatticeCompletionSpec LC)
       (C: MeetDensePrimeCompletion LC CS).

  Lemma emb_join_complete {L: cdlattice} {I} (x: I -> L):
    CS.emb (sup i, x i) = sup i, CS.emb (x i).
  Proof.
    apply antisymmetry.
    - rewrite (C.emb_meet_dense (sup i, CS.emb (x i))).
      apply inf_iff. intros [c Hc]. cbn.
      apply CS.emb_mor.
      apply sup_iff. intros i.
      rewrite sup_iff in Hc. specialize (Hc i).
      rewrite <- CS.emb_mor. apply Hc.
    - apply sup_iff. intros i.
      apply CS.emb_mor.
      eapply sup_at. reflexivity.
  Qed.

End JoinCompleteCompletion.

Module Type InfCompletion := LatticeCompletion Inf <+
                             MeetDensePrimeCompletion Inf <+
                             JoinCompleteCompletion Inf.

(** * Construction *)

Module Upset : InfCompletion.

  (** ** Opposite order *)

  (** To avoid redundancies, we define the opposite order and lattice,
    and construct upsets by dualizing the [Downset] completion. This
    may or may not result in a lower complexity than copy-and-pasting,
    so we should evaluate once the [Downset] proofs are completed. *)

  Program Definition opp_poset (C : poset) : poset :=
    {|
      poset_carrier := C;
      ref x y := y [= x;
    |}.
  Next Obligation.
    split.
    - intros x. reflexivity.
    - intros x y z Hyz Hxy. etransitivity; eauto.
  Qed.
  Next Obligation.
    intros x y Hxy Hyx.
    apply antisymmetry; auto.
  Qed.

  Program Definition opp_cdlat (L : cdlattice) : cdlattice :=
    {|
      cdl_poset := opp_poset L;
      lsup I x := linf x;
      linf I x := lsup x;
    |}.
  Next Obligation. eapply (inf_lb i). Qed.
  Next Obligation. apply inf_glb; auto. Qed.
  Next Obligation. apply sup_ub; auto. Qed.
  Next Obligation. apply sup_lub; auto. Qed.
  Next Obligation. apply inf_sup. Qed.

  (*
  Definition opp_map {A B} (f : A -> B) : opp A -> opp B :=
    fun '(opp_in a) => opp_in (f a).

  Instance opp_map_ref {A B} `{Poset A} `{Poset B} (f : A -> B) :
    PosetMorphism f ->
    PosetMorphism (opp_map f).
  Proof.
    intros Hf. split. intros [x] [y] Hxy. cbn in *. rauto.
  Qed.
   *)

  (** ** Upsets *)

  Definition F (C : poset) := opp_cdlat (downset (opp_poset C)).

  Section DEFS.
    Context {C : poset}.

    Definition emb (c : C) : F C :=
      Downset.emb (c : opp_poset C).

    Lemma emb_mor c1 c2 : emb c1 [= emb c2 <-> c1 [= c2.
    Proof.
      split; intro Hc; cbn in *.
      - rewrite Downset.emb_mor in Hc. assumption.
      - rewrite Downset.emb_mor. assumption.
    Qed.

    Lemma emb_meet_dense :
      forall x, x = inf {c : C | x [= emb c }, emb c.
    Proof. apply @Downset.emb_join_dense. Qed.

    Lemma emb_meet_prime I c (x: I -> F C) :
      inf j, x j [= emb c <-> (exists i : I, x i [= emb c).
    Proof. apply @Downset.emb_join_prime. Qed.

    (** ** Simulator *)

    Context {L : cdlattice}.

    Definition ext (f : C -> L) (x : F C) : L :=
      Downset.ext (f : opp_poset C -> opp_cdlat L) (x : downset (opp_poset C)).

    Context {f : C -> L} `{Hf : !PosetMorphism f}.

    Instance ext_mor :
      Inf.Morphism (ext f).
    Proof.
      intros I x. unfold ext. cbn.
      rewrite Sup.mor. cbn. auto.
    Qed.

    Lemma ext_ana :
      (forall x, ext f (emb x) = f x).
    Proof.
      intros x. unfold ext, emb. cbn.
      rewrite @Downset.ext_ana. cbn. auto.
      firstorder.
    Qed.

    Lemma ext_unique (g : F C -> L) `{Hg : !Inf.Morphism g} :
      (forall x, g (emb x) = f x) -> forall x, g x = ext f x.
    Proof.
      intros Hgf x.
      unfold emb, ext in *. cbn in *.
      erewrite <- @Downset.ext_unique; eauto.
      firstorder.
    Qed.
  End DEFS.

  Include (LatticeCompletionDefs Inf).
  Include (JoinCompleteCompletion Inf).

End Upset.

Notation upset := Upset.F.
Notation up := Upset.emb.
