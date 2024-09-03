Require Import Classical.
Require Import ClassicalChoice.
Require Import FunctionalExtensionality.
Require Import PropExtensionality.
From coqrel Require Import LogicalRelations.
From structures Require Import Lattice Completion.
Require Import Coq.Logic.Classical.
Require Import Coq.Logic.ChoiceFacts.

Axiom dep_choice : DependentFunctionalChoice.

(** * Interface *)

(** The downset lattice over a poset is a free distributive completion
  with respect to join-distributive morphisms. We use it as an
  intermediate step in the construction of the free completely
  distributive lattice (see [Morris, 2005]), and it could be used to
  construct traditional strategy models defined as prefix-closed sets
  of plays (which only feature angelic nondeterminism). *)

Module Sup <: LatticeCategory.

  Class Morphism {L M : cdlattice} (f : L -> M) :=
    mor : forall {I} (x : I -> L), f (lsup x) = sup i, f (x i).

  Lemma mor_join `{Morphism} x y :
    f (x || y) = f x || f y.
  Proof.
    Local Transparent join. unfold join.
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
    apply ref_join in Hxy.
    rewrite <- Hxy, mor_join.
    apply join_ub_l.
  Qed.

  Lemma id_mor (L : cdlattice) :
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

  Lemma mor_bot `{Morphism} :
    f bot = bot.
  Proof.
    Local Transparent bot. unfold bot.
    rewrite (mor (f:=f)).
    apply antisymmetry; apply sup_lub; intros [ ].
  Qed.

End Sup.

(** The completion that satisfies join-dense and join-prime properties *)
Module Type JoinDensePrimeCompletion (LC: LatticeCategory) (CS: LatticeCompletionSpec LC).

  Axiom emb_join_dense:
    forall {C: poset} (x: CS.F C), x = sup {c : C | CS.emb c [= x}, CS.emb c.

  Axiom emb_join_prime:
    forall {C: poset} {I} c (x: I -> CS.F C), CS.emb c [= lsup x <-> exists i, CS.emb c [= x i.

End JoinDensePrimeCompletion.

Module MeetCompleteCompletion (LC: LatticeCategory) (CS: LatticeCompletionSpec LC)
       (C: JoinDensePrimeCompletion LC CS).

  Lemma emb_meet_complete {L: cdlattice} {I} (x: I -> L):
    CS.emb (inf i, x i) = inf i, CS.emb (x i).
  Proof.
    apply antisymmetry.
    - apply inf_iff. intros i.
      apply CS.emb_mor.
      eapply inf_at. reflexivity.
    - rewrite (C.emb_join_dense (inf i, CS.emb (x i))).
      apply sup_iff. intros [c Hc]. cbn.
      apply CS.emb_mor.
      apply inf_iff. intros i.
      rewrite inf_iff in Hc. specialize (Hc i).
      rewrite <- CS.emb_mor. apply Hc.
  Qed.

End MeetCompleteCompletion.

Module Type SupCompletion := LatticeCompletion Sup <+
                             JoinDensePrimeCompletion Sup <+
                             MeetCompleteCompletion Sup.

(** * Construction *)

(** Our construction is straightforward. We use predicate
  extensionality to prove antisymmetry, and the axiom of choice to
  prove distributivity. *)

Module Downset <: SupCompletion.

  Record downset {C : poset} :=
    {
      has : C -> Prop;
      closed x y : x [= y -> has y -> has x;
    }.

  Arguments downset : clear implicits.
  (*
  Definition F := downset.
   *)

  Local Obligation Tactic :=
    cbn; try solve [firstorder].

  Section DOWNSETS.
    Context {C : poset}.

    (** ** Partial order *)

    Program Definition Fpos : poset :=
      {|
        poset_carrier := downset C;
        ref x y := forall c, has x c -> has y c;
      |}.

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

    Program Definition F : cdlattice :=
      {|
      cdl_poset := Fpos;
      lsup I x := {| has c := exists i, has (x i) c |};
      linf I x := {| has c := forall i, has (x i) c |};
      |}.

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
      apply (antisymmetry (A := Fpos)); cbn.
      - firstorder.
      - intros. apply NNPP. intros contra.
        assert (X: forall i : I, exists j : J i, ~ has (x i j) c).
        {
          clear -contra.
          intros i.
          apply not_ex_all_not with (n:=i) in contra.
          apply not_all_ex_not in contra. apply contra.
        }
        clear contra.
        apply dep_choice in X. firstorder.
    Qed.

    (** ** Embedding *)

    Program Definition emb (c : C) : F :=
      {|
        has x := x [= c;
      |}.
    Next Obligation.
      intros c x y Hxy Hyc.
      etransitivity; eauto.
    Qed.

    Lemma emb_mor (c1 c2 : C) :
      emb c1 [= emb c2 <-> c1 [= c2.
    Proof.
      cbn. firstorder.
      - apply H. reflexivity.
      - etransitivity; eauto.
    Qed.

    Lemma emb_join_dense :
      forall x, x = sup {c : C | emb c [= x}, emb c.
    Proof.
      intros x. apply antisymmetry.
      - cbn. intros.
        eexists (exist _ _ _). cbn.
        reflexivity.
        Unshelve. cbn.
        intros. eapply closed; eauto.
      - now apply fsup_lub.
    Qed.

    Lemma emb_join_prime {I} c (x : I -> F) :
      emb c [= lsup x <-> exists i, emb c [= x i.
    Proof.
      split.
      - intros H. cbn in *.
        specialize (H c). edestruct H as [i Hi]. reflexivity.
        exists i. intros. eapply closed; eauto.
      - firstorder. eapply sup_at. eauto.
    Qed.

    (** ** Simulator *)

    Context {L: cdlattice}.

    Definition ext (f : C -> L) (x : F) : L :=
      sup {c : C | emb c [= x}, f c.

    Context {f : C -> L}.

    Instance ext_mor :
      Sup.Morphism (ext f).
    Proof.
      intros I x.
      apply antisymmetry.
      - apply sup_lub. intros [c Hc].
        edestruct Hc as [i Hi]; cbn; try reflexivity.
        apply emb_join_prime in Hc as [j Hc].
        apply (sup_at j). unfold ext.
        apply (fsup_at c); auto.
        reflexivity.
      - apply sup_lub. intros i. unfold ext.
        apply fsup_lub. intros c Hc.
        apply (fsup_ub c). eauto using @sup_at.
    Qed.

    Context `{Hf : !PosetMorphism f}.

    Lemma ext_ana :
      (forall x, ext f (emb x) = f x).
    Proof.
      intros x. unfold ext.
      apply antisymmetry.
      - apply sup_lub. intros [c Hc].
        rstep. apply emb_mor. assumption.
      - apply fsup_ub. reflexivity.
    Qed.

    Lemma ext_unique (g : F -> L) `{Hg : !Sup.Morphism g} :
      (forall x, g (emb x) = f x) -> forall x, g x = ext f x.
    Proof.
      intros Hgf x.
      rewrite (emb_join_dense x).
      unfold fsup. rewrite Sup.mor.
      unfold ext.
      apply antisymmetry.
      - apply sup_lub.
        intros (i & Hi). rewrite Hgf.
        eapply fsup_ub. cbn. intros.
        eexists (exist _ _ _). cbn. reflexivity.
        Unshelve. cbn. intros. apply Hi. cbn. etransitivity; eauto.
      - apply fsup_lub. intros.
        eapply sup_at. rewrite Hgf. instantiate (1 := exist _ _ _).
        rstep. cbn. reflexivity.
        Unshelve. cbn in *. intros.
        edestruct H as [[ ] ]. eauto. cbn in *. apply h. auto.
    Qed.

  End DOWNSETS.

  Arguments F : clear implicits.
  Include (LatticeCompletionDefs Sup).
  Include (MeetCompleteCompletion Sup).
End Downset.

Notation downset := Downset.F.
Notation down := Downset.emb.
