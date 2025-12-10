Require Import interfaces.Category.
Require Import interfaces.ConcreteCategory.
Require Import interfaces.Monads.
Require Import models.DCPO.
Require Import FunctionalExtensionality.
Require Import PropExtensionality.
Require Import ProofIrrelevance.
Require Import coqrel.LogicalRelations.

(** * The Downset (Possibility) Monad *)

(** The downset construction forms a monad on the category of posets.

    - Objects: posets (using the ConcreteCategory structure from DCPO.v)
    - Morphisms: monotone maps
    - M X = Downset X (downward-closed subsets of X)
    - eta_X : X -> MX sends x to the principal downset
    - mu_X : MMX -> MX is the union
*)

(** ** Downset structure on Poset objects *)

Section DownsetConstruction.
  Variable P : Type.
  Variable PO : DCPO.PartialOrder P.

  (** A downset is a downward-closed predicate *)
  Record dset :=
    mk_dset {
      has : P -> Prop;
      closed : forall x y, x [= y -> has y -> has x;
    }.

  (** Partial order on downsets by inclusion *)
  Definition dset_le (D1 D2 : dset) : Prop :=
    forall x, has D1 x -> has D2 x.

  Lemma dset_le_preo : PreOrder dset_le.
  Proof.
    constructor.
    - intros D x H. exact H.
    - intros D1 D2 D3 H12 H23 x H1. apply H23, H12, H1.
  Qed.

  Lemma dset_le_po : Antisymmetric dset eq dset_le.
  Proof.
    intros [h1 c1] [h2 c2] H12 H21. simpl in *.
    assert (h1 = h2) as Heq.
    { apply functional_extensionality. intros z.
      apply propositional_extensionality.
      split; [apply H12 | apply H21]. }
    subst. f_equal. apply proof_irrelevance.
  Qed.

  Instance dset_PO : DCPO.PartialOrder dset :=
    {| le := dset_le;
       le_preo := dset_le_preo;
       le_po := dset_le_po |}.

  (** Principal downset *)
  Definition emb (p : P) : dset :=
    {| has := fun y => y [= p;
       closed := fun a b Hab Hbp => transitivity Hab Hbp |}.

End DownsetConstruction.

Arguments dset P {_}.
Arguments mk_dset {P _}.
Arguments has {P _}.
Arguments emb {P _}.
Arguments dset_PO {P _}.

(** Union of downsets *)
Section DownsetMu.
  Variable P : Type.
  Variable PO : DCPO.PartialOrder P.

  Definition mu (DD : @dset (dset P) dset_PO) : dset P.
  Proof.
    refine (@mk_dset P PO (fun z => exists D, has DD D /\ has D z) _).
    intros a b Hab [D [HDD HD]].
    exists D. split; auto.
    eapply closed; eauto.
  Defined.

End DownsetMu.

Arguments mu {P _}.

(** ** Downset Monad Definition *)

Module DownsetMonadDef <: MonadDefinition Poset.
  Import Poset.

  (** Object map: X -> Downset X *)
  Definition omap (X : Poset.t) : Poset.t :=
    @Poset.mkt (dset X) (@dset_PO _ (Poset.structure X)).

  (** fmap: direct image with downward closure *)
  Section FmapDef.
    Variables X Y : Poset.t.
    Variable f : Poset.m X Y.

    Let POX : DCPO.PartialOrder X := Poset.structure X.
    Let POY : DCPO.PartialOrder Y := Poset.structure Y.
    Let dset_POX : DCPO.PartialOrder (@dset _ POX) := @dset_PO _ POX.
    Let dset_POY : DCPO.PartialOrder (@dset _ POY) := @dset_PO _ POY.

    Let ff (x : X) : Y := @Poset.apply X Y f x.

    Definition fmap_fun_aux (D : @dset _ POX) : @dset _ POY.
    Proof.
      refine (@mk_dset _ POY (fun y => exists x, has D x /\ y [= (ff x)) _).
      intros y1 y2 Hy [a [Ha Hy1]].
      exists a. split; auto.
      etransitivity; eauto.
    Defined.

    Lemma fmap_mor_aux : @Poset.Morphism _ _ dset_POX dset_POY fmap_fun_aux.
    Proof.
      intros D1 D2 HD. simpl.
      intros y [a [Ha Hy]].
      exists a. split; auto.
    Qed.
  End FmapDef.

  Definition fmap {X Y : Poset.t} (f : Poset.m X Y) : Poset.m (omap X) (omap Y) :=
    @Poset.mkm (omap X) (omap Y) (fmap_fun_aux X Y f) (fmap_mor_aux X Y f).

  (** Unit: eta *)
  Section EtaDef.
    Variable X : Poset.t.
    Let POX : DCPO.PartialOrder X := Poset.structure X.
    Let dset_POX : DCPO.PartialOrder (@dset _ POX) := @dset_PO _ POX.

    Lemma eta_mor_aux : @Poset.Morphism _ _ POX dset_POX emb.
    Proof.
      intros x y Hxy. unfold dset_le. simpl.
      intros z Hz. simpl in Hz.
      exact (@transitivity _ (@le _ POX) _ z x y Hz Hxy).
    Qed.
  End EtaDef.

  Definition eta (X : Poset.t) : Poset.m X (omap X) :=
    @Poset.mkm X (omap X) emb (eta_mor_aux X).

  (** Multiplication: mu *)
  Section MuDef.
    Variable X : Poset.t.
    Let POX : DCPO.PartialOrder (Poset.carrier X) := Poset.structure X.
    Let dset_POX : DCPO.PartialOrder (@dset _ POX) := @dset_PO _ POX.
    Let dset_dset_POX : DCPO.PartialOrder (@dset (@dset _ POX) dset_POX) := @dset_PO _ dset_POX.

    Lemma mu_mor_aux : @Poset.Morphism _ _ dset_dset_POX dset_POX (@mu _ POX).
    Proof.
      intros DD1 DD2 HDD. simpl.
      intros x [D [HD1 Hx]].
      exists D. split; auto.
    Qed.
  End MuDef.

  Definition mu (X : Poset.t) : Poset.m (omap (omap X)) (omap X) :=
    @Poset.mkm (omap (omap X)) (omap X) mu (mu_mor_aux X).

  (** Helper lemma for equality of downsets *)
  Lemma dset_eq {P} `{PO: DCPO.PartialOrder P} (D1 D2 : dset P) :
    (forall x, has D1 x <-> has D2 x) -> D1 = D2.
  Proof.
    intros Heq.
    apply (@antisymmetry _ eq _ (@dset_le P PO) (@dset_le_po P PO));
      intros x Hx; apply Heq; auto.
  Qed.

  (** Functor laws *)
  Proposition fmap_id : forall X, fmap (Poset.id X) = Poset.id (omap X).
  Proof.
    intros X. apply Poset.meq. intros D.
    apply dset_eq. intros y. simpl.
    split.
    - intros H. destruct H as [x [Hx Hy]].
      eapply closed; eauto.
    - intros Hy. exists y. split. exact Hy.
      apply (@reflexivity _ (@le _ (Poset.structure X)) _).
  Qed.

  Proposition fmap_compose : forall {X Y Z} (g : Poset.m Y Z) (f : Poset.m X Y),
    fmap (Poset.compose g f) = Poset.compose (fmap g) (fmap f).
  Proof.
    intros X Y Z g f. apply Poset.meq. intros D.
    apply dset_eq. intros z. simpl.
    split.
    - intros H. destruct H as [x [Hx Hz]].
      exists (@Poset.apply X Y f x). split.
      + exists x. split. exact Hx.
        apply (@reflexivity _ (@le _ (Poset.structure Y)) _).
      + exact Hz.
    - intros H. destruct H as [y [Hy Hz]]. destruct Hy as [x [Hx Hxy]].
      exists x. split. exact Hx.
      eapply (@transitivity _ (@le _ (Poset.structure Z)) _); eauto.
      apply (Poset.morphism Y Z g). exact Hxy.
  Qed.

  (** Naturality of eta *)
  Proposition eta_natural {X Y} (f : Poset.m X Y) :
    Poset.compose (eta Y) f = Poset.compose (fmap f) (eta X).
  Proof.
    apply Poset.meq. intros x.
    apply dset_eq. intros y. simpl.
    split.
    - intros Hy. exists x. split; [reflexivity | exact Hy].
    - intros [x' [Hx' Hy]].
      simpl in Hx'.
      eapply (@transitivity _ _ _ y (@Poset.apply X Y f x') (@Poset.apply X Y f x)); eauto.
      apply (Poset.morphism X Y f). exact Hx'.
  Qed.

  (** Naturality of mu *)
  Proposition mu_natural {X Y} (f : Poset.m X Y) :
    Poset.compose (mu Y) (fmap (fmap f)) = Poset.compose (fmap f) (mu X).
  Proof.
    apply Poset.meq. intros DD.
    apply dset_eq. intros y.
    split.
    - simpl. intros H.
      destruct H as [D' H1]. destruct H1 as [H1a H1b].
      destruct H1a as [D H1a']. destruct H1a' as [HDD HD'incl].
      specialize (HD'incl y H1b).
      destruct HD'incl as [x Hx'].
      destruct Hx' as [Hx Hy].
      exists x. split; [| exact Hy].
      exists D; split; [exact HDD | exact Hx].
    - simpl. intros H.
      destruct H as [x H'].
      destruct H' as [Hmid Hy].
      destruct Hmid as [D0 Hmid'].
      destruct Hmid' as [HDD0 HD0x].
      assert (Hclosed : forall y1 y2 : Y,
                @le _ (Poset.structure Y) y1 y2 ->
                (exists a, has D0 a /\ @le _ (Poset.structure Y) y2 (@Poset.apply X Y f a)) ->
                (exists a, has D0 a /\ @le _ (Poset.structure Y) y1 (@Poset.apply X Y f a))).
      { intros y1 y2 Hy1 Hy2.
        destruct Hy2 as [a Ha'].
        destruct Ha' as [Ha Hy2'].
        exists a. split; auto.
        eapply (@transitivity _ (@le _ (Poset.structure Y)) _); eauto. }
      set (D' := @mk_dset Y (Poset.structure Y)
            (fun z => exists a, has D0 a /\ @le _ (Poset.structure Y) z (@Poset.apply X Y f a)) Hclosed).
      exists D'. split.
      + exists D0. split; auto.
        simpl. intros z Hz.
        destruct Hz as [a Ha'].
        destruct Ha' as [Ha Hz'].
        exists a. split; auto.
      + simpl. exists x. split; auto.
  Qed.

  (** Left unit law *)
  Proposition mu_eta_l X :
    Poset.compose (mu X) (eta (omap X)) = Poset.id (omap X).
  Proof.
    apply Poset.meq. intros D.
    apply dset_eq. intros x. simpl.
    split.
    - intros H.
      destruct H as [D' [HD' Hx]].
      apply HD'. exact Hx.
    - intros Hx.
      exists D. split.
      + intros y Hy. exact Hy.
      + exact Hx.
  Qed.

  (** Right unit law *)
  Proposition mu_eta_r X :
    Poset.compose (mu X) (fmap (eta X)) = Poset.id (omap X).
  Proof.
    apply Poset.meq. intros D.
    apply dset_eq. intros x. simpl.
    split.
    - intros H.
      destruct H as [D' [Hex Hx]]. destruct Hex as [x' [Hx' Hle]].
      simpl in Hle. eapply closed; eauto.
      apply Hle. exact Hx.
    - intros Hx.
      exists (emb x). split.
      + exists x. split.
        * exact Hx.
        * intros z Hz. exact Hz.
      + simpl. apply (@reflexivity _ (@le _ (Poset.structure X)) _).
  Qed.

  (** Associativity *)
  Proposition mu_mu X :
    Poset.compose (mu X) (mu (omap X)) = Poset.compose (mu X) (fmap (mu X)).
  Proof.
    apply Poset.meq. intros DDD.
    apply dset_eq. intros x. simpl.
    split.
    - intros H.
      destruct H as [DD [Hex1 HDDx]].
      destruct Hex1 as [DD' [HDDD' HDD'DD]].
      exists DD. split.
      + exists DD'. split. exact HDDD'.
        simpl. intros z Hz.
        exists DD. split; [exact HDD'DD | exact Hz].
      + exact HDDx.
    - intros H.
      destruct H as [D' [Hex HD'x]]. destruct Hex as [DD [HDDD Hle]].
      specialize (Hle x HD'x). destruct Hle as [D0 [HDD_D0 HD0x]].
      exists D0. split.
      + exists DD. split; [exact HDDD | exact HDD_D0].
      + exact HD0x.
  Qed.

End DownsetMonadDef.

(** ** Full Downset Monad with Kleisli category *)

Module DownsetMonad := MonadTheory Poset DownsetMonadDef.

(** Convenient aliases *)
Notation "'dset'" := DownsetMonadDef.omap.
Notation "'dset'" := DownsetMonadDef.fmap.
