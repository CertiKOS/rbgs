Require Import interfaces.Category.
Require Import interfaces.ConcreteCategory.
Require Import interfaces.Functor.
Require Import interfaces.MonoidalCategory.
Require Import interfaces.Monads.
Require Import interfaces.Limits.
Require Import interfaces.LiftMonad.
Require Import models.DCPO.
Require Import models.PosetBicartesian.
Require Import models.oalts.DownsetMonad.
Require Import models.oalts.AsyncEvent.
Require Import models.oalts.TimeFunctor.
Require Import models.oalts.interfaces.LiftToKleisli.

(** * Distributive Law: Time Functor over Downset Monad *)

(** We establish a distributive law between the Time functor and the
    Downset monad on the category of posets. This allows us to lift
    the Time functor to the Kleisli category of the Downset monad.

    The distributive law is:
      λ : L(E) × D(S) → D(L(E) × S)

    Given (α, D) where α ∈ L(E) = 1 + E and D is a downset of S:
      λ(α, D) = {(α', s) | α' ≤ α ∧ s ∈ D}
*)

(** ** Setup: Extract Terminals from Poset's Cartesian Structure *)

Module PosetTerminals := TerminalsFromCartesian PosetBicartesian.C.

(** ** Async Events on Poset *)

Module PosetAsyncEvents := AsyncEventsDefinition PosetBicartesian PosetTerminals.

(** ** Time Functor for Poset *)

Module PosetTimeFunctor := TimeFunctor PosetBicartesian PosetTerminals PosetAsyncEvents.

(** ** Distributive Law Definition *)

Module TimeDownsetDistr <: BiDistributiveLaw
    PosetAsyncEvents PosetBicartesian DownsetMonad PosetTimeFunctor.

  Import Poset.
  Import DownsetMonadDef.
  Import coqrel.LogicalRelations.

  (** The distributive law λ : Time(E, D(S)) → D(Time(E, S))
      i.e., λ : L(E) × D(S) → D(L(E) × S)

      Given (α, D) where α ∈ L(E) and D is a downset of S:
        λ(α, D) = {(α', s) | α' ≤ α ∧ s ∈ D}
  *)

  Section DistrDef.
    Variable E : PosetAsyncEvents.t.
    Variable S : Poset.t.

    (* Object-level definitions *)
    Let LE_obj := PosetAsyncEvents.L.omap E.
    Let DS_obj := DownsetMonadDef.omap S.
    Let TimEDS_obj := PosetTimeFunctor.omap E DS_obj.
    Let TimES_obj := PosetTimeFunctor.omap E S.
    Let DTimES_obj := DownsetMonadDef.omap TimES_obj.

    (* Carrier-level definitions *)
    Let LE := Poset.carrier LE_obj.
    Let CarrierS := Poset.carrier S.

    (* Partial order structures *)
    Let POLE : DCPO.PartialOrder LE := Poset.structure LE_obj.
    Let POS : DCPO.PartialOrder CarrierS := Poset.structure S.
    Let POTimES : DCPO.PartialOrder (LE * CarrierS) := Poset.structure TimES_obj.

    (** The downward closure property for the output *)
    Definition distr_pred (α : LE) (D : @dset CarrierS POS) : (LE * CarrierS) -> Prop :=
      fun p => @le _ POLE (fst p) α /\ has D (snd p).

    Lemma distr_pred_closed (α : LE) (D : @dset CarrierS POS) :
      forall p1 p2 : LE * CarrierS,
        @le _ POTimES p1 p2 ->
        distr_pred α D p2 ->
        distr_pred α D p1.
    Proof.
      intros [α1 s1] [α2 s2] [Hα Hs] [Hα2 Hs2].
      unfold distr_pred. simpl in *.
      split.
      - eapply (@transitivity _ (@le _ POLE) _); eauto.
      - eapply (@closed CarrierS POS); eauto.
    Qed.

    Definition distr_fun (p : LE * @dset CarrierS POS) : @dset (LE * CarrierS) POTimES :=
      @mk_dset (LE * CarrierS) POTimES
        (distr_pred (fst p) (snd p))
        (distr_pred_closed (fst p) (snd p)).

    Lemma distr_mor :
      @Poset.Morphism _ _ (Poset.structure TimEDS_obj) (Poset.structure DTimES_obj) distr_fun.
    Proof.
      intros [α1 D1] [α2 D2] [Hα HD]. simpl in *.
      unfold dset_le. simpl. intros [α' s] [Hα' Hs].
      split.
      - eapply (@transitivity _ (@le _ POLE) _); eauto.
      - apply HD. exact Hs.
    Qed.
  End DistrDef.

  Program Definition distr (E : PosetAsyncEvents.t) (S : Poset.t) :
    Poset.m (PosetTimeFunctor.omap E (DownsetMonad.omap S))
            (DownsetMonad.omap (PosetTimeFunctor.omap E S)) :=
    @Poset.mkm _ _ (distr_fun E S) (distr_mor E S).

  (** ** Naturality in the first argument *)
  Proposition distr_natural_l :
    forall {E1 E2 : PosetAsyncEvents.t} (e : PosetAsyncEvents.m E1 E2) (S : Poset.t),
    Poset.compose (distr E2 S) (PosetTimeFunctor.fmap e (Poset.id (DownsetMonad.omap S))) =
    Poset.compose (DownsetMonad.fmap (PosetTimeFunctor.fmap e (Poset.id S))) (distr E1 S).
  Proof.
    intros E1 E2 e S.
    apply Poset.meq. intro p; destruct p as [α D].
    apply dset_eq. intro q; destruct q as [α' s].
    split; intro H.
    - simpl in H. destruct H as [Hα' Hs].
      simpl. exists (α, s). split.
      + split; [reflexivity | exact Hs].
      + simpl. split; [exact Hα' | reflexivity].
    - simpl in H. destruct H as [[α'' s'] [[Hα'' Hs'] [Hα' Hs]]].
      simpl. split.
      + eapply (@transitivity _ _ _ α' (PosetAsyncEvents.L.KlU.fmap e α'') _); auto.
        apply (Poset.morphism _ _ (PosetAsyncEvents.L.KlU.fmap e)). exact Hα''.
      + eapply (@closed _ (Poset.structure S)); eauto.
  Qed.

  (** ** Naturality in the second argument *)
  Proposition distr_natural_r :
    forall (E : PosetAsyncEvents.t) {S1 S2 : Poset.t} (f : Poset.m S1 S2),
    Poset.compose (distr E S2) (PosetTimeFunctor.fmap (PosetAsyncEvents.id E) (DownsetMonad.fmap f)) =
    Poset.compose (DownsetMonad.fmap (PosetTimeFunctor.fmap (PosetAsyncEvents.id E) f)) (distr E S1).
  Proof.
    intros E S1 S2 f.
    apply Poset.meq. intros p; destruct p as [α D].
    apply dset_eq. intros p; destruct p as [α' s2]. simpl.
    split.
    - intros [Hα' [s1 [Hs1 Hfs1]]].
      simpl. exists (α, s1).
      split; [split; [reflexivity | exact Hs1] |].
      simpl. split; [exact Hα' | exact Hfs1].
    - intros [[α'' s1] [H1 H2]].
      destruct H1 as [Hα'' Hs1]. destruct H2 as [Hα' Hs2].
      destruct α'' as [u'' | e'']; destruct α as [u | e]; destruct α' as [u' | e'];
        simpl in *; try contradiction.
      + split; auto. exists s1. split; auto.
      + split; auto.
        eapply (@transitivity _ _ _ e' e'' _); auto.
        exists s1. split; auto.
  Qed.

  (** ** Compatibility with unit: λ ∘ Time(id, η) = η *)
  Proposition distr_unit :
    forall (E : PosetAsyncEvents.t) (S : Poset.t),
    Poset.compose (distr E S) (PosetTimeFunctor.fmap (PosetAsyncEvents.id E) (DownsetMonad.eta S)) =
    DownsetMonad.eta (PosetTimeFunctor.omap E S).
  Proof.
    intros E S.
    apply Poset.meq. intros p; destruct p as [α s].
    apply dset_eq. intros p; destruct p as [α' s']. simpl.
    destruct α as [u | e]; destruct α' as [u' | e']; simpl;
      split; intros [H1 H2]; split; auto.
  Qed.

  (** ** Compatibility with multiplication: λ ∘ Time(id, μ) = μ ∘ D(λ) ∘ λ *)
  Proposition distr_mult :
    forall (E : PosetAsyncEvents.t) (S : Poset.t),
    Poset.compose (distr E S) (PosetTimeFunctor.fmap (PosetAsyncEvents.id E) (DownsetMonad.mu S)) =
    Poset.compose (DownsetMonad.mu (PosetTimeFunctor.omap E S))
      (Poset.compose (DownsetMonad.fmap (distr E S)) (distr E (DownsetMonad.omap S))).
  Proof.
    intros E S.
    apply Poset.meq. intros p; destruct p as [α DD].
    apply dset_eq. intros p; destruct p as [α' s]. simpl.
    destruct α as [u | e]; destruct α' as [u' | e']; simpl.
    - split.
      + intros [Hα' [D [HDD Hs]]].
        set (POTimES := Poset.structure (PosetTimeFunctor.omap E S)).
        set (POLE := Poset.structure (PosetAsyncEvents.L.omap E)).
        assert (Hclosed : forall p1 p2 : PosetAsyncEvents.L.omap E * S,
          @le _ POTimES p1 p2 ->
          (@le _ POLE (fst p2) (inl u) /\ has D (snd p2)) ->
          (@le _ POLE (fst p1) (inl u) /\ has D (snd p1))).
        { intros [a1 b1] [a2 b2] [Ha Hb] [Ha2 Hb2]. simpl in *.
          split; [eapply (@transitivity _ (@le _ POLE) _ a1 a2 _); auto |
                  eapply (@closed _ (Poset.structure S)); eauto]. }
        set (D' := @mk_dset _ POTimES (fun p => @le _ POLE (fst p) (inl u) /\ has D (snd p)) Hclosed).
        exists D'. split.
        * exists (inl u, D). split.
          { split; [reflexivity | exact HDD]. }
          { simpl. intros [a b] [Ha Hb]. split; [exact Ha | exact Hb]. }
        * simpl. split; [exact Hα' | exact Hs].
      + intros [D' [[[α1 D1] [[Hα1 HD1] HD']] Hin]].
        simpl in *.
        specialize (HD' (inl u', s) Hin).
        destruct HD' as [Hα'_le Hs'].
        split.
        * eapply (@transitivity _ _ _ (inl u') α1 _); eauto.
        * exists D1. split; [exact HD1 | exact Hs'].
    - split; intros H.
      + destruct H as [Hcontra _]. simpl in Hcontra. destruct Hcontra.
      + destruct H as [D' [[[α1 D1] [[Hα1 _] HD']] Hin]].
        simpl in *. specialize (HD' (inr e', s) Hin).
        destruct α1 as [u1 | e1]; simpl in *; [|contradiction].
        destruct HD' as [Hcontra _]. destruct Hcontra.
    - split; intros H.
      + destruct H as [Hcontra _]. simpl in Hcontra. destruct Hcontra.
      + destruct H as [D' [[[α1 D1] [[Hα1 _] HD']] Hin]].
        simpl in *. specialize (HD' (inl u', s) Hin).
        destruct α1 as [u1 | e1]; simpl in *; [contradiction|].
        destruct HD' as [Hcontra _]. destruct Hcontra.
    - split.
      + intros [Hα' [D [HDD Hs]]].
        set (POTimES := Poset.structure (PosetTimeFunctor.omap E S)).
        set (POLE := Poset.structure (PosetAsyncEvents.L.omap E)).
        assert (Hclosed : forall p1 p2 : PosetAsyncEvents.L.omap E * S,
          @le _ POTimES p1 p2 ->
          (@le _ POLE (fst p2) (inr e) /\ has D (snd p2)) ->
          (@le _ POLE (fst p1) (inr e) /\ has D (snd p1))).
        { intros [a1 b1] [a2 b2] [Ha Hb] [Ha2 Hb2]. simpl in *.
          split; [eapply (@transitivity _ (@le _ POLE) _ a1 a2 _); auto |
                  eapply (@closed _ (Poset.structure S)); eauto]. }
        set (D' := @mk_dset _ POTimES (fun p => @le _ POLE (fst p) (inr e) /\ has D (snd p)) Hclosed).
        exists D'. split.
        * exists (inr e, D). split.
          { split; [reflexivity | exact HDD]. }
          { simpl. intros [a b] [Ha Hb]. split; [exact Ha | exact Hb]. }
        * simpl. split; [exact Hα' | exact Hs].
      + intros [D' [[[α1 D1] [[Hα1 HD1] HD']] Hin]].
        simpl in *.
        specialize (HD' (inr e', s) Hin).
        destruct HD' as [Hα'_le Hs'].
        split.
        * eapply (@transitivity _ _ _ (inr e') α1 _); eauto.
        * exists D1. split; [exact HD1 | exact Hs'].
  Qed.

End TimeDownsetDistr.

(** ** The Lifted Time Functor to Kleisli(Downset) *)

Module LiftedTimeFunctor :=
  LiftBifunctorToKleisli PosetAsyncEvents PosetBicartesian DownsetMonad
    PosetTimeFunctor TimeDownsetDistr.