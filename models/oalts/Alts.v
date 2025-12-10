Require Import interfaces.Category.
Require Import interfaces.Functor.
Require Import interfaces.Monads.
Require Import models.PosetBicartesian.
Require Import models.oalts.DownsetMonad.
Require Import models.oalts.AsyncEvent.
Require Import models.oalts.TimeFunctor.
Require Import models.oalts.TimeDownset.
Require Import models.oalts.LCoalg.

(** * Alternating Simulations (ALTS)

    We instantiate the labelled coalgebra framework with:
    - Labels: async events (posets with a lifting functor L(E) = 1 + E)
    - States: the Kleisli category of the Downset monad on Poset
    - Functor: the Time functor lifted via the distributive law

    An ALTS coalgebra (E, S, step) consists of:
    - E : a poset of events
    - S : a poset of states
    - step : S → D(L(E) × S) in the Kleisli category

    Morphisms are pairs (e, f) where e : E₁ → E₂ and f : S₁ → D(S₂)
    such that the simulation diagram commutes.
*)

(** The category of ALTS coalgebras *)
Module Alts := LCoalg PosetAsyncEvents DownsetMonad.Kl LiftedTimeFunctor.

(** Convenient notation for ALTS types *)
Module AltsNotation.
  (** An ALTS is a coalgebra: events, states, and a step function *)
  Definition alts := Alts.t.

  (** A homomorphism between ALTS *)
  Definition hom := Alts.m.

  (** The events of an ALTS *)
  Definition events (a : alts) : PosetAsyncEvents.t := Alts.labels a.

  (** The states of an ALTS *)
  Definition states (a : alts) : DownsetMonad.Kl.t := Alts.states a.

  (** The step function of an ALTS:
      step : S → D(L(E) × S) in the Kleisli category,
      which means step : S → D(D(L(E) × S)) = S → DD(L(E) × S) *)
  Definition step (a : alts) := Alts.step a.

  (** Build an ALTS from components *)
  Definition mk_alts := Alts.mk_coalg.

  (** Build a homomorphism from components *)
  Definition mk_hom := Alts.mk_coalg_mor.

  (** Identity homomorphism *)
  Definition id_hom := Alts.id.

  (** Composition of homomorphisms *)
  Definition compose_hom := @Alts.compose.
End AltsNotation.
