Require Import interfaces.Category.
Require Import interfaces.MonoidalCategory.
Require Import interfaces.Limits.
Require Import interfaces.LiftMonad.

(** * Asynchronous Events *)

(** Asynchronous events are either a visible event or an invisible event. *)
(** This is nicely captured by the Kleisli category of the lift monad. *)

Module AsyncEventsDefinition (C : CocartesianCategory) (T : Terminals C) <: Category.
  Module L := LiftMonad C T.
  Include L.Kl.
End AsyncEventsDefinition.

Module Type AsyncEvents (C : CocartesianCategory) (T : Terminals C).
  Include (AsyncEventsDefinition C T).
End AsyncEvents.
