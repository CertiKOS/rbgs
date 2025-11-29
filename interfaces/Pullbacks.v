Require Import interfaces.Category.
Require Import interfaces.Functor.

(** * Pullbacks *)

(** ** Category with weak pullbacks *)
(** It might seem superfluos at first to define weak pullbacks first
  and then pullbacks. However, many relevant categorical properties only depend
  on the existence of weak pullbacks.

  For example, to show bisimulations in the Aczel-Mendler representation
  compose it is enough to compute a weak pullback.

  Moreover, sometimes in practice using a weak pullback allows one to choose
  a simpler representation for the pullback product.
*)

Module Type WeakPullbacksDefinition (C : CategoryDefinition).
  (* Here is the pullback diagram for reference:
    [pb_prod f g] ---- [pb_p2 f g] -----> [B]
        |                             |
        |                             |
        |                             |
    [pb_p1 f g]                         [g]
        |                             |
        |                             |
        |                             |
        V                             V
       [A] ------------- [f] -----------> [C]
  *)
  Parameter pb_prod :
    forall {A B C}, forall (f : C.m A C) (g : C.m B C), C.t.
  Parameter pb_p1 :
    forall {A B C}, forall (f : C.m A C) (g : C.m B C), C.m (pb_prod f g) A.
  Parameter pb_p2 :
    forall {A B C}, forall (f : C.m A C) (g : C.m B C), C.m (pb_prod f g) B.
  Parameter pb_pair :
    forall {A B C} {f : C.m A C} {g : C.m B C},
      forall {X : C.t} {ll : C.m X A} {lr : C.m X B},
        C.compose f ll = C.compose g lr -> C.m X (pb_prod f g).

  Axiom pb_square :
    forall {A B C}, forall (f : C.m A C) (g : C.m B C),
      C.compose  f (pb_p1 f g) = C.compose g (pb_p2 f g).
  Axiom pb_p1_pair :
    forall {A B C} {f : C.m A C} {g : C.m B C},
      forall {X : C.t} {ll : C.m X A} {lr : C.m X B}
        (sq : C.compose f ll = C.compose g lr),
        C.compose (pb_p1 f g) (pb_pair sq) = ll.
  Axiom pb_p2_pair :
    forall {A B C} {f : C.m A C} {g : C.m B C},
      forall {X : C.t} {ll : C.m X A} {lr : C.m X B}
        (sq : C.compose f ll = C.compose g lr),
        C.compose (pb_p2 f g) (pb_pair sq) = lr.
End WeakPullbacksDefinition.

Module Type WeakPullbacks (C : CategoryDefinition) :=
  WeakPullbacksDefinition C.

(** ** Category with pullbacks *)

(** A pullback is just a weak pullback for which pairings are uniquely defined *)

Module Type PullbacksDefinition (C : CategoryDefinition).
  Include (WeakPullbacksDefinition C).

  Axiom pb_pair_uni :
    forall {A B C} {f : C.m A C} {g : C.m B C},
      forall {X : C.t} {ll : C.m X A} {lr : C.m X B}
        (sq : C.compose f ll = C.compose g lr),
        forall {p : C.m X (pb_prod f g)},
          C.compose (pb_p1 f g) p = ll ->
          C.compose (pb_p2 f g) p = lr ->
          p = (pb_pair sq).
End PullbacksDefinition.

Module Type Pullbacks (C : CategoryDefinition) :=
  PullbacksDefinition C.