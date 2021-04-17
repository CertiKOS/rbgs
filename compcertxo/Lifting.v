Require Import Relations RelationClasses Relators.
Require Import List.
Require Import Coqlib.
Require Import LanguageInterface Events Globalenvs Smallstep.

Section Lifting.
  Variable K: Type.
  Definition lifted_li li: language_interface :=
    {|
    query := query li * K;
    reply := reply li * K;
    entry '(q, _) := entry q
    |}.

  Context {liA liB state} (L: lts liA liB state).
  Let stateX := (state * K)%type.
  Let liBX := lifted_li liB.
  Let liAX := lifted_li liA.

  Inductive step' ge: stateX -> trace -> stateX -> Prop :=
  | step'_intro: forall s s' a t,
      step L ge s t s' ->
      step' ge (s, a) t (s', a).
  Inductive after_external': stateX -> reply liAX -> stateX -> Prop :=
  | after_external'_intro: forall s a r a' s',
      after_external L s r s' ->
      after_external' (s, a) (r, a') (s, a').

  Definition lifted_lts: lts liAX liBX stateX :=
    {|
    genvtype := genvtype L;
    step ge := step' ge;
    valid_query := fun (q: query liBX) => valid_query L (fst q);
    initial_state := (initial_state L) * eq;
    at_external := fun s (q: query liAX) => ((at_external L) * eq) s q;
    after_external s := (after_external L (fst s)) * eq;
    final_state := (final_state L) * eq;
    globalenv := globalenv L
    |}%rel.
End Lifting.

Delimit Scope li_scope with li.
Bind Scope li_scope with language_interface.
Delimit Scope lts_scope with lts.
Bind Scope lts_scope with lts.

(* Note since we are overloading the @ operator, the right associativity and
   precedence level will be inherited *)
Notation "li @ K" := (lifted_li K li): li_scope.
Notation "L @ K" := (lifted_lts K L): lts_scope.

Definition lifted_semantics {liA liB} (K: Type) (L: semantics liA liB) :=
  {|
  skel := skel L;
  activate se := (L se @ K)%lts;
  |}.

Delimit Scope sem_scope with sem.
Bind Scope sem_scope with semantics.
Notation "L @ K" := (lifted_semantics K L): sem_scope.

Notation " 'layer' K " := (Smallstep.semantics li_null (li_c @ K)) (at level 1).

(* Definition layer_sim {K1 K2: Type} (L1: layer K1) (L2: layer K2) *)
(*            (R: krel K1 K2) := forward_simulation 1 (kcc_ext R) L1 L2. *)

(* Section Layer_Lifting. *)
(*   Variable K: Type. *)
(*   Context {li state} (L: lts li_null li state). *)

(*   Definition lifted_lts_layer: lts li_null (li @ K) (state * K) := *)
(*     {| *)
(*     genvtype := genvtype L; *)
(*     step ge := step' K L ge; *)
(*     valid_query := fun (q: query (li @ K)) => valid_query L (fst q); *)
(*     initial_state := (initial_state L) * eq; *)
(*     at_external '(s, _) := at_external L s; *)
(*     after_external '(s, _) r '(s', _) := after_external L s r s'; *)
(*     final_state := (final_state L) * eq; *)
(*     globalenv := globalenv L *)
(*     |}%rel. *)
(* End Layer_Lifting. *)

(* Definition lifted_semantics_layer {li} (K: Type) (L: semantics li_null li) := *)
(*   {| *)
(*   skel := skel L; *)
(*   activate se := lifted_lts_layer K (L se); *)
(*   |}. *)

(* Notation "L @ K" := (lifted_semantics_layer K L): sem_scope. *)



(* TODO: move this to somewhere else *)
(* Definition lts_closed {liA liB} (L: Smallstep.semantics liA liB) := *)
(*   forall se s q, ~ (Smallstep.at_external (L se)) s q. *)

(* Lemma li_null_closed {li} (L: semantics li_null li): lts_closed L. *)
(* Proof. *)
(*   unfold lts_closed. *)
(*   intros. inversion q. *)
(* Qed. *)

(* Section LTS_CLOSED. *)

(*   Context {liA liB} (L: semantics liA liB). *)
(*   Context (HL: lts_closed L). *)

(*   Variable liX: language_interface. *)
(*   Definition lts' se: lts liX liB (state L) := *)
(*     {| *)
(*     genvtype := genvtype (L se); *)
(*     step ge := step (L se) ge; *)
(*     valid_query := valid_query (L se); *)
(*     initial_state := initial_state (L se); *)
(*     at_external := fun s q => False; *)
(*     after_external := fun q s r => False; *)
(*     final_state := final_state (L se); *)
(*     globalenv := globalenv (L se) *)
(*     |}. *)
(*   Definition closed_sem_conv := *)
(*     {| *)
(*     skel := skel L; *)
(*     activate se := lts' se; *)
(*     |}. *)

(*   (* TODO: proved equivalence *) *)
(* End LTS_CLOSED. *)
