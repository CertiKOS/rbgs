Require Import Relations RelationClasses Relators.
Require Import List.
Require Import Coqlib.
Require Import LanguageInterface Events Globalenvs Smallstep.

Section Lifting.
  Variable abd: Type.
  Definition lifted_li li: language_interface :=
    {|
    query := query li * abd;
    reply := reply li * abd;
    entry '(q, _) := entry q
    |}.

  Context {liA liB state} (L: lts liA liB state).
  Let statex := (state * abd)%type.
  Let liBx := lifted_li liB.
  Let liAx := lifted_li liA.

  Inductive step' ge: statex -> trace -> statex -> Prop :=
  | step'_intro: forall s s' a t,
      step L ge s t s' ->
      step' ge (s, a) t (s', a).
  Inductive after_external': statex -> reply liAx -> statex -> Prop :=
  | after_external'_intro: forall s a r a' s',
      after_external L s r s' ->
      after_external' (s, a) (r, a') (s, a').

  Definition lifted_lts: lts liAx liBx statex :=
    {|
    genvtype := genvtype L;
    step ge := step' ge;
    valid_query := fun (q: query liBx) => valid_query L (fst q);
    initial_state := (initial_state L) * eq;
    at_external := fun s (q: query liAx) => ((at_external L) * eq) s q;
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
