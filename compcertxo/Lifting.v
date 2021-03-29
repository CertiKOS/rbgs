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

Require Import Memory Values.

Definition no_perm_on (m: mem) (vars: block -> Z -> Prop): Prop :=
  forall b ofs, vars b ofs -> ~ Mem.perm m b ofs Max Nonempty.

Record krel {K1 K2: Type}: Type :=
  mk_krel {
      Rk: K1 -> K2 -> Prop;
      Rm: K1 -> mem -> Prop;
      G: block -> Z -> Prop;

      G_unchanged:
        forall k m1 m2,
          Rm k m1 -> Mem.unchanged_on G m1 m2 -> Rm k m2;
    }.
Arguments krel: clear implicits.

Section SIM_REL.
  Context {K1 K2} (R: krel K1 K2).

  Inductive kcc_ext_query: query (li_c @ K1) -> query (li_c @ K2) -> Prop :=
  | kcc_query_intro vf sg vargs1 vargs2 m1 m2 k1 k2:
      Val.lessdef_list vargs1 vargs2 ->
      Mem.extends m1 m2 ->
      vf <> Vundef -> Rk R k1 k2 -> Rm R k1 m2 ->
      no_perm_on m1 (G R) ->
      kcc_ext_query (cq vf sg vargs1 m1, k1) (cq vf sg vargs2 m2, k2).

  Inductive kcc_ext_reply: reply (li_c @ K1) -> reply (li_c @ K2) -> Prop :=
  | kcc_ext_reply_intro vres1 vres2 m1 m2 k1 k2:
      Val.lessdef vres1 vres2 ->
      Mem.extends m1 m2 ->
      Rk R k1 k2 -> Rm R k1 m2 ->
      no_perm_on m1 (G R) ->
      kcc_ext_reply (cr vres1 m1, k1) (cr vres2 m2, k2).

  Program Definition kcc_ext :=
    {|
    ccworld := unit;
    match_senv w := eq;
    match_query w := kcc_ext_query;
    match_reply w := kcc_ext_reply;
    |}.

End SIM_REL.

Module Ksim.
  Record ksim {K1 K2: Type} :=
    mk_ksim {
        L1: Smallstep.semantics li_null (li_c @ K1);
        L2: Smallstep.semantics li_null (li_c @ K2);
        R: krel K1 K2;

        layer_sim: forward_simulation 1 (kcc_ext R) L1 L2;
      }.
  Arguments ksim: clear implicits.
End Ksim.

Definition lts_closed {liA liB} (L: semantics liA liB) :=
  forall se s q, ~ (at_external (L se)) s q.

Lemma li_null_closed {li} (L: semantics li_null li): lts_closed L.
Proof.
  unfold lts_closed.
  intros. inversion q.
Qed.

Section LTS_CLOSED.

  Context {liA liB} (L: semantics liA liB).
  Context (HL: lts_closed L).

  Variable liX: language_interface.
  Definition lts' se: lts liX liB (state L) :=
    {|
    genvtype := genvtype (L se);
    step ge := step (L se) ge;
    valid_query := valid_query (L se);
    initial_state := initial_state (L se);
    at_external := fun s q => False;
    after_external := fun q s r => False;
    final_state := final_state (L se);
    globalenv := globalenv (L se)
    |}.
  Definition closed_sem_conv :=
    {|
    skel := skel L;
    activate se := lts' se;
    |}.

  (* TODO: proved equivalence *)
End LTS_CLOSED.

Require Import Clight.
Require Import CatComp.
Require Import Linking.

Definition layer_combine {K} (M: Clight.program)
           (L: Smallstep.semantics li_null (li_c @ K)) sk :=
  let L' := CatComp.semantics (semantics1 M @ K) (closed_sem_conv L (li_c @ K)) sk
  in closed_sem_conv L' li_null.


Record prog_ksim {K1 K2: Type} :=
  mk_prog_ksim {
      L1: Smallstep.semantics li_null (li_c @ K1);
      L2: Smallstep.semantics li_null (li_c @ K2);
      M: Clight.program;
      R: krel K1 K2;
      sk: AST.program unit unit;

      layer_sim: forward_simulation 1 (kcc_ext R) L1 (layer_combine M L2 sk);
      link_sk: link (skel (semantics1 M)) (skel L2) = Some sk;
    }.

Section PROG_SIM.
  Context {K1 K2} (pksim: @prog_ksim K1 K2).
  Program Definition prog_sim_coercion: @Ksim.ksim K1 K2 :=
    {|Ksim.L1 := L1 pksim;
      Ksim.L2 := layer_combine (M pksim) (L2 pksim) (sk pksim);
      Ksim.R := R pksim; |}.
  Next Obligation.
    exact (layer_sim pksim).
  Qed.
End PROG_SIM.
Coercion prog_sim_coercion : prog_ksim >-> Ksim.ksim.

Require Import FlatComp.
