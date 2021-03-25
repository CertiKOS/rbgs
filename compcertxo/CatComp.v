Require Import Relations RelationClasses Relators.
Require Import List.
Require Import Coqlib.
Require Import LanguageInterface Events Globalenvs Smallstep.

Section CAT_COMP.
  Context {li} (L1 L2: semantics li li).

  Section WITH_SE.
    Context (se: Genv.symtbl).
    Variant state :=
    | st1 (s: Smallstep.state L1)
    | st2 (s1: Smallstep.state L1) (s2: Smallstep.state L2).

    Inductive step: state -> trace -> state -> Prop :=
    | step1 s1 t s1':
        Step (L1 se) s1 t s1' ->
        step (st1 s1) t (st1 s1')
    | step2 s1 s2 t s2':
        Step (L2 se) s2 t s2' ->
        step (st2 s1 s2) t (st2 s1 s2')
    | step_push s1 q s2:
        Smallstep.at_external (L1 se) s1 q ->
        valid_query (L2 se) q = true ->
        Smallstep.initial_state (L2 se) q s2 ->
        step (st1 s1) E0 (st2 s1 s2)
    | step_pop s1 r s2 s1':
        Smallstep.final_state (L2 se) s2 r ->
        Smallstep.after_external (L1 se) s1 r s1' ->
        step (st2 s1 s2) E0 (st1 s1').

    Inductive initial_state (q: query li): state -> Prop :=
    | initial_state_intro s:
        valid_query (L1 se) q = true ->
        Smallstep.initial_state (L1 se) q s ->
        initial_state q (st1 s).

    Inductive at_external: state -> query li -> Prop :=
    | at_external_intro s1 s2 q:
        valid_query (L2 se) q = false ->
        Smallstep.at_external (L2 se) s2 q ->
        at_external (st2 s1 s2) q.

    Inductive after_external: state -> reply li -> state -> Prop :=
    | after_external_intro s1 s2 r s2':
        Smallstep.after_external (L2 se) s2 r s2' ->
        after_external (st2 s1 s2) r (st2 s1 s2').

    Inductive final_state: state -> reply li -> Prop :=
    | final_state_intro s r:
        Smallstep.final_state (L1 se) s r ->
        final_state (st1 s) r.

  End WITH_SE.

  Context (sk: AST.program unit unit).

  Definition semantics: semantics li li :=
    {|
    activate se :=
      {|
        Smallstep.step ge := step se;
        Smallstep.valid_query q := valid_query (L1 se) q || valid_query (L2 se) q;
        Smallstep.initial_state := initial_state se;
        Smallstep.at_external := at_external se;
        Smallstep.after_external := after_external se;
        Smallstep.final_state := final_state se;
        Smallstep.globalenv := tt;
        (* Genv.globalenv se p *)
      |};
    skel := sk;
    |}.

End CAT_COMP.

Require Import SmallstepLinking.

Arguments st1 {_ _ _}.
Arguments st2 {_ _ _}.

Section APPROX.
  Context {li} (L1 L2: Smallstep.semantics li li).
  Notation L := (fun i => match i with true => L1 | false => L2 end).
  Hypothesis one_way_query: forall se q,
      Smallstep.valid_query (L2 se) q = false ->
      Smallstep.valid_query (L1 se) q = false.

  Inductive state_match: state L1 L2 -> list (SmallstepLinking.frame L) -> Prop :=
  | state_match1 s:
      state_match (st1 s) (st L true s :: nil)
  | state_match2 s1 s2:
      state_match (st2 s1 s2) (st L false s2 :: st L true s1 :: nil).

  Context (sk: AST.program unit unit).

  Lemma catcomp_approx: forward_simulation 1 1 (Top.semantics L1 L2 sk)
                                           (SmallstepLinking.semantics L sk).
  Proof.
    constructor. econstructor; eauto.
    instantiate (1 := fun _ _ _ => _). cbn beta.
    intros se ? [ ] [ ] Hsk.
    apply forward_simulation_step with (match_states := state_match).
    - intros q ? [ ]. reflexivity.
    - intros q ? s1 [ ] Hq.
      inv Hq. exists (st L true s :: nil).
      split; constructor; auto.
    - intros s1 s2 r Hs Hr.
      inv Hr. inv Hs. exists r.
      split; constructor; auto.
    - intros s1 s2 q Hs Hq.
      inv Hq. inv Hs.
      exists tt. exists q. repeat apply conj; try constructor; auto.
      + intros j. destruct j; auto.
      + intros r1 ? s1' [ ] Hr.
        inv Hr. exists (st L false s2' :: st L true s0 :: nil).
        split; constructor; auto.
    - intros sx t sx' Hstep sy Hs.
      inv Hstep; inv Hs.
      + exists (st L true s1' :: nil).
        split; constructor; auto.
      + exists (st L false s2' :: st L true s1 :: nil).
        split; constructor; auto.
      + exists (st L false s2 :: st L true s1 :: nil).
        split; econstructor; eauto.
      + exists (st L true s1' :: nil).
        split; econstructor; eauto.
    - apply well_founded_ltof.
  Qed.
End APPROX.
