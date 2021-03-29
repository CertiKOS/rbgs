Require Import Relations RelationClasses Relators.
Require Import List.
Require Import Coqlib.
Require Import LanguageInterface Events Globalenvs SmallstepLinking Smallstep.

Section FLAT_COMP.
  Context {li} (L1 L2: semantics li li).

  Section WITH_SE.
    Context (se: Genv.symtbl).
    Variant state := | st1 (s: Smallstep.state L1) | st2 (s: Smallstep.state L2).

    Inductive step: state -> trace -> state -> Prop :=
    | step1 s t s':
        Step (L1 se) s t s' -> step (st1 s) t (st1 s')
    | step2 s t s':
        Step (L2 se) s t s' -> step (st2 s) t (st2 s').

    Inductive initial_state (q: query li): state -> Prop :=
    | initial_state1 s:
        valid_query (L1 se) q = true ->
        Smallstep.initial_state (L1 se) q s ->
        initial_state q (st1 s)
    | initial_state2 s:
        valid_query (L2 se) q = true ->
        Smallstep.initial_state (L2 se) q s ->
        initial_state q (st2 s).

    Inductive at_external: state -> query li -> Prop :=
    | at_external1 s q:
        valid_query (L1 se) q = false ->
        Smallstep.at_external (L1 se) s q ->
        at_external (st1 s) q
    | at_external2 s q:
        valid_query (L2 se) q = false ->
        Smallstep.at_external (L2 se) s q ->
        at_external (st2 s) q.

    Inductive after_external: state -> reply li -> state -> Prop :=
    | after_external1 s r s':
        Smallstep.after_external (L1 se) s r s' ->
        after_external (st1 s) r (st1 s')
    | after_external2 s r s':
        Smallstep.after_external (L2 se) s r s' ->
        after_external (st2 s) r (st2 s').

    Inductive final_state: state -> reply li -> Prop :=
    | final_state1 s r:
        Smallstep.final_state (L1 se) s r ->
        final_state (st1 s) r
    | final_state2 s r:
        Smallstep.final_state (L2 se) s r ->
        final_state (st2 s) r.
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

  Notation L := (fun i => match i with true => L1 | false => L2 end).

  Hypothesis zero_way_query: forall se q,
      xorb (Smallstep.valid_query (L true se) q)
           (Smallstep.valid_query (L false se) q) = false.

  Lemma zero_way_query1 se q:
    Smallstep.valid_query (L true se) q = false ->
    Smallstep.valid_query (L false se) q = false.
  Proof.
    cbn in *. specialize (zero_way_query se q).
    destruct (Smallstep.valid_query _ _);
      destruct (Smallstep.valid_query _ _);
      easy.
  Qed.

  Lemma zero_way_query2 se q:
    Smallstep.valid_query (L false se) q = false ->
    Smallstep.valid_query (L true se) q = false.
  Proof.
    cbn in *. specialize (zero_way_query se q).
    destruct (Smallstep.valid_query _ _);
      destruct (Smallstep.valid_query _ _);
      easy.
  Qed.

  Inductive state_match: state -> list (SmallstepLinking.frame L) -> Prop :=
  | state_match1 s:
      state_match (st1 s) (st L true s :: nil)
  | state_match2 s:
      state_match (st2 s) (st L false s :: nil).

  Lemma catcomp_approx: forward_simulation 1 1 semantics (SmallstepLinking.semantics L sk).
  Proof.
    constructor. econstructor; eauto.
    instantiate (1 := fun _ _ _ => _). cbn beta.
    intros se ? [ ] [ ] Hsk.
    apply forward_simulation_step with (match_states := state_match).
    - intros q ? [ ]. reflexivity.
    - intros q ? s1 [ ] Hq.
      inv Hq; eexists;
        split; constructor; auto.
    - intros s1 s2 r Hs Hr.
      inv Hr; inv Hs; exists r;
        split; constructor; auto.
    - intros s1 s2 q Hs Hq.
      inv Hq; inv Hs.
      + exists tt. exists q. repeat apply conj; try constructor; auto.
        intros j. destruct j; auto. apply zero_way_query1; auto.
        intros r1 ? s1' [ ] Hr.
        inv Hr. exists (st L true s' :: nil).
        split; constructor; auto.
      + exists tt. exists q. repeat apply conj; try constructor; auto.
        intros j. destruct j; auto. apply zero_way_query2; auto.
        intros r1 ? s1' [ ] Hr.
        inv Hr. exists (st L false s' :: nil).
        split; constructor; auto.
    - intros sx t sx' Hstep sy Hs.
      inv Hstep; inv Hs;
        eexists; split; constructor; auto.
    - apply well_founded_ltof.
  Qed.
End FLAT_COMP.

