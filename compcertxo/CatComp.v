Require Import Relations RelationClasses Relators.
Require Import List.
Require Import Coqlib.
Require Import LanguageInterface Events Globalenvs SmallstepLinking Smallstep.

(* Note that in a more general setting, the categorical composition takes two
   transition systems A ↠ B and B ↠ C and returns A ↠ C. Moreover, we'd like
   effect signature to replace the valid_query predicate to better handle the
   domain. Right now, valid_query q = true means q will invoke transitions and
   valid_query q = false means q will be treated as an external call during
   transition.  The problem here is that the two kinds queries are not
   mutually exclusive *)

Module CAT_COMP.
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
          (* Don't check the domain. Otherwise it can't call into identity
             component, which has empty domain *)
          (* valid_query (L2 se) q = true -> *)
          (* How to understand this? The condition is required by escaping
             calls *)
          valid_query (L1 se) q = false ->
          Smallstep.initial_state (L2 se) q s2 ->
          step (st1 s1) E0 (st2 s1 s2)
      | step_pop s1 r s2 s1':
          Smallstep.final_state (L2 se) s2 r ->
          Smallstep.after_external (L1 se) s1 r s1' ->
          step (st2 s1 s2) E0 (st1 s1').

      Inductive initial_state (q: query li): state -> Prop :=
      | initial_state_intro s:
          (* For the same reason as above *)
          (* valid_query (L1 se) q = true -> *)
          Smallstep.initial_state (L1 se) q s ->
          initial_state q (st1 s).

      Inductive at_external: state -> query li -> Prop :=
      | at_external_intro s1 s2 q:
          (* Escaping calls *)
          valid_query (L2 se) q = false ->
          valid_query (L1 se) q = false ->
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

  Section Property.
    Context (sk sk1 sk2: AST.program unit unit).
    Context {li} (L1 L2 L3: Smallstep.semantics li li).

    Arguments st1 {_ _ _} _.
    Arguments st2 {_ _ _} _ _.

    Inductive state_match1: state (semantics L1 L2 sk1) L3 ->
                            state L1 (semantics L2 L3 sk2) ->
                            Prop :=
    | st_match1 s:
        state_match1 (@st1 _ (semantics L1 L2 sk1) _ (st1 s)) (st1 s)
    | st_match2 s1 s2:
        state_match1 (@st1 _ (semantics L1 L2 sk1) _ (st2 s1 s2)) (@st2 _ _ (semantics L2 L3 sk2) s1 (st1 s2))
    | st_match3 s1 s2 s3:
        state_match1 (@st2 _ (semantics L1 L2 sk1) _ (st2 s1 s2) s3) (@st2 _ _ (semantics L2 L3 sk2) s1 (st2 s2 s3)).

    Lemma catcomp_assoc1: forward_simulation
                            1 1
                            (semantics (semantics L1 L2 sk1) L3 sk)
                            (semantics L1 (semantics L2 L3 sk2) sk).
    Proof.
      constructor. econstructor; auto.
      instantiate (1 := fun _ _ _ => _). cbn beta.
      intros se ? [ ] [ ] Hsk.
      apply forward_simulation_step with (match_states := state_match1).
      - intros q ? [ ]. cbn.
        now rewrite orb_assoc.
      - intros s1 s2 r Hs Hr. inv Hr. inv Hs. inv H.
        eexists. split. constructor. eauto. constructor.
      - intros s1 s2 r Hs Hf. inv Hf. inv H. inv Hs.
        eexists. split. constructor. eauto. constructor.
      - intros s1 s2 q Hs He. inv He. inv Hs.
        eexists _, _. apply orb_false_elim in H0 as [? ?].
        repeat apply conj.
        + econstructor.
          cbn. erewrite H2. rewrite H. reflexivity.
          rewrite H0. reflexivity.
          constructor; auto.
        + constructor.
        + constructor.
        + intros r1 r2 s1' Hr Ha.
          inv Hr. inv Ha.
          eexists. split.
          constructor. constructor. eauto. constructor.
      - intros s1 t s1' Hstep s2 Hs.
        inv Hstep.
        + inv H.
          * inv Hs. eexists. split.
            constructor. eauto. constructor.
          * inv Hs. eexists. split.
            constructor. constructor. eauto. constructor.
          * inv Hs. eexists. split.
            eapply step_push; eauto. constructor. eauto.
            constructor.
          * inv Hs. eexists. split.
            eapply step_pop; eauto. constructor. eauto.
            constructor.
        + inv Hs. eexists. split.
          eapply step2. eapply step2. eauto. constructor.
        + inv H. inv Hs. eexists.
          split. econstructor. eapply step_push; eauto.
          constructor.
        + inv H0. inv Hs. eexists.
          split. econstructor. eapply step_pop; eauto.
          constructor.
      - apply well_founded_ltof.
        Unshelve. exact tt.
    Qed.

    Lemma catcomp_assoc2: forward_simulation
                            1 1
                            (semantics L1 (semantics L2 L3 sk2) sk)
                            (semantics (semantics L1 L2 sk1) L3 sk).
    Proof.
      constructor. econstructor; auto.
      instantiate (1 := fun _ _ _ => _). cbn beta.
      intros se ? [ ] [ ] Hsk.
      apply forward_simulation_step with
          (match_states := fun s1 s2 => state_match1 s2 s1).
      - intros q ? [ ]. cbn.
        now rewrite orb_assoc.
      - intros q1 q2 s Hq Hi. inv Hi. inv Hq.
        eexists. split. constructor. constructor. eauto. constructor.
      - intros s1 s2 r Hs Hf. inv Hf. inv Hs.
        eexists. split. constructor. constructor. eauto. constructor.
      - intros s1 s2 q Hs He. inv He. inv H1. inv Hs.
        eexists _, _. apply orb_false_elim in H as [? ?].
        repeat apply conj.
        + econstructor; eauto. cbn. rewrite H0. easy.
        + constructor.
        + constructor.
        + intros r1 r2 s1' Hr Ha.
          inv Hr. inv Ha. inv H9.
          eexists. split.
          constructor. eauto. constructor.
      - intros s1 t s1' Hstep s2 Hs.
        inv Hstep.
        + inv Hs. eexists. split.
          apply step1. apply step1. eauto.
          constructor.
        + inv H.
          * inv Hs. eexists. split.
            constructor. apply step2. eauto.
            constructor.
          * inv Hs. eexists. split.
            constructor. eauto. constructor.
          * inv Hs. eexists. split.
            eapply step_push. constructor.

            inv H.
          * inv Hs. eexists. split.
            constructor. eauto. constructor.
          * inv Hs. eexists. split.
            constructor. constructor. eauto. constructor.
          * inv Hs. eexists. split.
            eapply step_push; eauto. constructor. eauto.
            constructor.
          * inv Hs. eexists. split.
            eapply step_pop; eauto. constructor. eauto.
            constructor.
        + inv Hs. eexists. split.
          eapply step2. eapply step2. eauto. constructor.
        + inv H. inv Hs. eexists.
          split. econstructor. eapply step_push; eauto.
          constructor.
        + inv H0. inv Hs. eexists.
          split. econstructor. eapply step_pop; eauto.
          constructor.
      - apply well_founded_ltof.
        Unshelve. exact tt.
    Qed.

  End Property.

  Notation L := (fun i => match i with true => L1 | false => L2 end).
  Hypothesis one_way_query: forall se q,
      Smallstep.valid_query (L2 se) q = false ->
      Smallstep.valid_query (L1 se) q = false.

  Inductive state_match: state -> list (SmallstepLinking.frame L) -> Prop :=
  | state_match1 s:
      state_match (st1 s) (st L true s :: nil)
  | state_match2 s1 s2:
      state_match (st2 s1 s2) (st L false s2 :: st L true s1 :: nil).

  Lemma catcomp_approx: forward_simulation 1 1 semantics (SmallstepLinking.semantics L sk).
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
  End CAT_COMP.
End CAT_COMP.

(* This is a special case of categorical composition, where the first component
   is a closed transition system *)
Section LAYER_COMP.
  Context {li} (L1: semantics li li) (L2: semantics li_null li).

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

    Inductive at_external: state -> query li_null -> Prop :=
    | at_external_intro s1 s2 q:
        (* valid_query (L2 se) q = false -> *)
        (* This should be empty *)
        Smallstep.at_external (L2 se) s2 q ->
        at_external (st2 s1 s2) q.

    Inductive after_external: state -> reply li_null -> state -> Prop :=
    | after_external_intro s1 s2 r s2':
        (* This should be empty *)
        Smallstep.after_external (L2 se) s2 r s2' ->
        after_external (st2 s1 s2) r (st2 s1 s2').

    Inductive final_state: state -> reply li -> Prop :=
    | final_state_intro s r:
        Smallstep.final_state (L1 se) s r ->
        final_state (st1 s) r.

  End WITH_SE.

  Context (sk: AST.program unit unit).

  Definition layer_comp: semantics li_null li :=
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

  Lemma star_internal1 se s t s':
    Star (L1 se) s t s' ->
    star (fun _ => step se) tt (st1 s) t (st1 s').
  Proof.
    induction 1; [eapply star_refl | eapply star_step]; eauto.
    constructor; auto.
  Qed.

  Lemma star_internal2 se s1 s t s':
    Star (L2 se) s t s' ->
    star (fun _ => step se) tt (st2 s1 s) t (st2 s1 s').
  Proof.
    induction 1; [eapply star_refl | eapply star_step]; eauto.
    constructor; auto.
  Qed.

  Lemma plus_internal1 se s t s':
    Plus (L1 se) s t s' ->
    plus (fun _ => step se) tt (st1 s) t (st1 s').
  Proof.
    destruct 1; econstructor; eauto using step1, star_internal1.
  Qed.

  Lemma plus_internal2 se s1 s t s':
    Plus (L2 se) s t s' ->
    plus (fun _ => step se) tt (st2 s1 s) t (st2 s1 s').
  Proof.
    destruct 1; econstructor; eauto using step2, star_internal2.
  Qed.

(* TODO: prove that layer composition is equivalent to categorical composition
  provided the bottom layer is closed *)
End LAYER_COMP.

Section LAYER_COMP_SIM.
  Context {li cc} (L1 L1': semantics li li)
          (HL1: fsim_components cc cc L1 L1').
  Context (L2 L2': semantics li_null li)
          (HL2: fsim_components 1 cc L2 L2').

  Variant index :=
  | index1: fsim_index HL1 -> index
  | index2: fsim_index HL1 -> fsim_index HL2 -> index.

  Variant order: index -> index -> Prop :=
  | order1 i1 i1':
      fsim_order HL1 i1 i1' ->
      order (index1 i1) (index1 i1')
  | order2 i1 i1' i2 i2' :
      fsim_order HL2 i2 i2' ->
      order (index2 i1 i2) (index2 i1' i2').

  Context (se se': Genv.symtbl) (w : ccworld cc).
  Context (Hse: match_senv cc w se se').
  Context (Hse1: Genv.valid_for (skel L1) se).
  Context (Hse2: Genv.valid_for (skel L2) se).

  Variant match_states: index -> state L1 L2 -> state L1' L2' -> Prop :=
  | match_states1 i s1 s1':
      match_senv cc w se se' ->
      fsim_match_states HL1 se se' w i s1 s1' ->
      match_states (index1 i) (st1 L1 L2 s1) (st1 L1' L2' s1')
  | match_states2 i i' w' s1 s1' s2 s2':
      match_senv cc w se se' ->
      match_senv cc w' se se' ->
      fsim_match_states HL2 se se' w' i' s2 s2' ->
      (forall r r' st1, match_reply cc w' r r' ->
                   Smallstep.after_external (L1 se) s1 r st1 ->
                   exists idx st1',
                     Smallstep.after_external (L1' se') s1' r' st1' /\
                     fsim_match_states HL1 se se' w idx st1 st1') ->
      match_states (index2 i i') (st2 L1 L2 s1 s2) (st2 L1' L2' s1' s2').

  Lemma step_fsim:
    forall s1 t s2, step L1 L2 se s1 t s2 ->
               forall i s1', match_states i s1 s1' ->
                        exists i' s2', (plus (fun _ => step L1' L2' se') tt s1' t s2' \/
                                   star (fun _ => step L1' L2' se') tt s1' t s2' /\ order i' i) /\
                                  match_states i' s2 s2'.
  Proof.
    intros ? ? ? Hstep ? ? Hs.
    destruct Hstep.
    - inv Hs.
      edestruct @fsim_simulation as (i' & s2' & Hstep' & Hs').
      apply HL1. eauto. eauto. eauto. eauto.
      eexists _, (st1 L1' L2' _). split.
      + destruct Hstep'; [left | right].
        apply plus_internal1. eauto.
        split. now apply star_internal1. constructor. apply a.
      + econstructor. eauto. eauto.
    - inv Hs.
      edestruct @fsim_simulation as (ix' & st2' & Hstep' & Hs').
      apply HL2. eauto. eauto. eauto. eauto.
      eexists _, (st2 L1' L2' _ _). split.
      + destruct Hstep'; [left | right].
        apply plus_internal2. eauto.
        split. now apply star_internal2. constructor. apply a.
      + econstructor. eauto. eauto. eauto. eauto.
    - inv Hs.
      edestruct @fsim_match_external as (w' & q' & Hext' & Hq' & Hse' & Haft).
      apply HL1. eauto. eauto. eauto. eauto.
      edestruct @fsim_match_initial_states as (? & ? & ? & ?).
      apply HL2. eauto. eauto. eauto. eauto.
      eexists _, (st2 L1' L2' _ _). split.
      + left. apply plus_one. eapply step_push. eauto.
        erewrite fsim_match_valid_query. eauto. apply HL2. eauto.
        eauto. eauto. eauto.
      + econstructor. eauto. eauto. eauto. eauto.
    - inv Hs.
      edestruct @fsim_match_final_states as (r' & Hf' & Hr).
      apply HL2. eauto. eauto. eauto. eauto.
      edestruct H8 as (? & ? & ? & ?). eauto. eauto.
      eexists _, (st1 L1' L2' _). split.
      + left. apply plus_one. eapply step_pop. eauto. eauto.
      + econstructor. eauto. eauto.
        Unshelve. auto. auto.
  Qed.

  Lemma external_fsim:
    forall i s1 s2 q1,
      match_states i s1 s2 ->
      at_external L1 L2 se s1 q1 ->
      exists (w0 : ccworld 1) (q2 : query li_null),
        at_external L1' L2' se' s2 q2 /\
        match_query 1 w0 q1 q2 /\
        match_senv 1 w0 se se' /\
        (forall r1 r2 s1',
            match_reply 1 w0 r1 r2 ->
            after_external L1 L2 se s1 r1 s1' ->
            exists i' s2',
              after_external L1' L2' se' s2 r2 s2' /\
              match_states i' s1' s2').
  Proof.
    intros. destruct q1.
  Qed.

  Lemma initial_fsim:
   forall q1 q2 s1,
     match_query cc w q1 q2 ->
     initial_state L1 L2 se q1 s1 ->
     exists i s2,
       initial_state L1' L2' se' q2 s2 /\
       match_states i s1 s2.
  Proof.
    intros. inv H0.
    edestruct @fsim_match_initial_states as (? & ? & ? & ?).
    apply HL1. eauto. eauto. eauto. eauto.
    eexists _, (st1 L1' L2' _). split.
    - econstructor. erewrite @fsim_match_valid_query.
      eauto. apply HL1. eauto. eauto. eauto. eauto.
    - econstructor. eauto. eauto.
  Qed.

  Lemma final_fsim:
    forall i s1 s2 r1,
      match_states i s1 s2 ->
      final_state L1 L2 se s1 r1 ->
      exists r2,
        final_state L1' L2' se' s2 r2 /\
        match_reply cc w r1 r2.
  Proof.
    intros. inv H0. inv H.
    edestruct @fsim_match_final_states.
    apply HL1. eauto. eauto. eauto. eauto.
    eexists. split. econstructor. apply H. apply H.
  Qed.

  Lemma layer_comp_fsim sk sk':
    fsim_properties 1 cc se se' w
                    (layer_comp L1 L2 sk se) (layer_comp L1' L2' sk' se')
                    index order match_states.
  Proof.
    split. cbn in *.
    - intros.
      replace (valid_query (L1 se) q1) with (valid_query (L1' se') q2).
      replace (valid_query (L2 se) q1) with (valid_query (L2' se') q2).
      reflexivity.
      erewrite @fsim_match_valid_query. eauto. apply HL2.
      eauto. eauto. eauto.
      erewrite @fsim_match_valid_query. eauto. apply HL1.
      eauto. eauto. eauto.
    - apply initial_fsim.
    - apply final_fsim.
    - apply external_fsim.
    - apply step_fsim.
  Qed.

End LAYER_COMP_SIM.

Require Import Linking SmallstepLinking.
