Require Import Relations.
Require Import List.
Require Import Coqlib.
Require Import LanguageInterface.
Require Import Events.
Require Import Globalenvs.
Require Import SmallstepLinking.
Require Import Smallstep.
Require Import Integers.
Require Import Linking.
Require Import AST.
Require Import CallconvAlgebra.

Require Import Coq.Logic.ClassicalFacts.
Require Import Coq.Logic.FunctionalExtensionality.
Axiom EquivThenEqual: prop_extensionality.

Open Scope smallstep_scope.
Delimit Scope smallstep_scope with smallstep.

Set Asymmetric Patterns.

Section COMP.
  Context {liA liB liC} (L1: semantics liB liC) (L2: semantics liA liB).
  Section WITH_SE.
    Context (se: Genv.symtbl).

    Variant comp_state :=
    | st1 (s: state L1) | st2 (s1: state L1) (s2: state L2).

    Inductive comp_step: comp_state -> trace -> comp_state -> Prop :=
    | step1 s1 t s1':
        Step (L1 se) s1 t s1' ->
        comp_step (st1 s1) t (st1 s1')
    | step2 s1 s2 t s2':
        Step (L2 se) s2 t s2' ->
        comp_step (st2 s1 s2) t (st2 s1 s2')
    | step_push s1 q s2:
        at_external (L1 se) s1 q ->
        initial_state (L2 se) q s2 ->
        comp_step (st1 s1) E0 (st2 s1 s2)
    | step_pop s1 r s2 s1':
        final_state (L2 se) s2 r ->
        after_external (L1 se) s1 r s1' ->
        comp_step (st2 s1 s2) E0 (st1 s1').

    Inductive comp_initial_state (q: query liC): comp_state -> Prop :=
    | comp_initial_state_intro s:
        initial_state (L1 se) q s ->
        comp_initial_state q (st1 s).

    Inductive comp_at_external: comp_state -> query liA -> Prop :=
    | comp_at_external_intro s1 s2 (q: query liA):
        at_external (L2 se) s2 q ->
        comp_at_external (st2 s1 s2) q.

    Inductive comp_after_external: comp_state -> reply liA -> comp_state -> Prop :=
    | comp_after_external_intro s1 s2 r s2':
        after_external (L2 se) s2 r s2' ->
        comp_after_external (st2 s1 s2) r (st2 s1 s2').

    Inductive comp_final_state: comp_state -> reply liC -> Prop :=
    | comp_final_state_intro s r:
        final_state (L1 se) s r ->
        comp_final_state (st1 s) r.

    Lemma star_internal1 s t s':
      Star (L1 se) s t s' ->
      star (fun _ => comp_step) tt (st1 s) t (st1 s').
    Proof.
      induction 1; [eapply star_refl | eapply star_step]; eauto.
      constructor; auto.
    Qed.

    Lemma plus_internal1 s t s':
      Plus (L1 se) s t s' ->
      plus (fun _ => comp_step) tt (st1 s) t (st1 s').
    Proof.
      destruct 1; econstructor; eauto using step1, star_internal1.
    Qed.

    Lemma star_internal2 s1 s t s':
      Star (L2 se) s t s' ->
      star (fun _ => comp_step) tt (st2 s1 s) t (st2 s1 s').
    Proof.
      induction 1; [eapply star_refl | eapply star_step]; eauto.
      constructor; auto.
    Qed.

    Lemma plus_internal2 s1 s t s':
      Plus (L2 se) s t s' ->
      plus (fun _ => comp_step) tt (st2 s1 s) t (st2 s1 s').
    Proof.
      destruct 1; econstructor; eauto using step2, star_internal2.
    Qed.

  End WITH_SE.

  Program Definition comp_semantics' sk: semantics liA liC :=
    {|
      activate se :=
        {|
          step ge:= comp_step se;
          initial_state := comp_initial_state se;
          at_external := comp_at_external se;
          after_external := comp_after_external se;
          final_state := comp_final_state se;
          globalenv := tt;
        |};
      skel := sk;
      footprint i := footprint L1 i \/ footprint L2 i;
    |}.

  Class CategoricalLinkable :=
    categorical_linking:
      forall se s q, at_external (L2 se) s q -> ~ valid_query L1 se q.

End COMP.

Definition comp_semantics {liA liB liC} (L1: semantics liB liC)
           (L2: semantics liA liB): option (semantics liA liC) :=
  option_map (comp_semantics' L1 L2) (link (skel L1) (skel L2)).

Section ID.
  Context {li: language_interface}.
  Variant id_state := | st_q (q: query li) | st_r (r: reply li).

  Inductive id_step: id_state -> trace -> id_state -> Prop := .

  Inductive id_initial_state: query li -> id_state -> Prop :=
  | id_initial_state_intro q:
      id_initial_state q (st_q q).

  Inductive id_at_external: id_state -> query li -> Prop :=
  | id_at_external_intro q:
      id_at_external (st_q q) q.

  Inductive id_after_external: id_state -> reply li -> id_state -> Prop :=
  | id_after_external_intro q r:
      id_after_external (st_q q) r (st_r r).

  Inductive id_final_state: id_state -> reply li -> Prop :=
  | id_final_state_intro r:
      id_final_state (st_r r) r.
End ID.

Program Definition id_semantics {li} sk: semantics li li :=
  {|
  activate se :=
    {|
      step _ := id_step;
      initial_state := id_initial_state;
      at_external := id_at_external;
      after_external := id_after_external;
      final_state := id_final_state;
      globalenv := tt;
    |};
  skel := sk;
  footprint i := False;
  |}.

Notation "L1 ∘ L2" :=  (comp_semantics L1 L2)(at level 40, left associativity): lts_scope.

Section ASSOC.

  Context {liA liB liC liD} (L1: semantics liC liD)
          (L2: semantics liB liC) (L3: semantics liA liB).
  Context (sk1 sk2 sk: AST.program unit unit).

  Let L12 := comp_semantics' L1 L2 sk1.
  Let L23 := comp_semantics' L2 L3 sk2.
  Let L := comp_semantics' L12 L3 sk.
  Let L' := comp_semantics' L1 L23 sk.

  Inductive assoc_state_match: comp_state L1 L23 -> comp_state L12 L3 -> Prop :=
  | assoc_match1 s1: assoc_state_match
                       (st1 L1 L23 s1)
                       (st1 L12 L3 (st1 L1 L2 s1))
  | assoc_match2 s1 s2: assoc_state_match
                          (st2 L1 L23 s1 (st1 L2 L3 s2))
                          (st1 L12 L3 (st2 L1 L2 s1 s2))
  | assoc_match3 s1 s2 s3: assoc_state_match
                             (st2 L1 L23 s1 (st2 L2 L3 s2 s3))
                             (st2 L12 L3 (st2 L1 L2 s1 s2) s3).

  (* Lemma assoc1: L1 ∘ (L2 ∘ L3) ≤ L1 ∘ L2 ∘ L3. *)
  Lemma assoc1: L' ≤ L.
  Proof.
    constructor. econstructor.
    - reflexivity.
    - intros. cbn. now rewrite or_assoc.
    - { intros se _ [ ] [ ] Hse.
        instantiate (1 := fun _ _ _ => _). cbn beta.
        apply forward_simulation_step
          with (match_states := assoc_state_match); cbn.
        - intros q _ s1 [ ] H. inv H.
          eexists. split; try repeat constructor; auto.
        - intros s1 s2 r Hs H. inv H. inv Hs.
          eexists. split; try repeat constructor; auto.
        - intros s1 s2 q Hs Hext. inv Hext. inv H. inv Hs.
          eexists tt, _. repeat apply conj; try repeat constructor; auto.
          intros r _ s1' [ ] Haft. inv Haft. inv H4.
          eexists. split; try repeat constructor; auto.
        - intros s1 t s1' Hstep s2 Hs.
          inv Hstep.
          + inv Hs. eexists; split; try repeat constructor; auto.
          + inv H; inv Hs; eexists; (split; [ | constructor ]).
            * apply step1. now apply step2.
            * now apply step2.
            * eapply step_push; eauto.
              constructor; auto.
            * eapply step_pop; try constructor; eauto.
          + inv H0. eexists; split; [ | constructor ].
            inv Hs. constructor. eapply step_push; eauto.
          + inv H. eexists; split; [ | constructor].
            inv Hs. constructor. econstructor; eauto.
      }
    - apply well_founded_ltof.
  Qed.

  (* Lemma assoc2: L1 ∘ L2 ∘ L3 ≤ L1 ∘ (L2 ∘ L3). *)
  Lemma assoc2: L ≤ L'.
  Proof.
    constructor. econstructor.
    - reflexivity.
    - intros. cbn. now rewrite or_assoc.
    - { intros se _ [ ] [ ] Hse.
        instantiate (1 := fun _ _ _ => _). cbn beta.
        apply forward_simulation_step
          with (match_states := fun s1 s2 => assoc_state_match s2 s1); cbn.
        - intros q _ s1 [ ] H. inv H. inv H0.
          eexists; split; constructor; auto.
        - intros s1 s2 r Hs H. inv H. inv H0. inv Hs.
          eexists; split; constructor; auto.
        - intros s1 s2 q Hs Hext. inv Hext. inv Hs.
          eexists tt, _. repeat apply conj; try repeat constructor; auto.
          intros r _ s1' [ ] Haft. inv Haft.
          eexists; split; repeat constructor; auto.
        - intros s1 t s1' Hstep s2 Hs.
          inv Hstep.
          + inv H; inv Hs; eexists; (split; [ | constructor ]).
            * now apply step1.
            * apply step2. now apply step1.
            * eapply step_push; try constructor; eauto.
            * eapply step_pop; try constructor; eauto.
          + inv Hs. eexists; split; repeat constructor; auto.
          + inv H. inv Hs. eexists; split; constructor.
            eapply step_push; eauto.
          + inv H0. inv Hs. eexists; split; constructor.
            eapply step_pop; eauto.
      }
    - apply well_founded_ltof.
  Qed.

  (* Theorem categorical_comp_assoc: L1 ∘ (L2 ∘ L3) ≡ L1 ∘ L2 ∘ L3. *)
  Theorem categorical_comp_assoc: L' ≡ L.
  Proof.
    split; [ exact assoc1 | exact assoc2 ].
  Qed.
End ASSOC.

Section FSIM.
  Context {liA1 liA2 liB1 liB2 liC1 liC2}
          (cc1: callconv liA1 liA2)
          (cc2: callconv liB1 liB2)
          (cc3: callconv liC1 liC2)
          (L1: semantics liB1 liC1) (L2: semantics liA1 liB1)
          (L1': semantics liB2 liC2) (L2': semantics liA2 liB2).
  Context (HL1: fsim_components cc2 cc3 L1 L1')
          (HL2: fsim_components cc1 cc2 L2 L2')
          (se1 se2: Genv.symtbl) (w : ccworld cc3) (qset: ident -> Prop)
          (Hse: match_senv cc3 w se1 se2)
          (Hse1: Genv.valid_for (skel L1) se1)
          (Hse2: Genv.valid_for (skel L2) se1).

  Variant index := | index1: fsim_index HL1 -> index
                   | index2: fsim_index HL1 -> fsim_index HL2 -> index.

  Variant order: index -> index -> Prop :=
             | order1 i1 i1': fsim_order HL1 i1 i1' ->
                              order (index1 i1) (index1 i1')
             | order2 i1 i2 i2': fsim_order HL2 i2 i2' ->
                                 order (index2 i1 i2) (index2 i1 i2').

  Inductive match_states: index -> comp_state L1 L2 -> comp_state L1' L2' -> Prop :=
  | match_st1 i1 s1 s1':
      fsim_match_states HL1 se1 se2 w i1 s1 s1' ->
      match_states (index1 i1) (st1 L1 L2 s1) (st1 L1' L2' s1')
  | match_st2 i1 i2 s1 s1' s2 s2' w':
      match_senv cc2 w' se1 se2 ->
      fsim_match_states HL2 se1 se2 w' i2 s2 s2' ->
      (forall r1 r2 (s2 : state L1),
          match_reply cc2 w' r1 r2 ->
          after_external (L1 se1) s1 r1 s2 ->
          exists (i' : fsim_index HL1) (s2' : state L1'),
            after_external (L1' se2) s1' r2 s2' /\
            fsim_match_states HL1 se1 se2 w i' s2 s2') ->
      match_states (index2 i1 i2) (st2 L1 L2 s1 s2) (st2 L1' L2' s1' s2').

  Local Lemma semantics_simulation sk sk':
    fsim_properties cc1 cc3 se1 se2 w
                    (comp_semantics' L1 L2 sk se1)
                    (comp_semantics' L1' L2' sk' se2)
                    index order match_states.
  Proof.
    split; cbn.
    - intros q1 q2 s1 Hq H. inv H.
      pose proof (fsim_lts HL1 _ _ Hse Hse1).
      edestruct @fsim_match_initial_states as (idx & s' & Hs' & Hs); eauto.
      exists (index1 idx), (st1 L1' L2' s'). split; econstructor; eauto.
    - intros i s1 s2 r1 Hs H. inv H. inv Hs.
      pose proof (fsim_lts HL1 _ _ Hse Hse1).
      edestruct @fsim_match_final_states as (r' & H' & Hr'); eauto.
      exists r'. split; auto. constructor; auto.
    - intros i s1 s2 q1 Hs H. inv H. inv Hs.
      pose proof (fsim_lts HL2 _ _ H2 Hse2).
      edestruct @fsim_match_external as (w1 & q' & H' & Hq' & Hse' & HH); eauto.
      exists w1, q'. repeat apply conj; auto.
      + constructor; auto.
      + intros r1 r2 xs1 Hr HH'. inv HH'.
        specialize (HH _ _ _ Hr H8) as (i2' & xs2 & Haft & Hss).
        eexists (index2 i1 i2'), (st2 L1' L2' _ _). split.
        * econstructor. eauto.
        * econstructor; eauto.
    - intros s1 t s2 Hstep idx s1' Hs.
      inv Hstep; inv Hs.
      + pose proof (fsim_lts HL1 _ _ Hse Hse1).
        edestruct @fsim_simulation as (idx' & s2' & Hs2' & Hs'); eauto.
        exists (index1 idx'), (st1 L1' L2' s2'). split.
        * destruct Hs2'; [ left | right ].
          apply plus_internal1. auto.
          split. apply star_internal1. apply H1. constructor; apply H1.
        * constructor. auto.
      + pose proof (fsim_lts HL2 _ _  H2 Hse2).
        edestruct @fsim_simulation as (idx' & xs2' & Hs2' & Hs'); eauto.
        exists (index2 i1 idx'), (st2 L1' L2' s1'0 xs2'). split.
        * destruct Hs2'; [ left | right ].
          -- apply plus_internal2. auto.
          -- split. apply star_internal2. apply H1.
             constructor. apply H1.
        * econstructor; eauto.
      + pose proof (fsim_lts HL1 _ _ Hse Hse1).
        edestruct @fsim_match_external as (w' & q' & H' & Hq' & Hse' & HH); eauto.
        pose proof (fsim_lts HL2 _ _ Hse' Hse2).
        edestruct @fsim_match_initial_states as (i2 & s2' & Hs2' & Hs'); eauto.
        exists (index2 i1 i2), (st2 L1' L2' s1'0 s2'). split.
        * left. apply plus_one. eapply step_push; eauto.
        * econstructor; eauto.
      + pose proof (fsim_lts HL2 _ _ H3 Hse2).
        edestruct @fsim_match_final_states as (r' & H' & Hr'); eauto.
        edestruct H7 as (idx & xs2' & HH & Hs2'); eauto.
        exists (index1 idx), (st1 L1' L2' xs2'). split.
        * left. apply plus_one. eapply step_pop; eauto.
        * constructor. auto.
  Qed.

End FSIM.

Section COMP_FSIM.

  Context {liA1 liA2 liB1 liB2 liC1 liC2}
          {cc1: callconv liA1 liA2} {cc2: callconv liB1 liB2} {cc3: callconv liC1 liC2}
          (L1a: semantics liB1 liC1) (L2a: semantics liB2 liC2)
          (L1b: semantics liA1 liB1) (L2b: semantics liA2 liB2).
  Hypothesis (HL1: forward_simulation cc2 cc3 L1a L2a)
             (HL2: forward_simulation cc1 cc2 L1b L2b).

  Variable (sk: AST.program unit unit).
  Hypothesis (Hsk1: linkorder (skel L1a) sk)
             (Hsk2: linkorder (skel L1b) sk).

  Lemma categorical_compose_simulation':
    forward_simulation cc1 cc3 (comp_semantics' L1a L1b sk)
                       (comp_semantics' L2a L2b sk).
  Proof.
    destruct HL1 as [Ha]. destruct HL2 as [Hb].
    constructor.
    eapply Forward_simulation
      with (order cc1 cc2 cc3 L1a L1b L2a L2b Ha Hb)
           (match_states cc1 cc2 cc3 L1a L1b L2a L2b Ha Hb).
    - cbn. destruct Ha, Hb. congruence.
    - cbn. intros i. destruct Ha, Hb.
      rewrite fsim_footprint, fsim_footprint0. reflexivity.
    - intros se1 se2 w Hse Hse1.
      eapply semantics_simulation; eauto.
      eapply Genv.valid_for_linkorder. apply Hsk1. auto.
      eapply Genv.valid_for_linkorder. apply Hsk2. auto.
    - clear - Ha Hb. intros [|].
      + induction (fsim_order_wf Ha f). constructor.
        intros. inv H1. apply H0. auto.
      + induction (fsim_order_wf Hb f0). constructor.
        intros. inv H1. apply H0. auto.
  Qed.

End COMP_FSIM.

Lemma categorical_compose_simulation
      {liA1 liA2 liB1 liB2 liC1 liC2}
      (cc1: callconv liA1 liA2) (cc2: callconv liB1 liB2) (cc3: callconv liC1 liC2)
      L1a L1b L1 L2a L2b L2:
  forward_simulation cc2 cc3 L1a L2a ->
  forward_simulation cc1 cc2 L1b L2b ->
  L1a ∘ L1b = Some L1 -> L2a ∘ L2b = Some L2 ->
  forward_simulation cc1 cc3 L1 L2.
Proof.
  intros [Ha] [Hb] H1 H2. unfold comp_semantics in *. unfold option_map in *.
  destruct (link (skel L1a) (skel L1b)) as [sk1|] eqn:Hsk1; try discriminate. inv H1.
  destruct (link (skel L2a) (skel L2b)) as [sk2|] eqn:Hsk2; try discriminate. inv H2.
  replace sk2 with sk1.
  eapply categorical_compose_simulation'; eauto.
  - constructor. eauto.
  - constructor. eauto.
  - pose proof (link_linkorder _ _ _ Hsk1) as [ ]. auto.
  - pose proof (link_linkorder _ _ _ Hsk1) as [ ]. auto.
  - destruct Ha, Hb. congruence.
Qed.

Section APPROX.
  Context {li} (L1 L2: semantics li li).
  Context `{!CategoricalLinkable L1 L2}
          `{!ProgramSem L1} `{!ProgramSem L2}.
  Context (sk: AST.program unit unit).

  Let L := fun i => match i with true => L1 | false => L2 end.

  Inductive match_frame: comp_state L1 L2 -> list (SmallstepLinking.frame L) -> Prop :=
  | match_frame1 s:
      match_frame (st1 L1 L2 s) (st L true s :: nil)
  | match_frame2 s1 s2:
      match_frame (st2 L1 L2 s1 s2) (st L false s2 :: st L true s1 :: nil).

  Lemma categorical_compose_approximation:
    forward_simulation 1 1 (comp_semantics' L1 L2 sk) (SmallstepLinking.semantics L sk).
  Proof.
    constructor. econstructor; eauto.
    {
      intros i. split.
      - intros [|]; [exists true | exists false]; firstorder.
      - intros [[|] ?]; [left | right]; firstorder.
    }
    intros se ? [ ] [ ] Hse.
    instantiate (1 := fun _ _ _ => _). cbn beta.
    apply forward_simulation_step with (match_states := match_frame).
    - intros q ? s1 [ ] H. inv H.
      exists (st L true s :: nil). split; constructor.
      eapply incoming_query_valid; eauto. auto.
    - intros s1 s2 r Hs H. inv H. inv Hs.
      exists r. split; constructor; auto.
    - intros s s' q Hs H. inv H. inv Hs.
      exists tt, q. repeat apply conj; try constructor; auto.
      + intros [|]; auto.
        eapply categorical_linking; eauto.
        eapply outgoing_query_invalid. eauto.
      + intros. inv H1. inv H. eexists. split; econstructor; eauto.
    - intros s1 t s2 Hstep s1' Hs. inv Hstep; inv Hs.
      + eexists (st L true _ :: nil). split; constructor; auto.
      + eexists (st L false _ :: st L true _ :: nil). split; constructor. auto.
      + eexists (st L false _ :: st L true _ :: nil). split.
        eapply SmallstepLinking.step_push; eauto.
        eapply incoming_query_valid; eauto.
        constructor.
      + eexists (st L true _ :: nil). split.
        eapply SmallstepLinking.step_pop; eauto.
        constructor.
    - apply well_founded_ltof.
  Qed.

End APPROX.

