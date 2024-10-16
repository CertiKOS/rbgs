Require Import Coqlib.
Require Import LanguageInterface Smallstep Globalenvs Events.
Require Import List.
Import ListNotations.

Definition empty_skel: AST.program unit unit :=
  {|
    AST.prog_defs := [];
    AST.prog_public := [];
    AST.prog_main := None;
  |}.

Lemma empty_linkorder sk:
  Linking.linkorder empty_skel sk.
Proof.
  repeat apply conj.
  - constructor.
  - apply incl_nil_l.
  - intros. inv H.
Qed.

Definition with_ (liA liB: language_interface): language_interface :=
  {|
    query := sum (query liA) (query liB);
    reply := sum (reply liA) (reply liB);
    entry := fun q => match q with
                  | inl qA => entry qA
                  | inr qB => entry qB
                  end;
  |}.
Infix "+" := with_ (at level 50, left associativity).

Section WITH.
  Context {liA1 liA2 liB1 liB2}
    (L1: semantics liA1 liB1) (L2: semantics liA2 liB2).
  Section WITH_SE.
    Context (se: Genv.symtbl).
    Definition with_state := (Smallstep.state L1 + Smallstep.state L2)%type.
    Inductive with_initial_state: query (liB1 + liB2) -> with_state -> Prop :=
    | with_initial_state1 q s:
      Smallstep.initial_state (L1 se) q s ->
      with_initial_state (inl q) (inl s)
    | with_initial_state2 q s:
      Smallstep.initial_state (L2 se) q s ->
      with_initial_state (inr q) (inr s).
    Inductive with_at_external: with_state -> query (liA1 + liA2) -> Prop :=
    | with_at_external1 s q:
      Smallstep.at_external (L1 se) s q ->
      with_at_external (inl s) (inl q)
    | with_at_external2 s q:
      Smallstep.at_external (L2 se) s q ->
      with_at_external (inr s) (inr q).
    Inductive with_after_external: with_state -> reply (liA1 + liA2) -> with_state -> Prop :=
    | with_after_external1 s r s':
      Smallstep.after_external (L1 se) s r s' ->
      with_after_external (inl s) (inl r) (inl s')
    | with_after_external2 s r s':
      Smallstep.after_external (L2 se) s r s' ->
      with_after_external (inr s) (inr r) (inr s').
    Inductive with_final_state: with_state -> reply (liB1 + liB2) -> Prop :=
    | with_final_state1 s r:
      Smallstep.final_state (L1 se) s r ->
      with_final_state (inl s) (inl r)
    | with_final_state2 s r:
      Smallstep.final_state (L2 se) s r ->
      with_final_state (inr s) (inr r).
    Inductive with_step: with_state -> trace -> with_state -> Prop :=
    | with_step1 s1 s1' t:
      Step (L1 se) s1 t s1' -> with_step (inl s1) t (inl s1')
    | with_step2 s2 s2' t:
      Step (L2 se) s2 t s2' -> with_step (inr s2) t (inr s2').

  End WITH_SE.

  Lemma star_internal1 se s t s':
    Star (L1 se) s t s' -> star with_step se (inl s) t (inl s').
  Proof.
    induction 1; [eapply star_refl | eapply star_step]; eauto.
    constructor; auto.
  Qed.

  Lemma plus_internal1 se s t s':
    Plus (L1 se) s t s' -> plus with_step se (inl s) t (inl s').
  Proof.
    destruct 1; econstructor; eauto using star_internal1.
    constructor; eauto.
  Qed.

  Lemma star_internal2 se s t s':
    Star (L2 se) s t s' -> star with_step se (inr s) t (inr s').
  Proof.
    induction 1; [eapply star_refl | eapply star_step]; eauto.
    constructor; auto.
  Qed.

  Lemma plus_internal2 se s t s':
    Plus (L2 se) s t s' -> plus with_step se (inr s) t (inr s').
  Proof.
    destruct 1; econstructor; eauto using star_internal2.
    constructor; eauto.
  Qed.

  Definition with_semantics sk: semantics (liA1 + liA2) (liB1 + liB2) :=
    {|
      activate se :=
        {|
          Smallstep.step := with_step;
          Smallstep.initial_state := with_initial_state se;
          Smallstep.at_external := with_at_external se;
          Smallstep.after_external := with_after_external se;
          Smallstep.final_state := with_final_state se;
          Smallstep.globalenv := se;
        |};
      skel := sk;
      footprint i := footprint L1 i \/ footprint L2 i;
    |}.

End WITH.

Section CALLCONV.

  Context {liA1 liA2 liB1 liB2}
    (cc1: callconv liA1 liB1) (cc2: callconv liA2 liB2).

  Inductive with_cc_match_query:
    ccworld cc1 + ccworld cc2 -> query (liA1 + liA2) -> query (liB1 + liB2) -> Prop :=
  | with_cc_match_query1 w1 q1 q2:
    match_query cc1 w1 q1 q2 -> with_cc_match_query (inl w1) (inl q1) (inl q2)
  | with_cc_match_query2 w2 q1 q2:
    match_query cc2 w2 q1 q2 -> with_cc_match_query (inr w2) (inr q1) (inr q2).

  Inductive with_cc_match_reply:
    ccworld cc1 + ccworld cc2 -> reply (liA1 + liA2) -> reply (liB1 + liB2) -> Prop :=
  | with_cc_match_reply1 w1 r1 r2:
    match_reply cc1 w1 r1 r2 -> with_cc_match_reply (inl w1) (inl r1) (inl r2)
  | with_cc_match_reply2 w2 r1 r2:
    match_reply cc2 w2 r1 r2 -> with_cc_match_reply (inr w2) (inr r1) (inr r2).

  Program Definition with_cc: callconv (liA1 + liA2) (liB1 + liB2) :=
    {|
      ccworld := ccworld cc1 + ccworld cc2;
      match_senv w :=
        match w with
        | inl w1 => match_senv cc1 w1
        | inr w2 => match_senv cc2 w2
        end;
      match_query := with_cc_match_query;
      match_reply := with_cc_match_reply;
    |}.
  Next Obligation.
    destruct w; eapply match_senv_public_preserved; eauto.
  Qed.
  Next Obligation.
    destruct w; eapply match_senv_valid_for; eauto.
  Qed.
  Next Obligation.
    destruct w; inv H0; eapply match_senv_symbol_address; eauto.
  Qed.
  Next Obligation. inv H; eapply match_query_defined; eauto. Qed.

End CALLCONV.
Infix "+" := with_cc (at level 50, left associativity): cc_scope.

Section SIM.
  Import Linking.

  Context {liA1 liA2 liA3 liA4 liB1 liB2 liB3 liB4}
    (La1: semantics liA1 liA2) (La2: semantics liA3 liA4)
    (Lb1: semantics liB1 liB2) (Lb2: semantics liB3 liB4)
    (cc1: callconv liA1 liB1) (cc2: callconv liA2 liB2)
    (cc3: callconv liA3 liB3) (cc4: callconv liA4 liB4)
    (sim1: forward_simulation cc1 cc2 La1 Lb1)
    (sim2: forward_simulation cc3 cc4 La2 Lb2)
    (sk: AST.program unit unit)
    (Hsk1: linkorder (skel La1) sk) (Hsk2: linkorder (skel La2) sk).

  Inductive with_fsim_order {index1 index2}
    (order1: index1 -> index1 -> Prop) (order2: index2 -> index2 -> Prop):
    (index1 + index2) -> (index1 + index2) -> Prop :=
  | with_fsim_order1 i1 i1':
    order1 i1 i1' -> with_fsim_order order1 order2 (inl i1) (inl i1')
  | with_fsim_order2 i2 i2':
    order2 i2 i2' -> with_fsim_order order1 order2 (inr i2) (inr i2').

  Inductive with_fsim_match_state {index1 index2}
    (match_state1: Genv.symtbl -> Genv.symtbl -> ccworld cc2 -> index1 -> state La1 -> state Lb1 -> Prop)
    (match_state2: Genv.symtbl -> Genv.symtbl -> ccworld cc4 -> index2 -> state La2 -> state Lb2 -> Prop):
    Genv.symtbl -> Genv.symtbl -> ccworld (cc2 + cc4) -> (index1 + index2) -> (state La1 + state La2) -> (state Lb1 + state Lb2) -> Prop :=
  | with_fsim_match_state1 se1 se2 w1 i1 s1 s1':
    match_state1 se1 se2 w1 i1 s1 s1' ->
    with_fsim_match_state match_state1 match_state2 se1 se2 (inl w1) (inl i1) (inl s1) (inl s1')
  | with_fsim_match_state2 se1 se2 w2 i2 s2 s2':
    match_state2 se1 se2 w2 i2 s2 s2' ->
    with_fsim_match_state match_state1 match_state2 se1 se2 (inr w2) (inr i2) (inr s2) (inr s2').

  Lemma with_fsim:
    forward_simulation (cc1 + cc3) (cc2 + cc4)
      (with_semantics La1 La2 sk)
      (with_semantics Lb1 Lb2 sk).
  Proof.
    destruct sim1 as [A]. destruct sim2 as [B].
    constructor.
    eapply Forward_simulation
      with (with_fsim_order (fsim_order A) (fsim_order B))
           (with_fsim_match_state (fsim_match_states A) (fsim_match_states B)).
    - reflexivity.
    - cbn. intros.
      pose proof (fsim_footprint A i).
      pose proof (fsim_footprint B i). firstorder.
    - intros * Hse Hvf; destruct wB.
      + eapply Genv.valid_for_linkorder in Hvf. 2: apply Hsk1.
        destruct A. cbn -[with_semantics].
        specialize (fsim_lts _ _ _ Hse Hvf). constructor.
        * intros * Hq Hs. inv Hq. inv Hs.
          edestruct @fsim_match_initial_states as (ix & sx & Hi & Hsx); eauto.
          exists (inl ix), (inl sx). split; constructor; eauto.
        * intros * Hs Hf. inv Hf; inv Hs.
          edestruct @fsim_match_final_states as (rx & Hfx & Hrx); eauto.
          exists (inl rx). split; constructor; eauto.
        * intros * Hs Ha. inv Ha; inv Hs.
          edestruct @fsim_match_external
            as (wx & qx & A1 & A2 & A3 & A4); eauto.
          exists (inl wx), (inl qx). split; repeat constructor; eauto.
          intros * Hr Ht. inv Ht; inv Hr.
          edestruct A4 as (ix & sx & B1 & B2); eauto.
          exists (inl ix), (inl sx). split; constructor; eauto.
        * intros * Hstep * Hs. inv Hstep; inv Hs.
          edestruct @fsim_simulation as (ix & sx & [A1|A2] & A3); eauto.
          -- exists (inl ix), (inl sx). split; constructor; eauto.
             eapply plus_internal1; eauto.
          -- exists (inl ix), (inl sx). split. 2: constructor; eauto.
             right. split; eauto.
             eapply star_internal1; apply A2.
             constructor; apply A2.
      + eapply Genv.valid_for_linkorder in Hvf. 2: apply Hsk2.
        destruct B. cbn -[with_semantics].
        specialize (fsim_lts _ _ _ Hse Hvf). constructor.
        * intros * Hq Hs. inv Hq. inv Hs.
          edestruct @fsim_match_initial_states as (ix & sx & Hi & Hsx); eauto.
          exists (inr ix), (inr sx). split; constructor; eauto.
        * intros * Hs Hf. inv Hf; inv Hs.
          edestruct @fsim_match_final_states as (rx & Hfx & Hrx); eauto.
          exists (inr rx). split; constructor; eauto.
        * intros * Hs Ha. inv Ha; inv Hs.
          edestruct @fsim_match_external
            as (wx & qx & A1 & A2 & A3 & A4); eauto.
          exists (inr wx), (inr qx). split; repeat constructor; eauto.
          intros * Hr Ht. inv Ht; inv Hr.
          edestruct A4 as (ix & sx & B1 & B2); eauto.
          exists (inr ix), (inr sx). split; constructor; eauto.
        * intros * Hstep * Hs. inv Hstep; inv Hs.
          edestruct @fsim_simulation as (ix & sx & [A1|A2] & A3); eauto.
          -- exists (inr ix), (inr sx). split; constructor; eauto.
             eapply plus_internal2; eauto.
          -- exists (inr ix), (inr sx). split. 2: constructor; eauto.
             right. split; eauto.
             eapply star_internal2; apply A2.
             constructor; apply A2.
    - red. intros [a|a].
      + induction (fsim_order_wf A a) as [x Hx IHx].
        constructor. intros b Hb. inv Hb. eauto.
      + induction (fsim_order_wf B a) as [x Hx IHx].
        constructor. intros b Hb. inv Hb. eauto.
  Qed.

End SIM.
