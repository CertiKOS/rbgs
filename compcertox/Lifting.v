Require Import Relations RelationClasses Relators.
Require Import List.
Require Import Coqlib.
Require Import LanguageInterface_ Events Globalenvs Smallstep_.

(* Definitions *)
Section Lifting.
  (* Lifting a language interface with abstract data of type K *)
  Variable K: Type.
  Definition lifted_li li: language_interface :=
    {|
    query := query li * K;
    reply := reply li * K;
    entry '(q, _) := entry q
    |}.

  (* Lifting an LTS with abstract data of type K. The lifted LTS simply
     passes the abstract state through without modifying it *)
  Context {liA liB state} (L: lts liA liB state).
  Let stateX := (state * K)%type.
  Let liBX := lifted_li liB.
  Let liAX := lifted_li liA.

  Program Definition lifted_lts: lts liAX liBX stateX :=
    {|
      genvtype := genvtype L;
      step p ge '(s, a) t '(s', a') := step L p ge s t s' /\ a = a';
      initial_state := (initial_state L) * eq;
      at_external := fun s (q: query liAX) => ((at_external L) * eq) s q;
      after_external s := (after_external L (fst s)) * eq;
      final_state := (final_state L) * eq;
      globalenv := globalenv L
    |}%rel.
  Next Obligation.
    destruct s, s'. split.
    eapply steps_monotone; now eauto.
    easy.
  Qed.

End Lifting.

Definition lifted_semantics {liA liB} (K: Type) (L: semantics liA liB) :=
  {|
    skel := skel L;
    activate se := lifted_lts K (L se);
    footprint := footprint L;
  |}.

(* Notations *)
Delimit Scope li_scope with li.
Bind Scope li_scope with language_interface.
(* Delimit Scope lts_scope with lts. *)
(* Bind Scope lts_scope with lts. *)

(* Note since we are overloading the @ operator, the right associativity and
   precedence level will be inherited *)
Notation "li @ K" := (lifted_li K li): li_scope.
(* Notation "L @ K" := (lifted_lts K L): lts_scope. *)

Delimit Scope lts_scope with lts.
Bind Scope lts_scope with semantics.
Notation "L @ K" := (lifted_semantics K L): lts_scope.

Notation " 'layer' K " := (Smallstep_.semantics li_null (li_c @ K)) (at level 1).

(* Properties *)
Require Import CategoricalComp.

Section CAT_COMP_LIFT.
  Variable K: Type.
  Context {liA liB liC} (L1: semantics liB liC) (L2: semantics liA liB).
  Variable (sk: AST.program unit unit).

  Local Inductive state_match: (comp_state L1 L2 * K) -> comp_state (L1 @ K) (L2 @ K) -> Prop :=
  | state_match1 s1 k:
      state_match (st1 _ _ s1, k) (st1 (L1@K) (L2@K) (s1, k))
  | state_match2 s1 s2 k k':
      state_match (st2 _ _ s1 s2, k) (st2 (L1@K) (L2@K) (s1, k') (s2, k)).

  Lemma lift_categorical_comp1:
    (comp_semantics' L1 L2 sk) @ K ≤ comp_semantics' (L1 @ K) (L2 @ K) sk.
  Proof.
    constructor. econstructor. reflexivity. intros i. reflexivity.
    intros se _ [ ] ? [ ] Hse. instantiate (1 := fun _ _ _ => _). cbn beta.
    eapply forward_simulation_step with (match_states := state_match).
    - intros q _ s1 [ ] Hq. destruct s1 as [s1 ks].
      inv Hq. inv H. destruct q as [q k]. cbn in *. subst.
      eexists _. split; repeat constructor; auto.
    - intros [s1 k] s2 [r kr] Hs Hr.
      inv Hr. inv H. cbn in *. subst. inv Hs.
      eexists. split; eauto. constructor. constructor; cbn; auto.
    - intros [s1 k] s2 [q1 kq] Hs Hq.
      eexists tt, _. repeat apply conj; try constructor.
      inv Hq. inv H. cbn in *. subst. inv Hs. constructor; auto.
      constructor; auto.
      intros [r1 kr1] [r2 kr2] [s1' k1'] [ ] Hr. inv Hr. inv H.
      inv Hq. inv H. cbn in *. subst. inv Hs. inv H8.
      eexists; split; repeat econstructor; eauto.
    - intros [s1 k1] t [s1' k1'] Hstep s2 Hs.
      inv Hstep. inv H; inv Hs.
      + eexists. split. apply step1.
        instantiate (1 := (_, _)). econstructor; eauto.
        constructor.
      + eexists. split. apply step2.
        instantiate (1 := (_, _)). econstructor; eauto.
        constructor.
      + eexists. split. eapply step_push.
        instantiate (1 := (_, _)). constructor; cbn; eauto.
        instantiate (1 := (_, _)). econstructor; cbn; eauto.
        auto. auto. constructor.
      + eexists. split. eapply  step_pop.
        instantiate (1 := (_, _)). econstructor; cbn; eauto.
        instantiate (1 := (_, _)). econstructor; cbn; eauto.
        constructor.
    - apply well_founded_ltof.
  Qed.

  Lemma lift_categorical_comp2:
    comp_semantics' (L1 @ K) (L2 @ K) sk ≤ (comp_semantics' L1 L2 sk) @ K.
  Proof.
    constructor. econstructor. reflexivity. intros i. reflexivity.
    intros se _ [ ] ? [ ] Hse. instantiate (1 := fun _ _ _ => _). cbn beta.
    eapply forward_simulation_step
      with (match_states := fun s1 s2 => state_match s2 s1).
    - intros [q1 kq] _ s [ ] H. inv H. inv H0.
      destruct s0. cbn in *. subst.
      eexists (_, _). split; repeat (cbn; econstructor); auto.
    - intros s1 [s2 ks] [r kr] Hs H. inv H. inv H0.
      destruct s. cbn in *. subst. inv Hs.
      eexists (_, _). split; repeat (cbn; econstructor); auto.
    - intros s1 [s2 ks] [q kq] Hs H. inv H. inv H2.
      cbn in *. subst. inv Hs. cbn in *.
      eexists _, (_, _).
      repeat apply conj; repeat constructor; eauto.
      intros [r1 kr1] [r2 kr2] s1' <- Hr. inv Hr. inv H6.
      destruct s2'. cbn in *. subst.
      eexists; split; repeat (cbn; econstructor); eauto.
      cbn. constructor; auto.
    - intros s1 t s1' Hstep [s2 ks] Hs.
      inv Hstep; inv Hs.
      + destruct s1'0. inv H.
        eexists (_, _); split; constructor; auto.
        apply step1. auto.
      + destruct s2'. inv H.
        eexists (_, _); split; constructor; auto.
        apply step2. auto.
      + destruct q, s3. inv H. inv H0. cbn in *. subst.
        eexists (_, _); split; constructor; auto.
        eapply step_push; eauto.
      + destruct r, s1'0. inv H. inv H0. cbn in *. subst.
        eexists (_, _); split; constructor; auto.
        eapply step_pop; eauto.
    - apply well_founded_ltof.
      Unshelve. exact tt.
  Qed.

  Lemma lift_categorical_comp:
    (comp_semantics' L1 L2 sk) @ K ≡ comp_semantics' (L1 @ K) (L2 @ K) sk.
  Proof.
    split; [ exact lift_categorical_comp1 | exact lift_categorical_comp2 ].
  Qed.

End CAT_COMP_LIFT.
