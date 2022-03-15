From Coq Require Import
     Relations
     RelationClasses
     List.
From models Require Import
     IntSpec.
From compcert Require Import
     Coqlib
     LanguageInterface
     Events
     Globalenvs
     Smallstep.
From lattices Require Import
     Upset Downset FCD.
From structures Require Import
     Effects Lattice.
Require Import examples.RefConv.

Import ISpec.

(** * Embed CompCert Semantics into Game Semantics *)

(** ** Embed Labelled Tranition Systems *)
Section LTS.

  Context {liA liB state} (L: lts liA liB state).

  (** *** Demonic Interpretation *)
  Section DEM.

    (** One way to think about demonic and angelic interpretation is via the
      refinement relation: the computation is more refined if it is more
      angelically non-deterministic or less demonically non-deterministic. We
      will consider a refinement of the computation to be an implementation with
      less non-deterministic choices, thus the demonic interpretation is
      used. The demonic view corresponds to the backward simulation.

      However, the problem with the compcert semantics is that when there are no
      possible transitions, the choice should be interpreted angelically as ⊥,
      rather than demonically as ⊤. Therefore, we rely on assertions.

      Since recursive definition in Coq is required to be terminating, we use
      the number of execution steps as the decreasing argument. If the
      transition does not finish within the number of steps, it
      crashes. Eventually, we use an angelic choice over the number of steps. *)

    Fixpoint dem_lts_spec' (n: nat) (s: state): ispec liA (reply liB) :=
      match n with
      | O => bot
      | S n =>
          _ <- assert (safe L s);
          (* internal step *)
          (inf { s' | Step L s E0 s' }, dem_lts_spec' n s') &&
          (* external call *)
          (inf { q | at_external L s q },
           r <- query_int q;
           _ <- assert (exists s', after_external L s r s');
           inf { s' | after_external L s r s' }, dem_lts_spec' n s') &&
          (* final state *)
          (inf { r | final_state L s r }, ret r)
      end.

    Definition dem_lts_spec: subst liA liB :=
      fun _ '(li_sig q) => sup n,
        _ <- assert (exists s, initial_state L q s);
        inf { s | initial_state L q s }, dem_lts_spec' n s.

  End DEM.

  (** *** Angelic Semantics *)
  Section ANG.

    Fixpoint ang_lts_spec' (n: nat) (s: state): ispec liA (reply liB) :=
      match n with
      | O => bot
      | S n =>
          (* internal step *)
          (sup { s' | Star L s E0 s' }, ang_lts_spec' n s') ||
          (* external call *)
          (sup { q | at_external L s q },
           r <- query_int q;
           sup { s' | after_external L s r s' }, ang_lts_spec' n s') ||
          (* final step *)
          (sup { r | final_state L s r }, ret r)
      end.

    Definition ang_lts_spec: subst liA liB :=
      fun _ '(li_sig q) => sup n,
        sup { s | initial_state L q s }, ang_lts_spec' n s.

    (** Executing one step in the FCD specification *)
    Lemma lts_spec_step s:
      sup n, ang_lts_spec' n s =
        (sup { s' | Star L s E0 s' }, sup n, ang_lts_spec' n s') ||
        (sup { q | at_external L s q },
          r <- query_int q;
         sup { s' | after_external L s r s' }, sup n, ang_lts_spec' n s') ||
        (sup { r | final_state L s r }, ret r).
    Proof.
      apply antisymmetry.
      - apply sup_iff. intros i.
        destruct i; cbn; eauto using bot_lb.
        repeat apply join_lub.
        + apply join_l. apply join_l.
          apply sup_iff. intros [s' H]. cbn.
          apply (sup_at (exist _ s' H)). apply (sup_at i). reflexivity.
        + apply join_l. apply join_r.
          apply sup_iff. intros [q H]. cbn.
          apply (sup_at (exist _ q H)). cbn.
          apply bind_proper_ref; try reflexivity.
          intros ra. unfold bind.
          apply sup_iff. intros [s' Hs'].
          eapply fsup_at. eauto. cbn.
          apply (sup_at i). reflexivity.
        + apply join_r. reflexivity.
      - repeat apply join_lub.
        + apply sup_iff. intros [s' H]. cbn.
          apply sup_iff. intros n. apply (sup_at (S n)). cbn.
          apply join_l. apply join_l.
          apply (sup_at (exist _ s' H)). reflexivity.
        + apply sup_iff. intros [q Hq]. cbn.
          unfold bind. setoid_rewrite Sup.mor.
          apply sup_iff. intros [ra|].
          * rewrite FCD.ext_ana. cbn. apply join_lub.
            -- apply (sup_at 1%nat). cbn. apply join_l. apply join_r.
               eapply fsup_at. eauto.
               setoid_rewrite Sup.mor.
               apply (sup_at (Some ra)). unfold bind.
               rewrite FCD.ext_ana. cbn.
               apply join_l. reflexivity.
            -- setoid_rewrite Sup.mor. apply sup_iff. intros [s' Hs'].
               cbn. rewrite Sup.mor. apply sup_iff. intros i.
               apply (sup_at (S i)). cbn. apply join_l. apply join_r.
               eapply fsup_at; eauto. unfold bind.
               setoid_rewrite Sup.mor. apply (sup_at (Some ra)).
               rewrite FCD.ext_ana. cbn. apply join_r.
               setoid_rewrite Sup.mor.
               apply (sup_at (exist _ s' Hs')). cbn. reflexivity.
          * rewrite FCD.ext_ana. cbn.
            apply (sup_at 1%nat). cbn. apply join_l. apply join_r.
            eapply fsup_at; eauto. unfold bind.
            setoid_rewrite Sup.mor. apply (sup_at None).
            rewrite FCD.ext_ana. reflexivity.
        + apply sup_iff. intros [r Hr]. cbn.
          apply (sup_at 1%nat). cbn. apply join_r.
          eapply fsup_at; eauto. reflexivity.
    Qed.

  End ANG.

  (** The two interpretations coincide when the computation has at most one
    behavior, i.e. when the LTS is deterministic *)
  Section DET.
    Context (se: Genv.symtbl).
    Hypothesis DET: lts_determinate L se.

    Lemma det_lts_spec_equiv:
      ang_lts_spec = dem_lts_spec.
    Proof.
      apply antisymmetry.
      - intros ? [q]. cbn. apply sup_lub. intros i.
        unfold assert.
    Abort.

  End DET.

  (* Definitions for defining the embedding through the play instead of
     interaction primitives. Not used for now *)
  (* Inductive state_exec: state -> query liA + reply liB -> Prop :=
  | state_exec_step s s' e:
      Step L s E0 s' ->
      state_exec s' e ->
      state_exec s e
  | state_exec_final s r:
      final_state L s r ->
      state_exec s (inr r)
  | state_exec_external s q:
      at_external L s q ->
      state_exec s (inl q).

  Inductive lts_play: state -> play liA (reply liB) -> Prop :=
  | lts_play_step s s' p:
    Step L s E0 s' ->
    lts_play s' p ->
    lts_play s p
  | lts_play_ret s r:
    final_state L s r ->
    lts_play s (pret r)
  | lts_play_query s q r (p: play liA (reply liB)) s':
    lts_play s' p ->
    at_external L s q ->
    after_external L s r s' ->
    lts_play s (pcons (li_sig q) r p). *)

End LTS.

(** ** Embed Calling Conventions *)
Section CC.

  (** We treat liB as the implementation. *)
  Context {liA liB} (cc: callconv liA liB).
  Context (se1 se2: Genv.symtbl).
  (** Translate a low level liB to high level liA. The first choice is made
    angelically because 1) there is usually at most one abstract representation;
    2) a more refined computation includes behaviors on more abstract
    representations, which means the computation is described from more angles.

    The second choice is made demonically because for an abstract state, its
    refinement implements one of the concrete representations.

    As for the choice of worlds, ... *)

  (* FIXME: left vs. right *)
  Definition cc_left: subst liA liB :=
    fun _ '(li_sig qb) =>
      sup w, sup { qa | match_query cc w qa qb },
      query_int qa >>= (fun ra => inf { rb | match_reply cc w ra rb }, ret rb).

  (** Translate high level liA into low level liB *)
  Definition cc_right: subst liB liA :=
    fun _ '(li_sig qa) =>
      inf w, inf { qb | match_query cc w qa qb },
      query_int qb >>= (fun rb => sup { ra | match_reply cc w ra rb }, ret ra).

  Lemma cc_epsilon: cc_left @ cc_right [= identity.
  Proof.
    intros ? [qb]. unfold identity, cc_left, cc_right, compose.
    rewrite Sup.mor. apply sup_iff. intros w.
    unfold fsup. rewrite Sup.mor.
    apply sup_iff. intros [qa Hq]. cbn.
    rewrite apply_bind. unfold bind.
    unfold query_int. rewrite apply_int_r.
    rewrite Inf.mor. apply (inf_at w).
    unfold finf. rewrite Inf.mor.
    apply (inf_at (exist _ qb Hq)). cbn.
    repeat setoid_rewrite Sup.mor.
    apply sup_iff. intros [rb|].
    - rewrite FCD.ext_ana. cbn.
      rewrite Sup.mor_join.
      apply join_lub.
      + rewrite FCD.ext_ana. cbn.
        unfold int. eapply (sup_at None). reflexivity.
      + rewrite !Sup.mor.
        apply sup_iff. intros [ra Hr]. cbn.
        unfold ret. rewrite FCD.ext_ana.
        rewrite FCD.ext_ana. cbn.
        apply join_lub.
        * eapply (sup_at None). reflexivity.
        * rewrite !Inf.mor.
          apply (inf_at (exist _ rb Hr)). cbn.
          unfold apply at 1. rewrite FCD.ext_ana. cbn.
          rewrite FCD.ext_ana.
          unfold int. apply (sup_at (Some rb)). reflexivity.
    - rewrite FCD.ext_ana. cbn.
      rewrite FCD.ext_ana. cbn.
      unfold int. apply (sup_at None). reflexivity.
  Qed.


  Lemma cc_eta: identity [= cc_right @ cc_left.
  Proof.
    intros ? [qa]. unfold identity, cc_left, cc_right, compose.
    rewrite Inf.mor. apply inf_iff. intros w.
    unfold finf. rewrite Inf.mor.
    apply inf_iff. intros [qb Hq]. cbn.
    unfold query_int. intm.
    unfold bind. rewrite Sup.mor. apply (sup_at w).
    unfold fsup. rewrite Sup.mor.
    apply (sup_at (exist _ qa Hq)). cbn.
    repeat setoid_rewrite Sup.mor.
    unfold int at 1. apply sup_iff. intros [ra|].
    - apply (sup_at (Some ra)).
      rewrite FCD.ext_ana. cbn.
      rewrite Sup.mor_join. apply join_r.
      rewrite !Inf.mor.
      apply inf_iff. intros [rb Hr]. cbn.
      unfold ret.
      rewrite !FCD.ext_ana. cbn.
      apply join_r.
      rewrite Sup.mor.
      apply (sup_at (exist _ ra Hr)). cbn.
      setoid_rewrite FCD.ext_ana. cbn.
      rewrite FCD.ext_ana. reflexivity.
    - apply (sup_at None).
      rewrite FCD.ext_ana. cbn.
      rewrite FCD.ext_ana. cbn. reflexivity.
  Qed.

  (** In particular, the calling conventions in CompCertO forms an adjunction *)
  Program Definition cc_adjunction: poset_adjunction liA liB :=
    {|
      left_arrow := cc_left;
      right_arrow := cc_right;
      epsilon := cc_epsilon;
      eta := cc_eta;
    |}.

End CC.

Lemma cc_adj_righr_eqv {liA liB} (cc: callconv liA liB):
  rc_adj_right cc = cc_right cc.
Proof.
  unfold rc_adj_right, cc_refconv, cc_right.
  apply antisymmetry.
  - cbn. intros ? [ qa ].
    apply inf_iff. intros w.
    apply inf_iff. intros [ qb Hq ]. cbn.
    unfold query_int. eapply inf_at. eapply (inf_at (li_sig qb)).
    eapply (finf_at (match_reply cc w)).
    exists (match_reply cc w). split.
    + constructor. auto.
    + reflexivity.
    + reflexivity.
  - cbn. intros ? [ qa ].
    apply inf_iff. intros ?. apply inf_iff. intros [ qb ].
    apply inf_iff. intros [ Rr [Rr' [HRr Hsub]]]. cbn.
    inv HRr. depsubst.
    apply (inf_at w). apply (finf_at qb). auto.
    unfold query_int. unfold int. sup_intro [rb|].
    + fcd_simpl. apply join_lub.
      * apply (sup_at None). fcd_simpl. reflexivity.
      * apply (sup_at (Some rb)).
        fcd_simpl. apply join_r. sup_intro [ ra Hr ].
        eapply (fsup_at ra). apply Hsub. auto. cbn. reflexivity.
    + fcd_simpl. apply (sup_at None). fcd_simpl. reflexivity.
Qed.

Lemma cc_adj_left_eqv {liA liB} (cc: callconv liA liB):
  rc_adj_left cc = cc_left cc.
Proof.
  unfold rc_adj_left, cc_refconv, cc_left.
  apply antisymmetry.
  - cbn. intros ? [ qb ].
    apply sup_iff. intros ?. apply sup_iff. intros [ qa ].
    apply sup_iff. intros [ Rr [Rr' [HRr Hsub]]]. cbn.
    inv HRr. depsubst.
    apply (sup_at w). apply (fsup_at qa). auto.
    unfold query_int. unfold int. sup_intro [ra|].
    + fcd_simpl. apply join_lub.
      * apply (sup_at None). fcd_simpl. reflexivity.
      * apply (sup_at (Some ra)).
        fcd_simpl. apply join_r. inf_intro [ rb Hr ].
        eapply (finf_at rb). apply Hsub. auto. reflexivity.
    + fcd_simpl. apply (sup_at None). fcd_simpl. reflexivity.
  - cbn. intros ? [ qb ].
    apply sup_iff. intros w.
    apply sup_iff. intros [ qa Hq ]. cbn.
    unfold query_int. eapply sup_at. eapply (sup_at (li_sig qa)).
    eapply (fsup_at (match_reply cc w)).
    exists (match_reply cc w). split.
    + constructor. auto.
    + reflexivity.
    + reflexivity.
Qed.

(* Note: it's hard to imply the [esig] from the context, since
   higher-order unification is generally difficult, i.e. to imply [E] from [E X] *)

(** ** Monotonicity of Embedding *)
Section FSIM.

  Context {liA1 liA2} (ccA: callconv liA1 liA2).
  Context {liB1 liB2} (ccB: callconv liB1 liB2).
  Context (se1 se2: Genv.symtbl).
  Context {state1 state2: Type}.
  Context (L1: lts liA1 liB1 state1) (L2: lts liA2 liB2 state2).
  Context (index: Type) (order: index -> index -> Prop)
          (match_states: Genv.symtbl -> Genv.symtbl -> ccworld ccB ->index -> state1 -> state2 -> Prop).
  Hypothesis FSIM:
    forall wB, fsim_properties ccA ccB se1 se2 wB L1 L2 index order (match_states se1 se2 wB).

  Lemma ang_fsim_embed:
    ang_lts_spec L1 [= (cc_right ccB) @ ang_lts_spec L2 @ (cc_left ccA).
  Proof.
    intros k [qb1]. unfold ISpec.compose.
    unfold ang_lts_spec at 1.
    apply sup_iff. intros steps.
    apply sup_iff. intros [s H1]. cbn.
    unfold finf. rewrite Inf.mor.
    apply inf_iff. intros wB. specialize (FSIM wB).
    rewrite Inf.mor.
    apply inf_iff. intros [qb2 Hqb].
    unfold query_int. intm.
    setoid_rewrite Sup.mor.
    setoid_rewrite apply_ret.
    setoid_rewrite Sup.mor.
    unfold bind. repeat setoid_rewrite Sup.mor.
    apply sup_at with (i := steps).
    edestruct (fsim_match_initial_states FSIM) as (i & s2 & H2 & Hs); eauto.
    eapply (sup_at (exist _ s2 H2)). cbn.
    clear H1 H2 Hqb. revert i s s2 Hs.
    induction steps; eauto using bot_lb.
    intros i s1 s2 Hs. cbn.
    repeat apply join_lub.
    - apply sup_iff. intros [s1' Hstep]. cbn.
      rewrite !Sup.mor_join.
      apply join_l. apply join_l.
      assert (exists i s2', Star L2 s2 E0 s2' /\ match_states se1 se2 wB i s1' s2') as (i' & s2' & Hstep2 & Hs').
      {
        revert i s2 Hs. pattern s1, s1'. eapply star_E0_ind; eauto; clear s1 s1' Hstep.
        - intros s1 i s2 Hs. exists i, s2; split; eauto using star_refl.
        - intros s1 s1' s1'' Hstep1 IHstar i s2 Hs.
          edestruct (simulation_star FSIM) as (i' & s2' & Hstep2 & Hs'); eauto using star_one.
          specialize (IHstar _ _ Hs') as (i'' & s2'' & Hstep2' & Hs'').
          eexists i'', s2''. split; eauto.
          eapply star_trans; eauto.
      }
      repeat setoid_rewrite Sup.mor.
      eapply (sup_at (exist _ s2' Hstep2)). cbn.
      specialize (IHsteps _ _ _ Hs'). apply IHsteps.
    - apply sup_iff. intros [qa1 H1]. cbn.
      rewrite !Sup.mor_join.
      apply join_l. apply join_r.
      edestruct @fsim_match_external as (w & qa2 & H2 & Hqa & _ & Hrx); eauto.
      setoid_rewrite Sup.mor.
      setoid_rewrite Sup.mor.
      eapply (sup_at (exist _ qa2 H2)). cbn.
      rewrite apply_bind. unfold query_int.
      rewrite apply_int_r.
      unfold bind. unfold cc_left at 2.
      repeat setoid_rewrite Sup.mor.
      eapply (sup_at w).
      eapply (sup_at (exist _ qa1 Hqa)). cbn.
      unfold query_int. unfold bind.
      apply sup_iff. intros [ra1|].
      + rewrite FCD.ext_ana. cbn.
        apply join_lub.
        * apply (sup_at (Some ra1)).
          rewrite FCD.ext_ana. cbn.
          rewrite !Sup.mor_join. apply join_l.
          rewrite FCD.ext_ana. cbn.
          rewrite FCD.ext_ana. cbn. reflexivity.
        * apply (sup_at (Some ra1)).
          rewrite FCD.ext_ana. cbn.
          rewrite !Sup.mor_join. apply join_r.
          repeat setoid_rewrite Inf.mor.
          apply inf_iff. intros [ra2 Hr]. cbn.
          unfold ret at 2. cbn.
          repeat setoid_rewrite FCD.ext_ana. cbn.
          rewrite !Sup.mor_join. apply join_r.
          setoid_rewrite Sup.mor.
          apply sup_iff. intros [s' H1'].
          specialize (Hrx _ _ _ Hr H1') as (i' & s2' & H2' & Hs'). cbn.
          setoid_rewrite Sup.mor.
          apply (sup_at (exist _ s2' H2')). cbn.
          specialize (IHsteps _ _ _ Hs').
          etransitivity.
          -- instantiate (1 := FCD.ext _ _). rstep. reflexivity.
          -- rewrite IHsteps. unfold apply.
             rewrite FCD.ext_ext. unfold t. rewrite FCD.ext_ext.
             eapply ext_proper_ref'.
             ++ split. intros a b Hab. rstep. now apply pbind_mor.
             ++ split. intros a b Hab. repeat rstep. now constructor.
             ++ intros x. rewrite FCD.ext_ana. cbn. apply join_r. reflexivity.
      + rewrite FCD.ext_ana. cbn.
        apply (sup_at None).
        repeat (setoid_rewrite FCD.ext_ana; cbn).
        reflexivity.
    - apply sup_iff. intros [rb1 H1]. cbn.
      rewrite !Sup.mor_join. apply join_r.
      edestruct @fsim_match_final_states as (rb2 & H2 & Hr); eauto.
      repeat setoid_rewrite Sup.mor.
      apply (sup_at (exist _ rb2 H2)). cbn.
      rewrite apply_ret.
      unfold ret at 3. rewrite FCD.ext_ana. cbn.
      apply (sup_at (exist _ rb1 Hr)). cbn.
      reflexivity.
  Qed.

End FSIM.

Section SEM.

  Context {liA1 liA2} (ccA: callconv liA1 liA2).
  Context {liB1 liB2} (ccB: callconv liB1 liB2).
  Context (L1: semantics liA1 liB1) (L2: semantics liA2 liB2).
  Context (se: Genv.symtbl).

  Hypothesis FSIM: forward_simulation ccA ccB L1 L2.
  Hypothesis HSE: forall wB, match_senv ccB wB se se.
  Hypothesis HSK: Genv.valid_for (skel L1) se.

  Lemma ang_fsim_embed':
    ang_lts_spec (L1 se) [= (cc_right ccB) @ ang_lts_spec (L2 se) @ (cc_left ccA).
  Proof.
    pose proof (ang_fsim_embed ccA ccB).
    destruct FSIM as [ [ ] ]. eapply H.
  Abort.

End SEM.

Require Import compcert.common.CategoricalComp.

(** ** Functoriality of the embedding *)
(** We prove the embedding preserves composition, i.e. ⟦L1⟧ ∘ ⟦L2⟧ ⊑ ⟦L1 ∘ L2⟧ *)
Section COMP.

  Context {liA liB liC} (L1: semantics liB liC) (L2: semantics liA liB).
  Context {L} (COMP: comp_semantics L1 L2 = Some L).

  Lemma comp_embed se:
    ang_lts_spec (L1 se) @ ang_lts_spec (L2 se) [= ang_lts_spec (L se).
  Proof.
    Local Opaque comp_semantics'.
    intros _ [qc]. unfold comp_semantics, option_map in COMP.
    destruct Linking.link; try congruence. inv COMP.
    unfold ISpec.compose. unfold ang_lts_spec at 2.
    rewrite Sup.mor. apply sup_iff. intros steps1.
    setoid_rewrite Sup.mor. apply sup_iff.
    intros [s1 Hinit]. cbn. unfold fsup. rewrite sup_sup.
    exploit @comp_initial_state_intro. eapply Hinit. intro Hinit'.
    eapply (sup_at (exist _ (st1 _ _ s1) Hinit')). cbn.
    clear Hinit Hinit'. revert s1. induction steps1.
    - intros s. apply (sup_at 0%nat). cbn.
      rewrite Sup.mor_bot. reflexivity.
    - intros s1. cbn. rewrite !Sup.mor_join. repeat apply join_lub.
      + setoid_rewrite Sup.mor.
        apply sup_iff. intros [s1' Hstep1]. cbn.
        exploit @star_internal1. apply Hstep1. intros Hstep.
        specialize (IHsteps1 s1'). etransitivity. apply IHsteps1.
        apply sup_iff. intros steps. apply (sup_at (S steps)).
        cbn. apply join_l. apply join_l.
        eapply fsup_at. apply Hstep. reflexivity.
      + setoid_rewrite Sup.mor. apply sup_iff.
        intros [qb1 Hext1]. cbn.
        rewrite apply_bind. unfold query_int.
        rewrite apply_int_r. unfold bind. unfold ang_lts_spec at 2.
        rewrite Sup.mor. setoid_rewrite Sup.mor.
        apply sup_iff. intros steps2.
        apply sup_iff. intros [s2 Hinit2]. cbn.
        rewrite lts_spec_step.
        apply join_l. apply join_l.
        eapply fsup_at. apply star_one. eapply step_push; eauto.

        clear Hext1 Hinit2. revert s2. induction steps2; intros s2; cbn.
        * rewrite Sup.mor_bot. apply bot_lb.
        * rewrite !Sup.mor_join. repeat apply join_lub.
          -- setoid_rewrite Sup.mor. apply sup_iff.
             intros [s2' H2]. cbn. specialize (IHsteps2 s2').
             etransitivity. apply IHsteps2.
             apply sup_iff. intros steps. apply (sup_at (S steps)). cbn.
             apply join_l. apply join_l.
             eapply fsup_at. apply star_internal2; eauto. reflexivity.
          -- setoid_rewrite Sup.mor. apply sup_iff.
             intros [qa Hext2]. cbn.
             unfold bind. unfold query_int.
             setoid_rewrite Sup.mor at 2. setoid_rewrite Sup.mor at 1.
             apply sup_iff.
             assert (Hcrash: (FCD.emb (@pmove (sig liA) _ _ qa)) [=
                               sup n : nat, ang_lts_spec' ((comp_semantics' L1 L2 p) se) n (st2 L1 L2 s1 s2)).
             {
               apply (sup_at 1%nat). cbn.
               apply join_l. apply join_r.
               eapply fsup_at. econstructor; eauto.
               unfold bind. unfold query_int.
               setoid_rewrite Sup.mor. apply (sup_at None).
               rewrite FCD.ext_ana. cbn. reflexivity.
             }
             intros [ra|].
             ++ setoid_rewrite FCD.ext_ana. cbn.
                rewrite Sup.mor_join. apply join_lub.
                ** rewrite FCD.ext_ana. apply Hcrash.
                ** setoid_rewrite Sup.mor at 2. rewrite Sup.mor.
                   apply sup_iff. intros [s2' Haft]. cbn.
                   pose proof @fmap_cons as fc. unfold bind in fc.
                   rewrite fc. clear fc.
                   apply join_lub.
                   --- apply Hcrash.
                   --- specialize (IHsteps2 s2').
                       rewrite IHsteps2.
                       rewrite Sup.mor. apply sup_iff. intros steps.
                       apply (sup_at (S steps)). cbn.
                       apply join_l. apply join_r.
                       eapply fsup_at. econstructor; eauto.
                       unfold bind. unfold query_int.
                       setoid_rewrite Sup.mor. apply (sup_at (Some ra)).
                       rewrite FCD.ext_ana. cbn. apply join_r.
                       apply ext_proper_ref; try typeclasses eauto.
                       intros c. reflexivity.
                       eapply fsup_at. econstructor; eauto. reflexivity.
             ++ rewrite FCD.ext_ana. cbn.
                rewrite FCD.ext_ana. apply Hcrash.
          -- setoid_rewrite Sup.mor. apply sup_iff.
             intros [rb Hfinal2]. cbn.
             unfold ret. rewrite FCD.ext_ana. cbn.
             setoid_rewrite Sup.mor. apply sup_iff.
             intros [s1' Haft1]. cbn.
             specialize (IHsteps1 s1').
             etransitivity. apply IHsteps1.
             apply sup_iff. intros steps. apply (sup_at (S steps)).
             cbn. apply join_l. apply join_l.
             eapply fsup_at. apply star_one. eapply step_pop; eauto.
             reflexivity.
      + setoid_rewrite Sup.mor. apply sup_iff.
        intros [rc Hfinal1]. cbn. unfold ret.
        setoid_rewrite FCD.ext_ana. cbn.
        apply (sup_at 1%nat). cbn. apply join_r.
        eapply fsup_at. constructor; eauto. reflexivity.
  Qed.

End COMP.
