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

Definition assume {E : esig} (P : Prop) : ispec E unit :=
  inf H : P, ret tt.

Lemma assume_l {E A} (P : Prop) (x y : ispec E A) :
  x [= y -> P ->
  _ <- assume P; x [= y.
Proof.
  intros Hxy HP. unfold assume.
  inf_mor. eapply (inf_at HP).
  fcd_simpl. apply Hxy.
Qed.

Lemma assume_r {E A} (P : Prop) (x y : ispec E A) :
  (P -> x [= y) ->
  x [= _ <- assume P; y.
Proof.
  intros H. unfold assume.
  inf_intro HP. fcd_simpl.
  apply H. apply HP.
Qed.

(** * Embed CompCert Semantics into Game Semantics *)

(** ** Embed Labelled Tranition Systems *)
Section LTS.

  Context {liA liB} (L: semantics liA liB).

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

    Fixpoint dem_lts_spec' (n: nat) (s: state L) se: ispec liA (reply liB) :=
      match n with
      | O => bot
      | S n =>
          _ <- assert (safe (L se) s);
          (* internal step *)
          (inf { s' | Step (L se) s E0 s' }, dem_lts_spec' n s' se) &&
          (* external call *)
          (inf { q | at_external (L se) s q },
           r <- query_int q se;
           _ <- assert (exists s', after_external (L se) s r s');
           inf { s' | after_external (L se) s r s' }, dem_lts_spec' n s' se) &&
          (* final state *)
          (inf { r | final_state (L se) s r }, ret r)
      end.

    Definition dem_lts_spec: subst liA liB :=
      fun _ '(li_sig q se) => sup n,
        _ <- assert (exists s, initial_state (L se) q s);
        inf { s | initial_state (L se) q s }, dem_lts_spec' n s se.

  End DEM.

  (** *** Angelic Semantics *)
  Section ANG.

    Fixpoint ang_lts_exec (n: nat) (s: state L) se: ispec liA (reply liB) :=
      match n with
      | O => bot
      | S n =>
          (* internal step *)
          (sup { s' | Star (L se) s E0 s' }, ang_lts_exec n s' se) ||
          (* external call *)
          (sup { q | at_external (L se) s q },
           r <- query_int q se;
           sup { s' | after_external (L se) s r s' }, ang_lts_exec n s' se) ||
          (* final step *)
          (sup { r | final_state (L se) s r }, ret r)
      end.

    Definition ang_lts_spec' sk: subst liA liB :=
      fun _ '(li_sig q se) =>
        _ <- assume (Genv.valid_for sk se);
        sup n, sup { s | initial_state (L se) q s }, ang_lts_exec n s se.

    Definition ang_lts_spec: subst liA liB := ang_lts_spec' (skel L).

    (** Executing one step in the FCD specification *)
    Lemma lts_spec_step s se:
      sup n, ang_lts_exec n s se =
        (sup { s' | Star (L se) s E0 s' }, sup n, ang_lts_exec n s' se) ||
        (sup { q | at_external (L se) s q },
          r <- query_int q se;
         sup { s' | after_external (L se) s r s' }, sup n, ang_lts_exec n s' se) ||
        (sup { r | final_state (L se) s r }, ret r).
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
    Hypothesis DET: lts_determinate (L se) se.

    Lemma det_lts_spec_equiv:
      ang_lts_spec = dem_lts_spec.
    Proof. Abort.

  End DET.

End LTS.

Require Import CAL.

(** The skeleton is used for choosing a compatible symbol table. So a larger
  skeleton accepts less symbol tables and thus leads to less behavior. *)
Instance skel_order_proper {liA liB} (L: semantics liA liB):
  Proper (Linking.linkorder ++> ref) (ang_lts_spec' L).
Proof.
  intros sk1 sk2 Hsk. intros k [qb se]. cbn.
  apply assume_r. intros Hv.
  apply assume_l. reflexivity.
  eapply Genv.valid_for_linkorder; eauto.
Qed.

(* Note: it's hard to imply the [esig] from the context, since
   higher-order unification is generally difficult, i.e. to imply [E] from [E X] *)

Local Opaque normalize_rc.

(** ** Monotonicity of Embedding *)
Section SEM.

  Context {liA1 liA2} (ccA: callconv liA1 liA2).
  Context {liB1 liB2} (ccB: callconv liB1 liB2).
  Context (L1: semantics liA1 liB1) (L2: semantics liA2 liB2).
  Variable (sk: AST.program unit unit).
  Hypothesis HSK: Linking.linkorder (skel L1) sk.
  Hypothesis FSIM: forward_simulation ccA ccB L1 L2.

  Lemma ang_fsim_embed' :
    ang_lts_spec' L1 sk [= (right_arrow (cc_rc ccB)) @ ang_lts_spec' L2 sk @ (left_arrow (cc_rc ccA)).
  Proof.
    intros k [qb1 se1]. unfold compose. cbn.
    unfold rc_adj_right. inf_intro a. inf_intro [qb2 se2].
    inf_intro [Rrb Hrb]. rc_inversion Hrb. depsubst.
    rename H4 into Hse. rename H5 into Hqb. rename w into wB.
    clear Hrel. rename Hsub into HRrb.
    intm. inf_mor. inf_intro Hv2.
    assert (Hv1: Genv.valid_for sk se1).
    { rewrite @match_senv_valid_for; eauto. }
    apply (inf_at Hv1). intm.
    apply sup_iff. intros steps.
    apply sup_iff. intros [s H1]. cbn.
    destruct FSIM as [[? ? match_states Hskeq Hfp Hlts Hwf]].
    clear FSIM. rename Hlts into FSIM.
    assert (Hsk1: Genv.valid_for (skel L1) se1).
    { eapply Genv.valid_for_linkorder; eauto. }
    specialize (FSIM se1 se2 wB Hse Hsk1).
    clear Hv1 Hv2 Hskeq.
    intm. sup_mor. apply (sup_at steps).
    edestruct (fsim_match_initial_states FSIM) as (i & s2 & H2 & Hs); eauto.
    sup_mor. eapply (fsup_at s2). apply H2.
    clear H1 H2 Hqb. revert i s s2 Hs.
    induction steps; eauto using bot_lb.
    intros i s1 s2 Hs. cbn.
    repeat apply join_lub.
    - sup_intro [s1' Hstep]. apply join_l. apply join_l.
      assert (exists i s2', Star (L2 se2) s2 E0 s2' /\ match_states se1 se2 wB i s1' s2') as (i' & s2' & Hstep2 & Hs').
      {
        revert i s2 Hs. pattern s1, s1'. eapply star_E0_ind; eauto; clear s1 s1' Hstep.
        - intros s1 i s2 Hs. exists i, s2; split; eauto using star_refl.
        - intros s1 s1' s1'' Hstep1 IHstar i s2 Hs.
          edestruct (simulation_star FSIM) as (i' & s2' & Hstep2 & Hs'); eauto using star_one.
          specialize (IHstar _ _ Hs') as (i'' & s2'' & Hstep2' & Hs'').
          eexists i'', s2''. split; eauto.
          eapply star_trans; eauto.
      }
      sup_mor. eapply (fsup_at s2'). apply Hstep2.
      specialize (IHsteps _ _ _ Hs'). apply IHsteps.
    - sup_intro [qa1 H1]. apply join_l. apply join_r.
      edestruct @fsim_match_external as (w & qa2 & H2 & Hqa & Hse' & Hrx); eauto.
      sup_mor. eapply (fsup_at qa2). apply H2.
      unfold query_int. intm. unfold rc_adj_left at 3.
      sup_mor. eapply sup_at.
      sup_mor. eapply (sup_at (li_sig qa1 se1)).
      sup_mor. eapply (fsup_at (match_reply ccA w)).
      { rc_econstructor; eauto. }
      intm. sup_mor. apply sup_iff. intros [ ra1 | ].
      + fcd_simpl. apply join_lub.
        * apply (sup_at None). fcd_simpl. reflexivity.
        * apply (sup_at (Some ra1)).
          fcd_simpl. apply join_r.
          inf_intro [ra2 Hr]. intm.
          sup_intro [s' H1'].
          specialize (Hrx _ _ _ Hr H1') as (i' & s2' & H2' & Hs').
          eapply (fsup_at s2'). apply H2'.
          specialize (IHsteps _ _ _ Hs').
          rewrite IHsteps. reflexivity.
      + apply (sup_at None). fcd_simpl. reflexivity.
    - sup_intro [rb1 H1]. apply join_r.
      edestruct @fsim_match_final_states as (rb2 & H2 & Hr); eauto.
      sup_mor. apply (fsup_at rb2). apply H2.
      intm. sup_mor.
      apply (fsup_at rb1). apply HRrb. apply Hr.
      intm. reflexivity.
  Qed.

End SEM.

Lemma ang_fsim_embed {liA1 liA2 liB1 liB2} ccA ccB
      (L1: semantics liA1 liB1) (L2: semantics liA2 liB2):
  forward_simulation ccA ccB L1 L2 ->
  ang_lts_spec L1 [= (right_arrow (cc_rc ccB)) @ ang_lts_spec L2 @ (left_arrow (cc_rc ccA)).
Proof.
  intros FSIM. destruct FSIM as [[]].
  unfold ang_lts_spec. rewrite <- fsim_skel.
  apply ang_fsim_embed'.
  apply Linking.linkorder_refl.
  constructor. econstructor; eauto.
Qed.

Lemma ang_fsim_embed_cc_id {liA liB} (L1 L2: semantics liA liB):
  forward_simulation 1 1 L1 L2 ->
  ang_lts_spec L1 [= ang_lts_spec L2.
Proof.
  intros H. apply ang_fsim_embed in H.
  rewrite H. cbn -[LatticeProduct.cdlat_prod].
  rewrite !cc_rc_id.
  rewrite rc_adj_right_id. rewrite compose_unit_l.
  rewrite rc_adj_left_id. rewrite compose_unit_r.
  reflexivity.
Qed.

Require Import compcert.common.CategoricalComp.

(** ** Functoriality of the embedding *)
(** We prove the embedding preserves composition, i.e. ⟦L1⟧ ∘ ⟦L2⟧ ⊑ ⟦L1 ∘ L2⟧. *)
Section COMP.

  Context {liA liB liC} (L1: semantics liB liC) (L2: semantics liA liB).
  Context {L} (COMP: comp_semantics L1 L2 = Some L).
  Variable (sk: AST.program unit unit).
  Hypothesis HSK: Linking.linkorder (skel L) sk.

  Lemma comp_embed':
    ang_lts_spec' L1 sk @ ang_lts_spec' L2 sk [= ang_lts_spec' L sk.
  Proof.
    Local Opaque comp_semantics'.
    intros _ [qc se]. unfold comp_semantics, option_map in COMP.
    destruct Linking.link eqn: Hlk; try congruence. inv COMP.
    unfold ISpec.compose. unfold ang_lts_spec' at 2.
    inf_mor. inf_intro Hsk.
    apply (inf_at Hsk). intm. sup_intro steps1.
    sup_intro [s1 Hinit]. unfold fsup. rewrite sup_sup.
    exploit @comp_initial_state_intro. eapply Hinit. intro Hinit'.
    eapply (sup_at (exist _ (st1 _ _ s1) Hinit')). cbn.
    clear Hinit Hinit'. revert s1. induction steps1.
    - intros s. apply (sup_at 0%nat). cbn.
      rewrite Sup.mor_bot. reflexivity.
    - intros s1. cbn. rewrite !Sup.mor_join. repeat apply join_lub.
      + sup_intro [s1' Hstep1].
        exploit @star_internal1. apply Hstep1. intros Hstep.
        specialize (IHsteps1 s1'). etransitivity. apply IHsteps1.
        apply sup_iff. intros steps. apply (sup_at (S steps)).
        cbn. apply join_l. apply join_l.
        eapply fsup_at. apply Hstep. reflexivity.
      + sup_intro [qb1 Hext1]. unfold query_int. intm.
        apply assume_l; eauto.
        sup_intro steps2. sup_intro [s2 Hinit2].
        rewrite lts_spec_step. apply join_l. apply join_l.
        eapply fsup_at. apply star_one. eapply step_push; eauto.

        clear Hext1 Hinit2. revert s2. induction steps2; intros s2; cbn.
        * rewrite Sup.mor_bot. apply bot_lb.
        * rewrite !Sup.mor_join. repeat apply join_lub.
          -- sup_intro [s2' H2]. specialize (IHsteps2 s2').
             etransitivity. apply IHsteps2.
             apply sup_iff. intros steps. apply (sup_at (S steps)). cbn.
             apply join_l. apply join_l.
             eapply fsup_at. apply star_internal2; eauto. reflexivity.
          -- sup_intro [qa Hext2]. unfold query_int. intm.
             assert (Hcrash: (FCD.emb (@pmove (sig liA) _ _ (li_sig qa se))) [=
                               sup n : nat, ang_lts_exec ((comp_semantics' L1 L2 p) ) n (st2 L1 L2 s1 s2) se).
             {
               apply (sup_at 1%nat). cbn. apply join_l. apply join_r.
               eapply fsup_at. econstructor; eauto.
               unfold query_int. sup_mor. apply (sup_at None).
               fcd_simpl. reflexivity.
             }
             sup_intro [ra|].
             ++ fcd_simpl. apply join_lub.
                ** apply Hcrash.
                ** sup_intro [s2' Haft].
                   specialize (IHsteps2 s2').
                   rewrite IHsteps2. clear IHsteps2.
                   sup_intro steps. apply (sup_at (S steps)). cbn.
                   apply join_l. apply join_r.
                   eapply fsup_at. econstructor; eauto.
                   unfold query_int. sup_mor. apply (sup_at (Some ra)).
                   fcd_simpl. apply join_r.
                   sup_mor. eapply (fsup_at (st2 _ _ s1 s2')). now constructor.
                   apply ext_proper_ref; try typeclasses eauto.
                   intros c. reflexivity. reflexivity.
             ++ fcd_simpl. apply Hcrash.
          -- sup_intro [rb Hfinal2]. intm.
             sup_intro [s1' Haft1].
             specialize (IHsteps1 s1').
             etransitivity. apply IHsteps1.
             apply sup_iff. intros steps. apply (sup_at (S steps)).
             cbn. apply join_l. apply join_l.
             eapply fsup_at. apply star_one. eapply step_pop; eauto.
             reflexivity.
      + sup_intro [rc Hfinal1]. fcd_simpl.
        apply (sup_at 1%nat). cbn. apply join_r.
        eapply fsup_at. constructor; eauto. reflexivity.
  Qed.

End COMP.

Lemma comp_embed {liA liB liC} (L1: semantics liB liC) (L2: semantics liA liB) L:
  comp_semantics L1 L2 = Some L ->
  ang_lts_spec L1 @ ang_lts_spec L2 [= ang_lts_spec L.
Proof.
  intros COMP. unfold ang_lts_spec.
  rewrite <- (comp_embed' _ _ COMP). 2: apply Linking.linkorder_refl.
  unfold comp_semantics, option_map in COMP.
  destruct Linking.link eqn: Hlink; try congruence. inv COMP.
  cbn -[LatticeProduct.cdlat_prod].
  apply compose_proper_ref; apply skel_order_proper; now apply Linking.link_linkorder in Hlink.
Qed.

(*
(** ** Embed Calling Conventions *)
Section CC.

  (** We treat liB as the implementation. *)
  Context {liA liB} (cc: callconv liA liB).
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

Section CC_SE.

  Context {liA liB} (cc: callconv liA liB).
  Context (se1 se2: Genv.symtbl).

  Definition cc_l: subst liA liB :=
    fun _ '(li_sig qb) =>
      sup { w | match_senv cc w se1 se2 }, sup { qa | match_query cc w qa qb },
      query_int qa >>= (fun ra => inf { rb | match_reply cc w ra rb }, ret rb).

  Definition cc_r: subst liB liA :=
    fun _ '(li_sig qa) =>
      inf { w | match_senv cc w se1 se2 }, inf { qb | match_query cc w qa qb },
      query_int qb >>= (fun rb => sup { ra | match_reply cc w ra rb }, ret ra).

  Lemma cc_epsilon_se: cc_l @ cc_r [= identity.
  Proof. Admitted.

  Lemma cc_eta_se: identity [= cc_r @ cc_l.
  Proof. Admitted.

  Program Definition cc_adjunction_se: poset_adjunction liA liB :=
    {|
      left_arrow := cc_l;
      right_arrow := cc_r;
      epsilon := cc_epsilon_se;
      eta := cc_eta_se;
    |}.

End CC_SE.
*)
