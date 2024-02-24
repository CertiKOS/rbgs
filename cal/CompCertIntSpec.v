From Coq Require Import
     Relations RelationClasses
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
From cal Require Import RefConv.

(* Import ISpec. *)

Import RefConv.M.

Lemma sim_refl {E A} (x: M.t E A) :
  M.sim x x.
Proof. reflexivity. Qed.

Hint Constructors M.sim.
Hint Resolve sim_refl.

Lemma sim_sup {E I A} (x y: I -> M.t E A) :
  (forall i, M.sim (x i) (y i)) -> M.sim (⊔ i, x i) (⊔ i, y i).
Proof.
  intros. constructor. intros i. econstructor. eauto.
Qed.

Lemma sim_fsup {E I A} (x y: I -> M.t E A) (P: I -> Prop) :
  (forall i, P i -> M.sim (x i) (y i)) ->
  M.sim (⊔ { i | P i }, x i) (⊔ { i | P i }, y i).
Proof.
  intros. constructor. intros [i Hi]. econstructor. eauto.
Qed.

(* TODO: move to module M *)
Definition join {E A} (x y: M.t E A) := ⊔ b: bool, if b then x else y.
Definition meet {E A} (x y: M.t E A) := ⊓ b: bool, if b then x else y.
Infix "⊓" := meet (at level 40, left associativity).
Infix "⊔" := join (at level 50, left associativity).

Definition assert {E A} (P: Prop) (x: M.t E A): M.t E A := ⊔ H: P, x.
Definition assume {E A} (P: Prop) (x: M.t E A): M.t E A := ⊓ H: P, x.
Notation "'assert' P ; x" := (assert P x) (at level 65).
Notation "'assume' P ; x" := (assume P x) (at level 65).

Definition bot {E A}: M.t E A := ⊔ i: Empty_set, match i with end.
Definition top {E A}: M.t E A := ⊓ i: Empty_set, match i with end.
Notation "⊥" := bot.
Notation "⊤" := top.

Lemma bot_lb {E A} (x: M.t E A) :
  M.sim bot x.
Proof. constructor. intros [ ]. Qed.

Lemma join_lub {E A} (x y z: M.t E A) :
  M.sim x z -> M.sim y z -> M.sim (x ⊔ y) z.
Proof.
  intros Hx Hy. unfold join.
  constructor. intros [|]; auto.
Qed.

Lemma join_l {E A} (x y z: M.t E A) :
  M.sim x y -> M.sim x (y ⊔ z).
Proof.
  intro. etransitivity; eauto.
  eapply sim_sup_r with (i := true). reflexivity.
Qed.

Lemma join_r {E A} (x y z: M.t E A) :
  M.sim x z -> M.sim x (y ⊔ z).
Proof.
  intro. etransitivity; eauto.
  eapply sim_sup_r with (i := false). reflexivity.
Qed.

Definition query_int {li} := @eli_intro li.

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

    Fixpoint dem_lts_spec' (n: nat) (s: state L) se: M.t liA (reply liB) :=
      match n with
      | O => ⊥
      | S n =>
          assert (safe (L se) s);
          (* internal step *)
          (⊓ { s' | Step (L se) s E0 s' }, dem_lts_spec' n s' se) ⊓
          (* external call *)
          (⊓ { q | at_external (L se) s q },
           r ← query_int q se;
           assert (exists s', after_external (L se) s r s');
           ⊓ { s' | after_external (L se) s r s' }, dem_lts_spec' n s' se) ⊓
          (* final state *)
          (⊓ { r | final_state (L se) s r }, M.Ret r)
      end.

    Definition dem_lts_spec: subst liA liB :=
      fun _ '(eli_intro q se) => ⊔ n,
        assert (exists s, initial_state (L se) q s);
        ⊔ { s | initial_state (L se) q s }, dem_lts_spec' n s se.

  End DEM.

  (** *** Angelic Semantics *)
  Section ANG.

    Fixpoint ang_lts_exec (n: nat) (s: state L) se: M.t liA (reply liB) :=
      match n with
      | O => ⊥
      | S n =>
          (* internal step *)
          (⊔ { s' | Star (L se) s E0 s' }, ang_lts_exec n s' se) ⊔
          (* external call *)
          (⊔ { q | at_external (L se) s q },
           r ← query_int q se;
           ⊔ { s' | after_external (L se) s r s' }, ang_lts_exec n s' se) ⊔
          (* final step *)
          (⊔ { r | final_state (L se) s r }, M.Ret r)
      end.

    Definition ang_lts_spec' sk: subst liA liB :=
      fun _ '(eli_intro q se) =>
        assume (Genv.valid_for sk se);
        ⊔ n, ⊔ { s | initial_state (L se) q s }, ang_lts_exec n s se.

    Definition ang_lts_spec: subst liA liB := ang_lts_spec' (skel L).

    (** Executing one step in the FCD specification *)
    Lemma lts_spec_step s se:
      M.bisim
        (⊔ n, ang_lts_exec n s se)
        ((⊔ { s' | Star (L se) s E0 s' }, ⊔ n, ang_lts_exec n s' se) ⊔
         (⊔ { q | at_external (L se) s q },
           ⊔ n,
           r ← query_int q se;
           ⊔ { s' | after_external (L se) s r s' }, ang_lts_exec n s' se) ⊔
         (⊔ { r | final_state (L se) s r }, M.Ret r)).
    Proof.
      apply antisymmetry.
      - constructor. intros i.
        destruct i; cbn; eauto using bot_lb.
        repeat apply join_lub.
        + apply join_l. apply join_l.
          apply sim_fsup. intros s' H. eauto.
        + apply join_l. apply join_r.
          apply sim_fsup. intros q H.
          econstructor. eauto.
        + apply join_r. eauto.
      - repeat apply join_lub.
        + constructor. intros [s' H]. cbn.
          constructor. intros n.
          eapply sim_sup_r with (i := S n). cbn.
          apply join_l. apply join_l.
          eapply sim_fsup_r with (i := s'); eauto.
        + constructor. intros [q H]. cbn.
          constructor. intros n.
          eapply sim_sup_r with (i := (S n)). cbn.
          apply join_l. apply join_r.
          eapply sim_fsup_r with (i := q); eauto.
        + constructor. intros [r H]. cbn.
          eapply sim_sup_r with (i := 1%nat). cbn.
          apply join_r. eapply sim_fsup_r with (i := r); eauto.
    Qed.

    Lemma lts_spec_step' s se:
      M.sim
        (⊔ n, ang_lts_exec (S n) s se)
        (⊔ n, ang_lts_exec n s se).
    Proof. constructor. intros i. eauto. Qed.

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

(** The skeleton is used for choosing a compatible symbol table. So a larger
  skeleton accepts less symbol tables and thus leads to less behavior. *)
(* Instance skel_order_proper {liA liB} (L: semantics liA liB): *)
(*   Proper (Linking.linkorder ++> M.sim_) (ang_lts_spec' L). *)
(* Proof. *)
(*   intros sk1 sk2 Hsk. intros k [qb se]. cbn. *)
(*   apply assume_r. intros Hv. *)
(*   apply assume_l. reflexivity. *)
(*   eapply Genv.valid_for_linkorder; eauto. *)
(* Qed. *)

(* Note: it's hard to imply the [esig] from the context, since
   higher-order unification is generally difficult, i.e. to imply [E] from [E X] *)

Lemma assume_l {E A} (P : Prop) (x y : M.t E A) :
  P -> M.sim x y -> M.sim (assume P; x) y.
Proof. intros Hxy HP. constructor; eauto. Qed.

Lemma bind_join {E A B} (x y: M.t E A) (f: A -> M.t E B) :
  M.bisim (bind (x ⊔ y) f) ((bind x f) ⊔ (bind y f)).
Proof.
  split; cbn.
  - constructor. intros [ | ]; [ apply join_l | apply join_r ]; eauto.
  - apply join_lub.
    apply sim_sup_r with (i := true). reflexivity.
    apply sim_sup_r with (i := false). reflexivity.
Qed.

Lemma apply_join {E F A} (x y: M.t F A) (z: E ⤳ F) :
  M.bisim ((x ⊔ y) // z) ((x // z) ⊔ (y // z)).
Proof.
  split; cbn.
  - constructor. intros [ | ]; [ apply join_l | apply join_r ]; eauto.
  - apply join_lub.
    apply sim_sup_r with (i := true). reflexivity.
    apply sim_sup_r with (i := false). reflexivity.
Qed.

Instance apply_proper_sim {E F A}:
  Proper (bisim_ ==> bisim ==> sim) (@apply E F A).
Proof.
(*   intros s1 s2 Hs t1 t2 Ht. induction Ht; cbn; try econstructor; eauto. *)
(*   apply bind_proper_sim; eauto. *)
(* Qed. *)
Admitted.

Instance sim_proper_ {E F}:
  Proper (M.bisim ==> M.bisim ==> iff) (@M.sim E F).
Proof.
Admitted.

(* Opaque join. *)

(** ** Monotonicity of Embedding *)
Section SEM.

  Context {liA1 liA2} (ccA: callconv liA1 liA2).
  Context {liB1 liB2} (ccB: callconv liB1 liB2).
  Context (L1: semantics liA1 liB1) (L2: semantics liA2 liB2).
  Variable (sk: AST.program unit unit).
  Hypothesis HSK: Linking.linkorder (skel L1) sk.
  Hypothesis FSIM: forward_simulation ccA ccB L1 L2.

  Lemma ang_fsim_embed' :
    ang_lts_spec' L1 sk ≲ (right_arrow (cc_rc ccB)) ∘ ang_lts_spec' L2 sk ∘ (left_arrow (cc_rc ccA)).
  Proof.
    intros k [qb1 se1]. unfold compose. cbn.
    apply sim_inf_r. intros a.
    apply sim_inf_r. intros [qb2 se2]. cbn.
    apply sim_inf_r. intros [Rrb Hrb]. cbn.
    rc_inversion Hrb. subst_dep.
    rename H4 into Hse. rename H5 into Hqb. rename w into wB.
    clear Hrel. rename Hsub into HRrb.
    apply sim_inf_r. intros Hv2.
    assert (Hv1: Genv.valid_for sk se1).
    { rewrite @match_senv_valid_for; eauto. }
    apply assume_l. exact Hv1.
    apply sim_sup_l. intros steps.
    apply sim_sup_l. intros [s H1]. cbn.
    destruct FSIM as [[? ? match_states Hskeq Hfp Hlts Hwf]].
    clear FSIM. rename Hlts into FSIM.
    assert (Hsk1: Genv.valid_for (skel L1) se1).
    { eapply Genv.valid_for_linkorder; eauto. }
    specialize (FSIM se1 se2 wB Hse Hsk1).
    clear Hv1 Hv2 Hskeq.
    apply sim_sup_r with (i := steps).
    edestruct (fsim_match_initial_states FSIM) as (i & s2 & H2 & Hs); eauto.
    eapply sim_sup_r with (i0 := (exist _ s2 H2)). cbn.
    clear H1 H2 Hqb. revert i s s2 Hs.
    induction steps; eauto using bot_lb.
    intros i s1 s2 Hs. cbn.
    repeat apply join_lub.
    - apply sim_sup_l. intros [s1' Hstep]. cbn.
      apply sim_sup_r with (i0 := true). cbn. (* join_l *)
      apply sim_sup_r with (i0 := true). cbn. (* join_l *)
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
      apply sim_sup_r with (i0 := (exist _ s2' Hstep2)). cbn.
      eapply IHsteps; eauto.
    - apply sim_sup_l. intros [qa1 H1]. cbn.
      apply sim_sup_r with (i0 := true). cbn. (* join_l *)
      apply sim_sup_r with (i0 := false). cbn. (* join_r *)
      edestruct @fsim_match_external as (w & qa2 & H2 & Hqa & Hse' & Hrx); eauto.
      apply sim_sup_r with (i0 := (exist _ qa2 H2)). cbn.
      eapply sim_sup_r. eapply sim_sup_r with (i0 := (eli_intro qa1 se1)).
      eapply sim_sup_r with (i0 := exist _ (match_reply ccA w) _). cbn.
      Unshelve. 2: { cbn. rc_econstructor; eauto. }
      constructor. intros ra1.
      apply sim_inf_r. intros [ra2 Hr]. cbn.
      apply sim_sup_l. intros [s' H1']. cbn.
      specialize (Hrx _ _ _ Hr H1') as (i' & s2' & H2' & Hs').
      eapply sim_sup_r with (i0 := (exist _ s2' H2')). cbn.
      eapply IHsteps; eauto.
    - apply sim_sup_l. intros [rb1 H1]. cbn.
      apply sim_sup_r with (i0 := false). cbn. (* join_r *)
      edestruct @fsim_match_final_states as (rb2 & H2 & Hr); eauto.
      apply sim_sup_r with (i0 := (exist _ rb2 H2)). cbn.
      eapply sim_sup_r with (i0 := exist _ rb1 _). cbn.
      Unshelve. 2: { cbn. apply HRrb. apply Hr. }
      reflexivity.
  Qed.

End SEM.

Lemma ang_fsim_embed {liA1 liA2 liB1 liB2} ccA ccB
      (L1: semantics liA1 liB1) (L2: semantics liA2 liB2):
  forward_simulation ccA ccB L1 L2 ->
  ang_lts_spec L1 ≲ (right_arrow (cc_rc ccB)) ∘ ang_lts_spec L2 ∘ (left_arrow (cc_rc ccA)).
Proof.
  intros FSIM. destruct FSIM as [[]].
  unfold ang_lts_spec. rewrite <- fsim_skel.
  apply ang_fsim_embed'.
  apply Linking.linkorder_refl.
  constructor. econstructor; eauto.
Qed.

Lemma ang_fsim_embed_cc_id {liA liB} (L1 L2: semantics liA liB):
  forward_simulation 1 1 L1 L2 ->
  ang_lts_spec L1 ≲ ang_lts_spec L2.
Proof.
  intros H. apply ang_fsim_embed in H.
  rewrite H. rewrite !cc_rc_id.
  rewrite right_arrow_id.
  rewrite left_arrow_id.
  rewrite compose_unit_r.
  rewrite compose_unit_l.
  reflexivity.
Qed.

Require Import compcert.common.CategoricalComp.

Lemma sup_sup {E I J A} (x: I -> J -> M.t E A) :
  M.bisim (⊔ i, ⊔ j, x i j) (⊔ j, ⊔ i, x i j).
Proof.
  split; do 2 (constructor; intros); do 2 econstructor; eauto.
Qed.

Lemma sup_bind {E I A B} (x: E A) (f: I -> A -> M.t E B):
  M.sim (M.Bind x (fun v => ⊔ i, f i v)) (⊔ i, M.Bind x (f i)).
Proof.
Abort.


(** ** Functoriality of the embedding *)
(** We prove the embedding preserves composition, i.e. ⟦L1⟧ ∘ ⟦L2⟧ ⊑ ⟦L1 ∘ L2⟧. *)
Section COMP.

  Context {liA liB liC} (L1: semantics liB liC) (L2: semantics liA liB).
  Context {L} (COMP: comp_semantics L1 L2 = Some L).
  Variable (sk: AST.program unit unit).
  Hypothesis HSK: Linking.linkorder (skel L) sk.

  Lemma comp_embed':
    ang_lts_spec' L1 sk ∘ ang_lts_spec' L2 sk ≲ ang_lts_spec' L sk.
  Proof.
    Local Opaque comp_semantics'.
    intros _ [qc se]. unfold comp_semantics, option_map in COMP.
    destruct Linking.link eqn: Hlk; try congruence. inv COMP. cbn.
    apply sim_inf_r. intros Hsk.
    eapply sim_inf_l. apply Hsk.
    apply sim_sup_l. intros steps1.
    apply sim_sup_l. intros [s1 Hinit]. cbn.
    setoid_rewrite sup_sup.
    exploit @comp_initial_state_intro. eapply Hinit. intro Hinit'.
    eapply sim_sup_r with (i := (exist _ (st1 _ _ s1) Hinit')). cbn.
    clear Hinit Hinit'. revert s1. induction steps1.
    - intros s. apply sim_sup_r with (i := 0%nat). cbn.
      constructor. intros [  ].
    - intros s1. cbn.
      apply sim_sup_l; intros [ | ]. cbn. (* apply join_lub *)
      apply sim_sup_l; intros [ | ].
      + apply sim_sup_l. intros [s1' Hstep1]. cbn.
        exploit @star_internal1. apply Hstep1. intros Hstep.
        specialize (IHsteps1 s1'). etransitivity. apply IHsteps1.
        apply sim_sup_l. intros steps. apply sim_sup_r with (i := S steps). cbn.
        apply join_l. apply join_l.
        eapply sim_fsup_r. apply Hstep. reflexivity.
      + apply sim_sup_l. intros [qb Hext1]. cbn.
        apply assume_l. apply Hsk.
        apply sim_sup_l. intros steps2.
        apply sim_sup_l. intros [s2 Hinit2]. cbn.
        rewrite lts_spec_step. apply join_l. apply join_l.
        eapply sim_fsup_r. apply star_one. eapply step_push; eauto.
        (* apply sim_sup_r with (i := steps2). *)

        clear Hext1 Hinit2. revert s2. induction steps2; intros s2; cbn.
        * apply sim_sup_l. intros [  ].
        * apply sim_sup_l. intros [ | ]. cbn.
          apply sim_sup_l. intros [ | ]. cbn.
          -- apply sim_sup_l. intros [ s2' H2 ]. cbn.
             etransitivity. apply IHsteps2.
             apply sim_sup_l. intros steps. apply sim_sup_r with (i := S steps). cbn.
             apply join_l. apply join_l.
             eapply sim_fsup_r. apply star_internal2; eauto. reflexivity.

          -- cbn. apply sim_sup_l. intros [ qa Hext2 ]. cbn.
             apply join_l. apply join_r.
             eapply sim_fsup_r. constructor. apply Hext2.
             constructor. intros ra.
             apply sim_sup_l. intros [s2' Haft]. cbn.
             rewrite IHsteps2.
             eapply sim_fsup_r. constructor. apply Haft.
             reflexivity.
          -- cbn. apply join_l. apply join_l.
             apply sim_sup_l. intros [rb Hfinal2]. cbn.
             apply sim_sup_l. intros [s1' Haft1]. cbn.
             rewrite IHsteps1.

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
