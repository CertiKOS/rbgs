From Coq Require Import
     List Lia.
From models Require Import
     IntSpec.
From cal Require Import
     RefConv CompCertIntSpec
     IntSpecCAL.
From lattices Require Import
     Upset Downset FCD.
From structures Require Import
     Effects Lattice.
From compcert Require Import
     Coqlib
     AST Values Memory
     Globalenvs
     LanguageInterface
     Smallstep.
From compcertox Require Import
     Lifting CModule AbRel.
Import ListNotations ISpec.

Unset Asymmetric Patterns.

(** * CompCert Layers *)

(** The language interface "C simple" which does not include the memory *)
Inductive c_esig : esig :=
| c_event : val -> signature -> list val -> Genv.symtbl -> c_esig val.

Inductive c_rc: rc_rel (c_esig # mem) li_c :=
| c_rc_intro vf sg args e_c e_s m se:
  let R := (fun '(r, m) c_r => c_r = cr r m) in
  e_c = c_event vf sg args se -> e_s = est_intro m ->
  c_rc _ (etens_intro e_c e_s) _ (eli_intro (cq vf sg args m) se) R.

Close Scope Z_scope.
Record clight_layer {S1 S2} (L1: 0 ~> (li_c @ S1)%li) (L2: 0 ~> (li_c @ S2)%li) :=
  {
    clight_impl: cmodule;
    clight_rel: abrel S2 S1;

    clight_layer_ref:
      let MS := ang_lts_spec (((semantics clight_impl) @ S1)%lts)
      in L2 [= right_arrow (cc_rc clight_rel) @ MS @ L1;
  }.
Arguments clight_impl {_ _ _ _}.
Arguments clight_rel {_ _ _ _}.
Arguments clight_layer_ref {_ _ _ _}.

(*
Section CAT_APP.
  Context {M N sk1 sk2} `{!CategoricalComp.CategoricalLinkable (semantics M sk1) (semantics N sk2)}.

  Lemma cmodule_categorical_comp_simulation sk:
    forward_simulation
      1 1
      (CategoricalComp.comp_semantics' (semantics M sk1) (semantics N sk2) sk)
      (semantics (M ++ N) sk).
  Proof.
    etransitivity.
    2: { apply cmodule_categorical_comp_simulation.
         unfold CategoricalComp.CategoricalLinkable in *.
         cbn in *. apply H. }
    etransitivity.
    2: { apply lift_comp_component. }
    instantiate (1 := sk2).
    instantiate (1 := sk1).
    unfold skel_extend. reflexivity.
  Qed.

  Lemma cmodule_categorical_comp_simulation_lifted sk S:
    forward_simulation
      1 1
      (CategoricalComp.comp_semantics' (semantics M sk1 @ S) (semantics N sk2 @ S) sk)
      (semantics (M ++ N) sk @ S).
  Proof.
    pose proof (cmodule_categorical_comp_simulation sk) as HX.
    eapply (@lifting_simulation S) in HX.
    etransitivity. 2: apply HX.
    apply lift_categorical_comp2.
  Qed.
End CAT_APP.
 *)

Lemma cmodule_rel {S1 S2} M (R: abrel _ _):
  ang_lts_spec (semantics M @ S2) @ right_arrow (cc_rc R) [=
    right_arrow (cc_rc R) @ ang_lts_spec (semantics M @ S1).
Proof.
  pose proof (cmodule_abrel R M) as H.
  eapply ang_fsim_embed in H. rewrite H.
  cbn -[LatticeProduct.poset_prod].
  rewrite !compose_assoc.
  rewrite @rc_adj_epsilon. rewrite compose_unit_r. reflexivity.
Qed.

(** ** Composition *)
Section COMP.

  Context {Ks Kn Kf}
          (Ls: 0 ~> (li_c @ Ks)%li)
          (Ln: 0 ~> (li_c @ Kn)%li)
          (Lf: 0 ~> (li_c @ Kf)%li)
          (C1: clight_layer Ls Ln) (C2: clight_layer Ln Lf).
  Context C (HC: cmod_app (clight_impl C2) (clight_impl C1) = Some C).
  Context (HR: disjoint_abrel (clight_rel C2) (clight_rel C1)).
  Context (Hcomp: CategoricalComp.CategoricalLinkable
                    (semantics (clight_impl C2))
                    (semantics (clight_impl C1))).

  Local Obligation Tactic := idtac.

  (* Embedded version of layer_vcomp] from Compsition.v *)
  Program Definition clight_layer_compose: clight_layer Ls Lf :=
    {|
      clight_impl := C;
      clight_rel := abrel_comp (clight_rel C2) (clight_rel C1);
    |}.
  Next Obligation.
    destruct C1 as [M1 R1 Hsim1].
    destruct C2 as [M2 R2 Hsim2].
    Local Opaque LatticeProduct.poset_prod.
    cbn -[semantics right_arrow] in *. etransitivity.
    apply Hsim2. clear Hsim2.
    rewrite Hsim1. clear Hsim1.
    rewrite <- (compose_assoc _ (right_arrow (cc_rc R1)) _).
    rewrite cmodule_rel; eauto. rewrite compose_assoc.
    rewrite <- (compose_assoc _ (right_arrow R1) _).
    apply compose_proper_ref.
    {
      rewrite right_arrow_compose. apply right_arrow_monotonic.
      unfold cc_refconv.        (* we could not make it a coercion *)
      rewrite <- cc_rc_compose. apply cc_rc_ref.
      apply krel_comp_ref. exact HR.
    }
    rewrite <- compose_assoc.
    apply compose_proper_ref. 2: reflexivity.
    erewrite (comp_embed (semantics M2 @ Ks)%lts (semantics M1 @ Ks)%lts).
    2: { unfold CategoricalComp.comp_semantics. cbn.
         erewrite cmod_app_skel. reflexivity. apply HC. }
    apply ang_fsim_embed_cc_id.
    etransitivity. apply lift_categorical_comp2.
    apply lifting_simulation.
    apply cmodule_categorical_comp_simulation; eauto.
  Qed.

End COMP.

(** * Connection between the Strategy World and the CompCert World *)

Require Import Events.

Record rho_rel (U: Type) :=
  {
    rho_pred (se: Genv.symtbl) :> U -> mem -> Prop;
    rho_footprint : list (ident * Z);

    rho_ext (se: Genv.symtbl) : mem * U -> mem -> Prop :=
      fun '(m1, u) m2 =>
        Mem.extends m1 m2
        /\ (forall b ofs, locsp se rho_footprint b ofs -> loc_out_of_bounds m1 b ofs)
        /\ defined_on (fun b ofs => Mem.perm m2 b ofs Max Nonempty
                                /\ loc_out_of_bounds m1 b ofs) m2
        /\ rho_pred se u m2;

    rho_invar : forall se u m m',
      rho_pred se u m ->
      Mem.unchanged_on (locsp se rho_footprint) m m' ->
      rho_pred se u m';
    rho_valid : forall se u m b ofs,
      rho_pred se u m -> (locsp se rho_footprint) b ofs -> Mem.valid_block m b;
    rho_perm : forall se u m b ofs,
      rho_pred se u m -> (locsp se rho_footprint) b ofs -> Mem.perm m b ofs Max Nonempty;
  }.

Arguments rho_footprint {_} _.
Arguments rho_ext {_} _.

Inductive rho_rc_reply {U:Type} (rho: rho_rel U) se m1 m2 : val * (mem * U) -> val * mem -> Prop :=
| rho_rc_reply_intro r1 r2 u n1 n2
   (ACCMS: Mem.unchanged_on (loc_out_of_bounds m1) m1 n1)
   (ACCMF: Mem.unchanged_on (fun b ofs => loc_out_of_bounds m1 b ofs /\
                                         ~ locsp se (rho_footprint rho) b ofs) m2 n2)
   (RETINJ: Val.inject inject_id r1 r2)
   (ABS: rho_ext rho se (n1, u) n2):
  rho_rc_reply rho se m1 m2 (r1, (n1, u)) (r2, n2).

Inductive rho_rc {U} (rho: rho_rel U): rc_rel (c_esig # (mem * U)) (c_esig # mem) :=
| rho_rc_intro vf1 vf2 sg vargs1 vargs2 se u m1 m2:
  rho_ext rho se (m1, u) m2 ->
  vf1 <> Vundef ->
  Val.inject inject_id vf1 vf2 ->
  Val.inject_list inject_id vargs1 vargs2 ->
  rho_rc rho _ (c_event vf1 sg vargs1 se # (m1, u)) _ (c_event vf2 sg vargs2 se # m2)
         (rho_rc_reply rho se m1 m2).

Program Definition rho_abrel {S1 S2 U} (R: S2 -> U * S1 -> Prop) (rho: rho_rel U) : abrel S2 S1 :=
  {|
    abrel_pred se := fun s2 '(m, s1) => exists u, R s2 (u, s1) /\ rho se u m;
    abrel_footprint := rho_footprint rho;
  |}.
Next Obligation.
  eexists; split; eauto.
  eapply rho_invar; eauto.
Qed.
Next Obligation.
  eapply rho_valid; eauto.
Qed.
Next Obligation.
  eapply rho_perm; eauto.
Qed.

Inductive li_state_rc {li: language_interface} {S: Type}: rc_rel (li # S) (li @ S)%li :=
| li_state_rc_intro (q: query li) s se:
  li_state_rc _ (eli_intro q se # s) _ (eli_intro (li:=li@S) (q, s) se) eq.

Definition c_mem_state_rc {S: Type}: rc_rel (c_esig # (mem * S)) (li_c @ S)%li :=
  rc_compose sig_assoc (rc_compose  (c_rc * rc_id) li_state_rc).

Close Scope Z_scope.

Record esig_rc (E: esig) :=
  {
    esig_refconv :> refconv E (c_esig # mem);
    (*
    esig_rc_clo :
      forall ar e R vf1 sg vargs1 m vf2 vargs2 se,
        esig_refconv ar e _ (c_event vf1 sg vargs1 se # m) R ->
        Val.inject inject_id vf1 vf2 -> Val.inject_list inject_id vargs1 vargs2 ->
        esig_refconv ar e _ (c_event vf2 sg vargs2 se # m) R;
     *)
  }.


Section REL_REF.

  Context {S1 S2 U} (R: S2 -> U * S1 -> Prop) (rho: rho_rel U).
  Context {E2} (r2: esig_rc E2).

  Definition lhs: (li_c @ S1)%li ~> (li_c @ S2)%li :=
    left_arrow c_mem_state_rc
    @@ slift (left_arrow r2)
    @ right_arrow (rc_id * rel_rc R)
    @ slift (right_arrow r2)
    @ h @ h @ h
    @ slift (right_arrow (rho_rc rho))
    @@ right_arrow c_mem_state_rc.

  Definition rhs: (li_c @ S1)%li ~> (li_c @ S2)%li := right_arrow (rho_abrel R rho).

  Lemma rel_ref: lhs [= rhs.
  Proof.
    unfold lhs, rhs. cbn. intros ? [ [ q s2 ] ].
    cbn. unfold rc_adj_right at 8.
    apply inf_iff. intros ?. apply inf_iff. intros qs1.
    apply inf_iff. intros (Rx & HR). cbn.
    destruct HR as (Rx' & Hrel & Hsub).
    inversion Hrel. cbn in *. depsubst. clear Hrel H4 H1.
    rename H7 into Hq. destruct q2 as [ q1 s1 ].
    inv Hq. inv H5. inv ABS. rename x into u. destruct H as [ HR Hrho ].
    rename se2 into se.

    match goal with
    | |- context [ _ @ ?f ] => set (f1 := f)
    end.
    unfold compose. unfold rc_adj_left.
    sup_intro ?. sup_intro m. sup_intro (Ra & HRa).
    rc_elim (inv) HRa. depsubst.
    rc_elim (inv) H4. depsubst. clear_hyp.
    rc_elim (inv) H5. depsubst.
    rc_elim (inv) H5. cbn in *. depsubst. clear_hyp.
    rc_elim (inv) H4. depsubst. clear_hyp.
    rc_elim (inv) H2. depsubst. clear_hyp. inv H4.
    (* rc_id is tricky *)
    rc_inversion H13. simple inversion Hrel. depsubst. clear_hyp. inv H7.
    clear Hrel. intm. unfold f1 at 2.

    match goal with
    | |- context [ _ @ ?f' ] => set (f2 := f')
    end.
    unfold compose. unfold rc_adj_right.
    inf_mor. eapply inf_at.
    inf_mor. eapply (inf_at (c_event vfs sg vargss se # s0 # s2)).
    inf_mor. eapply finf_at. rc_econstructor.
    intm. unfold f2 at 2.

    match goal with
    | |- context [ _ @ ?f' ] => set (f3 := f')
    end.
    unfold compose. cbn. unfold rc_adj_left.
    sup_intro ?. sup_intro e2. sup_intro [Rr2 Hr2].
    intm. unfold f3 at 2.

    match goal with
    | |- context [ _ @ ?f' ] => set (f4 := f')
    end.
    unfold compose. unfold rc_adj_right.
    inf_mor. eapply inf_at.
    inf_mor. eapply (inf_at (e2 # (u, s1))).
    inf_mor. eapply finf_at.
    { rc_econstructor; rc_econstructor. easy. }
    intm. unfold f4 at 2.

    match goal with
    | |- context [ _ @ ?f' ] => set (f5 := f')
    end.
    unfold compose. cbn. unfold rc_adj_right.
    inf_mor. eapply inf_at.
    inf_mor. eapply (inf_at (c_event vfs sg vargss se # s0)).
    inf_mor. eapply finf_at. instantiate (1 := Rr2).
    exact Hr2. intm. unfold f5 at 2.

    match goal with
    | |- context [ _ @ ?f' ] => set (f6 := f')
    end.
    unfold compose. unfold rc_adj_left.
    sup_intro ?. sup_intro m. sup_intro [ Rb Hrb ].
    destruct m. destruct e. destruct p. destruct p.
    rc_elim (inv) Hrb. depsubst. clear_hyp.
    intm. unfold f6 at 2.

    match goal with
    | |- context [ _ @ ?f' ] => set (f7 := f')
    end.
    unfold compose. unfold rc_adj_right.
    inf_mor. eapply inf_at.
    inf_mor. eapply (inf_at (c_event vfs sg vargss se # (s0, u, s1))).
    inf_mor. eapply finf_at.
    { rc_econstructor; rc_econstructor. constructor. }
    intm. unfold f7 at 2.

    match goal with
    | |- context [ _ @ ?f' ] => set (f8 := f')
    end.
    unfold compose. unfold rc_adj_right.
    inf_mor. eapply inf_at.
    inf_mor. eapply (inf_at (c_event vfs sg vargss se # (s0, u) # s1)).
    inf_mor. eapply finf_at. rc_econstructor.
    intm. unfold f8 at 2.

    match goal with
    | |- context [ _ @ ?f' ] => set (f9 := f')
    end.
    unfold compose. cbn. unfold rc_adj_right.
    inf_mor. eapply inf_at.
    inf_mor. eapply (inf_at (c_event vff sg vargsf se # mf)).
    inf_mor. eapply finf_at.
    { rc_econstructor. 2-4: eauto.
      constructor. auto. split; auto. }
    intm. unfold f9 at 2.

    unfold compose. unfold rc_adj_left.
    sup_intro ?. sup_intro m. sup_intro [ Rc Hrc ].
    destruct m. destruct e. destruct p.
    rc_elim (inv) Hrc. depsubst. clear_hyp. intm.

    unfold rc_adj_right at 2.
    inf_mor. eapply inf_at.
    inf_mor. eapply (inf_at ((eli_intro (li:=li_c@S1)(cq vff sg vargsf mf ,s1) se))).
    inf_mor. eapply finf_at.
    { repeat rc_econstructor; reflexivity. }
    intm.

    apply int_ref. intros [cr s1'].
    sup_intro (x & Hx).
    destruct cr as [ r m' ]. destruct x. destruct p.
    inv Hx. destruct H. inv H. inv H0. destruct H.
    subst x. destruct H. cbn in *. inv H.
    fcd_simpl.
    inf_mor. apply (finf_at (v, m, s1')).
    apply Hsub8. constructor.
    fcd_simpl. sup_intro (x & Hx).
    (* rho_with_se *)
    destruct x. destruct p. inv Hx.
    fcd_simpl. sup_intro (x & Hx).
    (* assoc *)
    destruct x. destruct p. destruct p. inv Hx.
    fcd_simpl. sup_intro (x & Hx).
    (* eq * assoc *)
    destruct x. destruct p. destruct p. destruct Hx. cbn in *. inv H0.
    fcd_simpl.
    inf_mor. apply (finf_at (v0, m0, (u0, s1'))).
    apply Hsub7. constructor.
    fcd_simpl. sup_intro (n2 & Hr2').
    fcd_simpl. sup_intro (x & Hx). destruct x. destruct Hx. cbn in *. subst.
    fcd_simpl. inf_mor. apply (finf_at (v0, m0)). apply Hr2'.
    fcd_simpl. sup_intro (x & Hx). destruct x. destruct p. inv Hx.
    fcd_simpl. inf_mor. apply (finf_at (cr v0 m0, s)).
    apply Hsub0. eexists; split.
    apply Hsub1. constructor.
    apply Hsub2. eexists; split.
    apply Hsub4. instantiate (1 := (_, _)). split.
    apply Hsub5. subst R5. cbn. reflexivity.
    apply Hsub6. cbn. reflexivity.
    apply Hsub3. reflexivity.
    fcd_simpl. clear f1 f2 f3 f4 f5 f6 f7 f8 f9.
    apply (fsup_at (cr v0 m0, s)).
    apply Hsub.
    exists (mk_aw se m0 m). split.
    - constructor; eauto.
    - constructor; eauto.
      all: try apply ABS.
      exists u0. split; eauto. apply ABS.
    - fcd_simpl. reflexivity.
  Qed.

End REL_REF.

Section STRATEGY_REF.

  Record strategy_clight {E1 E2 U} (Sigma: E1 ~> E2 # U) :=
    {
      rho : rho_rel U;
      r1 : esig_rc E1;
      r2 : esig_rc E2;
      M: cmodule;

      strategy_clight_ref:
        left_arrow c_rc
        @ left_arrow (rho_rc rho)
        @@ slift (left_arrow r2)
        @ Sigma
        @ right_arrow r1
        @ right_arrow c_rc
        [= ang_lts_spec (semantics M)
    }.

End STRATEGY_REF.

Lemma lift_lts_ref {liA liB} (L: Smallstep.semantics liA liB) (K: Type):
  left_arrow li_state_rc @ slift (ang_lts_spec L) @ right_arrow li_state_rc [=
    ang_lts_spec (L@K)%lts.
Proof.
  cbn. intros ? [[qb k] se].
  unfold rc_adj_left, rc_adj_right, compose. cbn.
  sup_intro ?. sup_intro [? ? [qb' se'] [k']].
  sup_intro [Rx HRx]. rc_elim (inv) HRx. depsubst. intm.
  apply assume_r. intros Hse.
  unfold assume. inf_mor. apply (inf_at Hse). fcd_simpl.
  rewrite sup_fsup. sup_intro [si Hsi].
  rewrite sup_fsup. eapply (fsup_at (si, k)).
  { constructor; eauto. }
  sup_intro steps. apply (sup_at steps).
  clear Hsi. revert si k. induction steps.
  - intros si k. cbn. repeat sup_mor. reflexivity.
  - intros si k. Opaque lifted_semantics.
    cbn. sup_mor. repeat apply join_lub.
    + apply join_l. apply join_l.
      sup_intro (st & Hst).
      eapply (fsup_at (st, k)).
      { now apply lifting_step_star. }
      apply IHsteps.
    + apply join_l. apply join_r.
      sup_intro (qa & Hq). eapply (fsup_at (qa, k)).
      { constructor; eauto. }
      unfold query_int. intm.
      inf_mor. eapply inf_at.
      inf_mor. eapply (inf_at (eli_intro (li:=(liA@K)) (qa, k) se)).
      inf_mor. eapply finf_at.
      { rc_econstructor. }
      intm. unfold int at 3 4.
      sup_intro [[ra k']|].
      * fcd_simpl. apply join_lub.
        -- apply (sup_at None). fcd_simpl. reflexivity.
        -- apply (sup_at (Some (ra, k'))). fcd_simpl.
           apply join_r. rstep.
           sup_intro ((ra', k'') & Hr). inv Hr.
           intm. sup_intro (s' & Hs').
           eapply (fsup_at (s', k')).
           { constructor; eauto. }
           apply IHsteps.
      * apply (sup_at None). fcd_simpl. reflexivity.
    + apply join_r. sup_intro (r & Hr).
      apply (fsup_at (r, k)).
      { constructor; eauto. }
      fcd_simpl.
      inf_mor. eapply (finf_at (_, _)). apply Hsub. reflexivity.
      fcd_simpl. reflexivity.
Qed.

Lemma lift_rc_r {E F S} (r: E <=> F):
  right_arrow (r * rc_id) = slift (S:=S) (right_arrow r).
Proof.
  apply antisymmetry; intros ? [? ? m [s]]; cbn; unfold rc_adj_right.
  - inf_intro ?. inf_intro ?.
    inf_intro (R & HR).
    eapply inf_at. eapply inf_at.
    eapply finf_at.
    { rc_econstructor; [ eauto | rc_econstructor ]. }
    intm. unfold int.
    sup_intro [[n t]|].
    + fcd_simpl. apply join_lub.
      * apply (sup_at None). now fcd_simpl.
      * apply (sup_at (Some (n, t))).
        fcd_simpl. apply join_r. rstep.
        sup_intro ((x, t') & Hr). inv Hr.
        cbn in *. subst.
        eapply (fsup_at x). eauto. now fcd_simpl.
    + apply (sup_at None). fcd_simpl. reflexivity.
  - inf_intro ?. inf_intro ?. inf_intro (R & HR).
    rc_elim (inv) HR. depsubst. clear_hyp.
    destruct m2'. destruct H11 as (Rx & (Hx & Hy)).
    simple inversion Hx. clear Hx. depsubst. clear_hyp. inv H2.
    eapply inf_at. eapply inf_at.
    (* fixme *)
    eapply (inf_at (exist _ _ H6)).
    intm. unfold int.
    sup_intro [[n t]|].
    + fcd_simpl. apply join_lub.
      * apply (sup_at None). fcd_simpl. reflexivity.
      * apply (sup_at (Some (n, t))).
        fcd_simpl. apply join_r. rstep.
        sup_intro (x & Hr).
        eapply (fsup_at (x, t)). apply Hsub.
        split; eauto. now fcd_simpl.
    + apply (sup_at None). fcd_simpl. reflexivity.
Qed.

Lemma lift_rc_l S:
  left_arrow (c_rc * rc_id) = slift (S:=S) (left_arrow c_rc).
Admitted.

Section COMPILE_LAYER.

  Context {E1 E2 S1 S2 U} (L1: 0 ~> E1 # S1) (L2: 0 ~> E2 # S2)
          (st_layer: strategy_layer U L1 L2).
  Context (st_clight: strategy_clight (strategy_impl st_layer)).

  Definition Lc1: 0 ~> (li_c @ S1)%li :=
    left_arrow c_mem_state_rc @@ slift (left_arrow (r1 _ st_clight)) @ L1.

  Definition Lc2: 0 ~> (li_c @ S2)%li :=
    left_arrow c_mem_state_rc @@ slift (left_arrow (r2 _ st_clight)) @ L2.

  Local Obligation Tactic := idtac.
  Local Opaque semantics.

  Program Definition c_layer: clight_layer Lc1 Lc2 :=
    {|
      clight_impl := M _ st_clight;
      clight_rel := (rho_abrel (strategy_rel st_layer) (rho _ st_clight));
    |}.
  Next Obligation.
    unfold Lc1, Lc2.
    destruct st_clight as [ rho r1 r2 M strategy_clight_ref ].
    destruct st_layer as [ Sigma R strategy_layer_ref ].
    Local Opaque LatticeProduct.poset_prod.
    Local Opaque left_arrow right_arrow.
    cbn in *.
    pose proof (rel_ref R rho r2) as H. unfold lhs, rhs in H. cbn in *.
    rewrite <- H. clear H.
    rewrite <- lift_lts_ref.
    rewrite strategy_layer_ref. clear strategy_layer_ref.
    rewrite <- strategy_clight_ref. clear strategy_clight_ref.
    (* fixme *)
    unfold h, sig_assoc_left, sig_assoc_right, st_assoc_right.
    (* unfold state_sig. *)

    rewrite !slift_compose.
    rewrite <- !compose_assoc. apply compose_proper_ref. 2: reflexivity.
    rewrite !compose_assoc.
    apply compose_proper_ref. reflexivity.
    apply compose_proper_ref. reflexivity.
    apply compose_proper_ref. reflexivity.
    apply compose_proper_ref. reflexivity.
    do 11 rewrite <- compose_assoc.
    apply compose_proper_ref.
    {
      rewrite !compose_assoc.
      unfold c_mem_state_rc.
      rewrite <- !right_arrow_compose.
      rewrite !compose_assoc.

      rewrite <- (compose_assoc _ (right_arrow sig_assoc) (left_arrow sig_assoc)).
      rewrite assoc_inverse. rewrite compose_unit_l.
      setoid_rewrite <- (compose_assoc _ (left_arrow li_state_rc) (right_arrow li_state_rc)).
      rewrite <- eta. rewrite compose_unit_l.
      setoid_rewrite lift_rc_r.
      setoid_rewrite <- (compose_assoc _ (slift (left_arrow c_rc)) (slift (right_arrow c_rc))).
      rewrite <- (slift_compose (right_arrow c_rc)).
      rewrite <- eta. rewrite slift_identity. rewrite compose_unit_l.
      rewrite <- (compose_assoc _ (slift (left_arrow _)) (slift (right_arrow _))).
      rewrite <- (slift_compose (right_arrow _) (left_arrow _)).
      rewrite <- eta. rewrite slift_identity. rewrite compose_unit_l.
      rewrite <- (compose_assoc _ _ (right_arrow sig_assoc)).
      rewrite <- (compose_assoc _ (_ @ _)).
      rewrite <- (compose_assoc _ (_ @ _)).
      etransitivity.
      instantiate (1 := slift (right_arrow r2) @
                              right_arrow sig_assoc @ slift (slift (left_arrow r2))).
      2: {
        apply compose_proper_ref. reflexivity.
        apply compose_proper_ref. 2: reflexivity.
        apply assoc_property.
      }
      rewrite <- assoc_lift.
      rewrite <- (compose_unit_l (right_arrow _)) at 1.
      rewrite <- compose_assoc. apply compose_proper_ref. 2: reflexivity.
      rewrite <- slift_compose. rewrite <- eta.
      rewrite slift_identity. reflexivity.
    }
    rewrite <- (compose_unit_r (slift Sigma)) at 1.
    apply compose_proper_ref. reflexivity.
    unfold c_mem_state_rc. rewrite <- !left_arrow_compose.
    rewrite !compose_assoc. cbn.
    rewrite <- (compose_assoc _ ((left_arrow _)) ((right_arrow _))).
    rewrite <- eta. rewrite compose_unit_l.
    rewrite <- (compose_assoc _ ((right_arrow _)) ((left_arrow _))).
    rewrite assoc_inverse. rewrite compose_unit_l.
    setoid_rewrite lift_rc_l.
    rewrite <- (compose_assoc _ (_ (left_arrow _)) (_ (right_arrow _))).
    rewrite <- slift_compose. rewrite <- eta.
    rewrite slift_identity. rewrite compose_unit_l.
    rewrite <- slift_compose. rewrite <- eta.
    rewrite slift_identity. reflexivity.
  Qed.

End COMPILE_LAYER.


(** Obsolete stuff *)
(*
Local Opaque normalize_rc.
Close Scope Z_scope.

Lemma foo {E: esig} {S1 S2 S3 U: Type} (R: S1 -> S2 * S3 -> Prop):
  right_arrow sig_comm @ slift (right_arrow (rc_id * rel_rc R)) [=
    right_arrow (rc_id(E:=E#U) * rel_rc R) @ right_arrow sig_comm.
Proof.
  intros ? [ ? ? [ ? ? m [ u ] ] [ s1 ] ]. cbn.
  unfold compose, rc_adj_right.
  inf_intro ?. inf_intro m'. inf_intro [ Rx HRx ].
  rc_destruct HRx. rc_destruct H. rc_destruct H0.
  destruct m0 as [ ? ? e [ s ]].
  eapply inf_at. inf_mor. eapply inf_at. inf_mor. eapply finf_at.
  { rc_econstructor. }
  intm.
  inf_intro ?. inf_intro m'. inf_intro [ Ry HRy ].
  rc_inversion HRy. depsubst. clear_hyp. clear Hrel.
  eapply inf_at. inf_mor. eapply inf_at. inf_mor. eapply finf_at.
  { rc_econstructor; rc_econstructor; eauto. }
  intm. apply bind_proper_ref. 2: reflexivity.
  intros [ ? ? ].
  sup_intro [ n Hn ]. inv Hn. destruct n. destruct p.
  cbn [fst snd] in *. subst. eapply fsup_at.
  { apply Hsub2. constructor. }
  fcd_simpl.
  sup_intro [ n Hn ]. inv Hn.
  eapply fsup_at.
  { apply Hsub. instantiate (1 := (_, _)). split; eauto.
    apply Hsub0. reflexivity. }
  fcd_simpl. reflexivity.
Qed.

Lemma baz {E F: esig} {S1 S2} (f: E ~> F):
  slift(S:=S1) (slift(S:=S2) f) [= right_arrow sig_comm @ slift(S:=S2) (slift(S:=S1) f) @ right_arrow sig_comm.
Proof.
Abort.

Lemma xxx {E F: esig} {S1 S2} (f: E ~> F):
  slift(S:=S1) (slift(S:=S2) f) [=
    left_arrow sig_comm @ left_arrow sig_assoc @ (slift f) @ right_arrow sig_assoc @ right_arrow sig_comm.
Proof.
Abort.
*)
