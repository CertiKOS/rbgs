From Coq Require Import
     List Lia.
From models Require Import
     IntSpec.
From examples Require Import
     CAL CompCertIntSpec RefConv
     BoundedQueueCode.
From lattices Require Import
     Upset Downset FCD.
From structures Require Import
     Effects Lattice.
From compcert Require Import
     AST Values Memory
     Globalenvs
     LanguageInterface
     Smallstep.
From compcertox Require Import
     Lifting CModule AbstractStateRel.
Import ListNotations ISpec.

Unset Asymmetric Patterns.

(** ** Preliminaries *)

Ltac clear_hyp :=
  repeat match goal with
         | [ H : (?t = ?t)%type |- _ ] => clear H
         end.

(** The language interface "C simple" which does not include the memory *)
Inductive c_esig : esig :=
| c_event : val -> signature -> list val -> Genv.symtbl -> c_esig val.

Inductive c_rc: rc_rel (c_esig # mem) li_c :=
| c_rc_intro vf sg args e_c e_s m se:
  let R := (fun '(r, m) c_r => c_r = cr r m) in
  e_c = c_event vf sg args se -> e_s = state_event m ->
  c_rc _ (esig_tens_intro e_c e_s) _ (li_sig (cq vf sg args m) se) R.

(** Some auxiliary definitions *)
Inductive assoc {A B C: Type}: A * (B * C) -> A * B * C -> Prop :=
| assoc_intro a b c: assoc (a, (b, c)) ((a, b), c).
Inductive sig_assoc {E: esig} {S1 S2: Type}: rc_rel (E#(S1*S2)) (E#S1#S2) :=
| sig_assoc_intro ar (m: E ar) s1 s2 :
  sig_assoc _ (m # (s1, s2)) _ ((m # s1) # s2) assoc.
Inductive eq_comm {A B C: Type}: A * B * C -> A * C * B -> Prop :=
| eq_comm_intro a b c: eq_comm ((a, b), c) ((a, c), b).
Inductive sig_comm {E: esig} {S1 S2: Type}: rc_rel (E#S1#S2) (E#S2#S1) :=
| sig_comm_intro ar (m: E ar) s1 s2:
  sig_comm _ (m # s1 # s2) _ (m # s2 # s1) eq_comm.

Inductive comm {A B: Type}: A * B -> B * A -> Prop :=
| comm_intro a b: comm (a, b) (b, a).
Definition st_comm {E: esig} {S1 S2: Type}: rc_rel (E#(S1*S2)) (E#(S2*S1)) :=
  (rc_id * rel_rc comm)%rc.
Definition st_assoc {E: esig} {S1 S2 S3: Type}: rc_rel (E#(S1*(S2*S3))) (E#(S1*S2*S3)) :=
  (rc_id * rel_rc assoc)%rc.

(** Using type inference to make twisting on types more ergonomic *)
Class StrategyHelper E F := h: E ~> F.

Global Instance sig_assoc_right {E} {S1 S2} :
  StrategyHelper (E#S1#S2) (E#(S1*S2)) := right_arrow sig_assoc.

Notation "f @@ g" := (f @ h @ g).

Open Scope rc_scope.

(** ** CAL in the Strategy World *)

Record strategy_layer {E1 E2} {S1 S2} (U: Type) (L1: 0 ~> E1 # S1) (L2: 0 ~> E2 # S2) :=
  {
    strategy_impl: E1 ~> E2 # U;
    strategy_rel: S2 -> U * S1 -> Prop;

    (* L₂ ⊑ (E₂@R)_ ∘ (Σ@S₁) ∘ L₁ *)
    strategy_layer_ref:
      L2 [= right_arrow (rc_id * rel_rc strategy_rel) @@ slift strategy_impl @ L1;
  }.
Arguments strategy_impl {_ _ _ _ _ _ _}.
Arguments strategy_rel {_ _ _ _ _ _ _}.
Arguments strategy_layer_ref {_ _ _ _ _ _ _}.

(** *** Composition *)

(** Stateful sequential composition of strategies *)
Definition st_compose {E F G} {U1 U2} (f: F ~> G#U1) (g: E ~> F#U2) : E ~> G#(U1*U2) :=
  h @ slift f @ g.

Section COMP.

  Context {E1 E2 E3} {S1 S2 S3 U1 U2}
          (L1: 0 ~> E1 # S1) (L2: 0 ~> E2 # S2) (L3: 0 ~> E3 # S3)
          (C1: strategy_layer U1 L1 L2)
          (C2: strategy_layer U2 L2 L3).

  Local Obligation Tactic := idtac.

  Program Definition strategy_layer_compose: strategy_layer (U2*U1) L1 L3 :=
    {|
      strategy_impl := st_compose (strategy_impl C2) (strategy_impl C1);
      strategy_rel := rel_compose (strategy_rel C2) (rel_compose (eq * strategy_rel C1) assoc);
    |}.
  Next Obligation.
  Admitted.

End COMP.

(** ** CAL in the CompCert World *)

Require Import compcertox.KRel.

Record clight_layer {S1 S2} (L1: 0 ~> (li_c @ S1)%li) (L2: 0 ~> (li_c @ S2)%li) :=
  {
    clight_impl: cmodule;
    clight_sk: AST.program unit unit;
    clight_rel: krel S1 S2;

    clight_sk_order: skel_module_compatible clight_impl clight_sk;
    clight_layer_ref:
      let MS := ang_lts_spec (((semantics clight_impl clight_sk) @ S1)%lts)
      in L2 [= right_arrow (cc_rc clight_rel) @ MS @ L1;
  }.
Arguments clight_impl {_ _ _ _}.
Arguments clight_sk {_ _ _ _}.
Arguments clight_rel {_ _ _ _}.
Arguments clight_sk_order {_ _ _ _}.
Arguments clight_layer_ref {_ _ _ _}.

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

Lemma cmodule_rel {S1 S2} M sk (R: krel _ _):
  skel_module_compatible M sk ->
  ang_lts_spec (semantics M sk @ S2) @ rc_adj_right (cc_rc R) [=
    rc_adj_right (cc_rc R) @ ang_lts_spec (semantics M sk @ S1).
Proof.
  intros H. eapply (cmodule_krel R) in H.
  eapply ang_fsim_embed in H. rewrite H.
  cbn -[LatticeProduct.poset_prod].
  rewrite !compose_assoc.
  rewrite @rc_adj_epsilon. rewrite compose_unit_r. reflexivity.
Qed.

(** *** Composition *)
Section COMP.

  Context {S1 S2 S3}
          (L1: 0 ~> (li_c @ S1)%li)
          (L2: 0 ~> (li_c @ S2)%li)
          (L3: 0 ~> (li_c @ S3)%li)
          (C1: clight_layer L1 L2) (C2: clight_layer L2 L3).
  Context (sk: AST.program unit unit)
          (Hsk: Linking.link (clight_sk C2) (clight_sk C1) = Some sk).
  Context (Hcomp: CategoricalComp.CategoricalLinkable
                    (semantics (clight_impl C2) (clight_sk C2))
                    (semantics (clight_impl C1) (clight_sk C1))).

  Local Obligation Tactic := idtac.

  (* Embedded version of layer_vcomp] from Compsition.v *)
  Program Definition clight_layer_compose: clight_layer L1 L3 :=
    {|
      clight_impl := clight_impl C2 ++ clight_impl C1;
      clight_sk := sk;
      clight_rel := krel_compose (clight_rel C1) (clight_rel C2);
    |}.
  Next Obligation.
    destruct C1 as [M1 sk1 R1 Hsk1 Hsim1].
    destruct C2 as [M2 sk2 R2 Hsk2 Hsim2].
    unfold skel_module_compatible in *. cbn in *.
    clear - Hsk Hsk1 Hsk2.
    apply Linking.link_linkorder in Hsk as [Hk1 Hk2].
    rewrite Forall_forall in *.
    setoid_rewrite in_app_iff.
    intros p [Hp|Hp]; eapply Linking.linkorder_trans; eauto.
  Qed.
  Next Obligation.
    destruct C1 as [M1 sk1 R1 Hsk1 Hsim1].
    destruct C2 as [M2 sk2 R2 Hsk2 Hsim2].
    Local Opaque LatticeProduct.poset_prod.
    cbn -[semantics] in *. etransitivity.
    apply Hsim2. clear Hsim2.
    rewrite Hsim1. clear Hsim1.
    rewrite <- (compose_assoc _ (rc_adj_right (cc_rc R1)) _).
    rewrite cmodule_rel; eauto. rewrite compose_assoc.
    rewrite <- (compose_assoc _ (rc_adj_right R1) _).
    apply compose_proper_ref.
    {
      rewrite rc_adj_right_compose.
      unfold cc_refconv. rewrite cc_rc_compose. reflexivity.
    }
    rewrite <- compose_assoc.
    apply compose_proper_ref. 2: reflexivity.
    erewrite (comp_embed (semantics M2 sk2 @ S1)%lts (semantics M1 sk1 @ S1)%lts).
    2: { unfold CategoricalComp.comp_semantics. cbn. rewrite Hsk. reflexivity. }
    apply ang_fsim_embed_cc_id.
    apply cmodule_categorical_comp_simulation_lifted.
  Qed.

End COMP.

(** ** Connection between the Strategy World and the CompCert World *)

(* Should be define as [massert] *)
Record rho_rel (U: Type) :=
  {
    rho_pred (se: Genv.symtbl) :> U -> mem -> Prop;
    rho_footprint : ident -> Prop;

    rho_ext (se: Genv.symtbl) : mem * U -> mem -> Prop :=
      fun '(m1, u) m2 =>
        Mem.extends m1 m2 /\ rho_pred se u m2 /\
          no_perm_on m1 (blocks se rho_footprint);
  }.

(* used to be [id (E:=C) * rho ] *)
Inductive rho_with_se {U} (rho: rho_rel U): rc_rel (c_esig # (mem * U)) (c_esig # mem) :=
| rho_with_se_intro vf sg vargs se u m1 m2:
  let R := fun '(r1, (m1, u)) '(r2, m2) => r1 = r2 /\ rho_ext _ rho se (m1, u) m2 in
  rho_ext _ rho se (m1, u) m2 ->
  rho_with_se rho _ (c_event vf sg vargs se # (m1, u)) _ (c_event vf sg vargs se # m2) R.

Program Definition rho_krel {S1 S2 U} (R: S2 -> U * S1 -> Prop) (rho: rho_rel U) : krel' S1 S2 :=
  {|
    krel_pred se := fun s2 '(m, s1) => exists u, R s2 (u, s1) /\ rho se u m;
    krel_footprint := rho_footprint _ rho;
  |}.
Next Obligation.
Admitted.
Next Obligation.
Admitted.

Global Instance sig_assoc_left {E} {S1 S2} :
  StrategyHelper (E#(S1*S2)) (E#S1#S2) := left_arrow sig_assoc.

Global Instance st_assoc_right {E} {S1 S2 S3} :
  StrategyHelper (E#(S1*S2*S3)) (E#(S1*(S2*S3))) := right_arrow st_assoc.

Inductive li_state_rc {li: language_interface} {S: Type}: rc_rel (li # S) (li @ S)%li :=
| li_state_rc_intro (q: query li) s se:
  li_state_rc _ (li_sig q se # s) _ (li_sig (li:=li@S) (q, s) se) eq.

Definition c_mem_state_rc {S: Type}: rc_rel (c_esig # (mem * S)) (li_c @ S)%li :=
  rc_compose sig_assoc (rc_compose  (c_rc * rc_id) li_state_rc).

Require Import Coqlib.
Close Scope Z_scope.

Instance apply_mor {E S A} (s: S) :
  CDL.Morphism (@srun E S A s).
Proof.
  unfold srun. split.
  - intros x y. rewrite Sup.mor. reflexivity.
  - intros x y. rewrite Inf.mor. reflexivity.
Qed.

Record esig_rc (E: esig) :=
  {
    esig_refconv :> refconv E (c_esig # mem);
    esig_rc_clo :
      forall ar e R vf1 sg vargs1 m vf2 vargs2 se,
        esig_refconv ar e _ (c_event vf1 sg vargs1 se # m) R ->
        Val.inject inject_id vf1 vf2 -> Val.inject_list inject_id vargs1 vargs2 ->
        esig_refconv ar e _ (c_event vf2 sg vargs2 se # m) R;
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
    @ slift (right_arrow (rho_with_se rho))
    @@ right_arrow c_mem_state_rc.

  Definition rhs: (li_c @ S1)%li ~> (li_c @ S2)%li := right_arrow (krel_singleton (rho_krel R rho)).

  Local Opaque normalize_rc.

  Lemma rel_ref: lhs [= rhs.
  Proof.
    unfold lhs, rhs. cbn. intros ? [ [ q s2 ] ].
    cbn. unfold rc_adj_right at 8.
    apply inf_iff. intros ?. apply inf_iff. intros qs1.
    apply inf_iff. intros (Rx & HR). cbn.
    destruct HR as (Rx' & Hrel & Hsub).
    inversion Hrel. cbn in *. depsubst. clear Hrel H4 H1.
    rename H7 into Hq. destruct q2 as [ q1 s1 ].
    inv Hq. inv H5. inv H9. rename x into u. destruct H as [ HR Hrho ].
    rename se2 into se.
    rename H3 into Hvf. rename H4 into Hargs. rename H6 into Hm.
    rename H7 into Hvf1. rename H8 into Hperm.

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
    inf_mor. eapply (inf_at (c_event vf1 sg vargs1 se # s0 # s2)).
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
    inf_mor. eapply (inf_at (c_event vf2 sg vargs2 se # s0)).
    inf_mor. eapply finf_at. instantiate (1 := Rr2).
    eapply (esig_rc_clo _ r2); eauto.
    intm. unfold f5 at 2.

    match goal with
    | |- context [ _ @ ?f' ] => set (f6 := f')
    end.
    unfold compose. unfold rc_adj_left.
    sup_intro ?. sup_intro m. sup_intro [ Rb Hrb ].
    destruct m. destruct s. destruct p. destruct p.
    rc_elim (inv) Hrb. depsubst. clear_hyp.
    intm. unfold f6 at 2.

    match goal with
    | |- context [ _ @ ?f' ] => set (f7 := f')
    end.
    unfold compose. unfold rc_adj_right.
    inf_mor. eapply inf_at.
    inf_mor. eapply (inf_at (c_event vf2 sg vargs2 se # (s0, u, s1))).
    inf_mor. eapply finf_at.
    { rc_econstructor; rc_econstructor. constructor. }
    intm. unfold f7 at 2.

    match goal with
    | |- context [ _ @ ?f' ] => set (f8 := f')
    end.
    unfold compose. unfold rc_adj_right.
    inf_mor. eapply inf_at.
    inf_mor. eapply (inf_at (c_event vf2 sg vargs2 se # (s0, u) # s1)).
    inf_mor. eapply finf_at. rc_econstructor.
    intm. unfold f8 at 2.

    match goal with
    | |- context [ _ @ ?f' ] => set (f9 := f')
    end.
    unfold compose. cbn. unfold rc_adj_right.
    inf_mor. eapply inf_at.
    inf_mor. eapply (inf_at (c_event vf2 sg vargs2 se # m2)).
    inf_mor. eapply finf_at.
    { rc_econstructor. constructor. auto. split; auto. }
    intm. unfold f9 at 2.

    unfold compose. unfold rc_adj_left.
    sup_intro ?. sup_intro m. sup_intro [ Rc Hrc ].
    destruct m. destruct s. destruct p.
    rc_elim (inv) Hrc. depsubst. clear_hyp. intm.

    unfold rc_adj_right at 2.
    inf_mor. eapply inf_at.
    inf_mor. eapply (inf_at ((li_sig (li:=li_c@S1)(cq vf2 sg vargs2 m2 ,s1) se))).
    inf_mor. eapply finf_at.
    { repeat rc_econstructor; reflexivity. }

    sup_mor. sup_mor. cbn. apply sup_iff. intros [ [ cr s1' ] | ].
    - fcd_simpl. sup_mor. sup_mor. apply join_lub.
      { apply (sup_at None). fcd_simpl. reflexivity. }
      sup_intro (x & Hx).
      destruct cr as [ r m' ]. destruct x. destruct p.
      inv Hx. destruct H. inv H. inv H0. destruct H.
      subst x. destruct H. cbn in *. inv H.
      fcd_simpl. apply join_lub.
      { apply (sup_at None). fcd_simpl. reflexivity. }
      inf_mor. apply (finf_at (v, m, s1')).
      apply Hsub8. constructor.
      fcd_simpl. sup_intro (x & Hx).
      (* rho_with_se *)
      destruct x. destruct p. destruct Hx as (-> & Hm'& Hrho'& Hperm').
      fcd_simpl. sup_intro (x & Hx).
      (* assoc *)
      destruct x. destruct p. destruct p. inv Hx.
      fcd_simpl. sup_intro (x & Hx).
      (* eq * assoc *)
      destruct x. destruct p. destruct p. destruct Hx. cbn in *. inv H0.
      fcd_simpl.
      inf_mor. apply (finf_at (v, m0, (u0, s1'))).
      apply Hsub7. constructor.
      fcd_simpl. sup_intro (n2 & Hr2').
      fcd_simpl. sup_intro (x & Hx). destruct x. destruct Hx. cbn in *. subst.
      fcd_simpl. inf_mor. apply (finf_at (v, m0)). apply Hr2'.
      fcd_simpl. sup_intro (x & Hx). destruct x. destruct p. inv Hx.
      fcd_simpl. inf_mor. apply (finf_at (cr v m0, s)).
      apply Hsub0. eexists; split.
      apply Hsub1. constructor.
      apply Hsub2. eexists; split.
      apply Hsub4. instantiate (1 := (_, _)). split.
      apply Hsub5. subst R5. cbn. reflexivity.
      apply Hsub6. cbn. reflexivity.
      apply Hsub3. reflexivity.
      fcd_simpl. clear f1 f2 f3 f4 f5 f6 f7 f8 f9.
      apply (sup_at (Some (cr v m, s1'))). fcd_simpl.
      apply join_r. sup_mor.
      apply (fsup_at (cr v m0, s)).
      apply Hsub. constructor; try easy.
      exists u0. split; easy. fcd_simpl. reflexivity.
    - apply (sup_at None). fcd_simpl. reflexivity.
  Qed.

End REL_REF.

Section STRATEGY_REF.

  Record strategy_clight {E1 E2 U} (Sigma: E1 ~> E2 # U) :=
    {
      rho : rho_rel U;
      r1 : esig_rc E1;
      r2 : esig_rc E2;
      M: cmodule;
      sk : AST.program unit unit;

      strategy_clight_ref:
        left_arrow c_rc
        @ left_arrow (rho_with_se rho)
        @@ slift (left_arrow r2)
        @ Sigma
        @ right_arrow r1
        @ right_arrow c_rc
        [= ang_lts_spec (semantics M sk)
    }.

End STRATEGY_REF.

Lemma lift_lts_ref {liA liB} (L: Smallstep.semantics liA liB) (K: Type):
  left_arrow li_state_rc @ slift (ang_lts_spec L) @ right_arrow li_state_rc [= ang_lts_spec (L@K)%lts.
Proof.
Admitted.

Lemma slift_compose {E F G S} (f: F ~> G) (g: E ~> F):
  slift (S:=S) (f @ g) = slift f @ slift g.
Proof.
  apply antisymmetry.
  - intros ? [ ? ? m [ s ] ]. cbn.
    unfold compose. cbn. rewrite srun_slift. reflexivity.
  - intros ? [ ? ? m [ s ] ]. cbn.
    unfold compose. cbn. rewrite srun_slift. reflexivity.
Qed.

Lemma assoc_inverse {E S1 S2}:
  rc_adj_left (@sig_assoc E S1 S2) @ rc_adj_right sig_assoc = identity.
Proof.
Admitted.

Lemma lift_rc_r S:
  rc_adj_right (c_rc * rc_id) = slift (S:=S) (rc_adj_right c_rc).
Admitted.

Lemma lift_rc_l S:
  rc_adj_left (c_rc * rc_id) = slift (S:=S) (rc_adj_left c_rc).
Admitted.

Lemma assoc_lift {E F S1 S2} (f: E ~> F):
  slift f @ rc_adj_right sig_assoc = rc_adj_right sig_assoc @ slift(S:=S2) (slift(S:=S1) f).
Proof.
Admitted.

Lemma assoc_property {E S1 S2 S3}:
  rc_adj_right sig_assoc [=
    rc_adj_left sig_assoc @ rc_adj_right (st_assoc (E:=E) (S1:=S1) (S2:=S2) (S3:=S3))
                @ rc_adj_right sig_assoc @ slift (rc_adj_right sig_assoc).
Proof.
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
      clight_sk := sk _ st_clight;
      clight_rel := krel_singleton (rho_krel (strategy_rel st_layer) (rho _ st_clight));
    |}.
  Next Obligation.
  Admitted.
  Next Obligation.
    unfold Lc1, Lc2.
    destruct st_clight as [ rho r1 r2 M sk strategy_clight_ref ].
    destruct st_layer as [ Sigma R strategy_layer_ref ].
    Local Opaque LatticeProduct.poset_prod.
    cbn in *.
    pose proof (rel_ref R rho r2) as H. unfold lhs, rhs in H. cbn in *.
    rewrite <- H. clear H.
    rewrite <- lift_lts_ref.
    rewrite strategy_layer_ref. clear strategy_layer_ref.
    rewrite <- strategy_clight_ref. clear strategy_clight_ref.
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
      rewrite <- !rc_adj_right_compose.
      rewrite !compose_assoc.
      setoid_rewrite <- (compose_assoc _ (rc_adj_right sig_assoc) (rc_adj_left sig_assoc)).
      rewrite assoc_inverse. rewrite compose_unit_l. cbn.
      setoid_rewrite <- (compose_assoc _ (rc_adj_left li_state_rc) (rc_adj_right li_state_rc)).
      rewrite <- rc_adj_eta. rewrite compose_unit_l.
      setoid_rewrite lift_rc_r.
      setoid_rewrite <- (compose_assoc _ (slift (rc_adj_left c_rc)) (slift (rc_adj_right c_rc))).
      setoid_rewrite <- (slift_compose (rc_adj_right c_rc)).
      rewrite <- rc_adj_eta. rewrite slift_identity. rewrite compose_unit_l.
      setoid_rewrite <- (compose_assoc _ (slift (rc_adj_left _)) (slift (rc_adj_right _))).
      setoid_rewrite <- (slift_compose (rc_adj_right _) (rc_adj_left _)).
      rewrite <- rc_adj_eta. rewrite slift_identity. rewrite compose_unit_l.
      setoid_rewrite <- (compose_assoc _ _ (rc_adj_right sig_assoc)).
      setoid_rewrite <- (compose_assoc _ (_ @ _)).
      setoid_rewrite <- (compose_assoc _ (_ @ _)).
      etransitivity.
      instantiate (1 := slift (rc_adj_right r2) @
                              rc_adj_right sig_assoc @ slift (slift (rc_adj_left r2))).
      2: {
        apply compose_proper_ref. reflexivity.
        apply compose_proper_ref. 2: reflexivity.
        apply assoc_property.
      }
      rewrite <- assoc_lift.
      rewrite <- (compose_unit_l (rc_adj_right _)) at 1.
      rewrite <- compose_assoc. apply compose_proper_ref. 2: reflexivity.
      rewrite <- slift_compose. rewrite <- rc_adj_eta.
      rewrite slift_identity. reflexivity.
    }
    rewrite <- (compose_unit_r (slift Sigma)) at 1.
    apply compose_proper_ref. reflexivity.
    unfold c_mem_state_rc. rewrite <- !rc_adj_left_compose.
    rewrite !compose_assoc. cbn.
    setoid_rewrite <- (compose_assoc _ ((rc_adj_left _)) ((rc_adj_right _))).
    rewrite <- rc_adj_eta. rewrite compose_unit_l.
    setoid_rewrite <- (compose_assoc _ ((rc_adj_right _)) ((rc_adj_left _))).
    rewrite assoc_inverse. rewrite compose_unit_l.
    setoid_rewrite lift_rc_l.
    setoid_rewrite <- (compose_assoc _ (_ (rc_adj_left _)) (_ (rc_adj_right _))).
    rewrite <- slift_compose. rewrite <- rc_adj_eta.
    rewrite slift_identity. rewrite compose_unit_l.
    rewrite <- slift_compose. rewrite <- rc_adj_eta.
    rewrite slift_identity. reflexivity.
  Qed.

End COMPILE_LAYER.

Close Scope bool_scope.

Lemma fmap_cons_bind {E A X} m (n: X) (t: t E A):
  FCD.emb (pmove m) || FCD.map (pcons m n) t = n' <- FCD.emb (pcons m n (pret n)); sup _ : n' = n, t.
Proof.
  unfold bind. setoid_rewrite FCD.ext_ana. cbn. f_equal.
  unfold FCD.map. f_equal.
  apply antisymmetry.
  - apply (sup_at eq_refl). reflexivity.
  - apply sup_iff. intros. reflexivity.
Qed.

Lemma fmap_cons_bind_ref {E A X} m (n: X) (t: t E A):
  FCD.map (pcons m n) t [= n' <- FCD.emb (pcons m n (pret n)); sup _ : n' = n, t.
Proof.
  setoid_rewrite <- fmap_cons_bind. apply join_r. reflexivity.
Qed.

Lemma apply_fmap_cons {E F A X} (f: E ~> F) m (n: X) (t: t F A):
  apply f (FCD.map (pcons m n) t) [= n' <- f _ m; sup _ : n' = n, apply f t.
Proof.
  rewrite fmap_cons_bind_ref. intm.
  setoid_rewrite FCD.ext_ana. cbn.
  unfold bind. setoid_rewrite Sup.mor. rstep.
  edestruct (FCD.join_meet_dense (f X m)) as (I & J & c & Hc).
  rewrite Hc. clear Hc.
  setoid_rewrite Sup.mor. apply sup_iff. intros i. apply (sup_at i).
  setoid_rewrite Inf.mor. apply inf_iff. intros j. apply (inf_at j).
  rewrite FCD.ext_ana.
  induction (c i j); cbn.
  - apply sup_iff. intros <-. reflexivity.
  - reflexivity.
  - apply join_lub.
    + rstep. constructor.
    + rewrite IHp. rewrite FCD.ext_ana. reflexivity.
Qed.

Section PARAMETRICITY.

  Local Opaque normalize_rc.

  Open Scope rc_scope.
  Context {S1 S2: Type} (R: S2 -> S1 -> Prop).
  Context {E1 E2: esig} (f: E1 ~> E2).

  (** f@S1 ∘ E1@R ⊑ E2@R ∘ f@S2 *)
  Lemma state_commute:
    slift (S:=S2) f @ right_arrow (rc_id (E:=E1) * rel_rc R) [=
      right_arrow (rc_id (E:=E2) * rel_rc R) @ slift (S:=S1) f.
  Proof.
    intros ar es2. destruct es2 as [ ? ? e2 [ s2 ] ].
    unfold compose. cbn. unfold rc_adj_right.
    inf_intro ar. inf_intro [ ? ? e2' [ s1 ] ]. inf_intro [Rx HRx].
    rc_inversion HRx. depsubst. clear_hyp. clear Hrel.
    rc_destruct H2. intm.
    rc_inversion H13. depsubst. clear_hyp. clear Hrel.
    generalize (f _ m). intros t.
    edestruct (FCD.join_meet_dense t) as (I & J & c & Hc). subst t.
    unfold srun.
    sup_intro i. apply (sup_at i).
    inf_intro j. apply (inf_at j).
    fcd_simpl. revert s1 s2 H4. induction (c i j); intros s1 s2 Hs; cbn.
    - fcd_simpl. sup_mor. eapply (fsup_at (v, s2)).
      + apply Hsub; split; eauto.
      + fcd_simpl. reflexivity.
    - fcd_simpl.
      inf_mor. eapply inf_at.
      inf_mor. apply (inf_at (st m0 s1)).
      inf_mor. eapply finf_at. rc_econstructor; rc_econstructor; eauto.
      sup_mor. sup_intro [ [ n s1' ] | ].
      + fcd_simpl. sup_mor. sup_mor. apply join_lub.
        * fcd_simpl. reflexivity.
        * sup_intro [ x' s2' ]. fcd_simpl.
          apply join_lub.
          -- reflexivity.
          -- sup_mor. apply bot_lb.
      + fcd_simpl. reflexivity.
    (* an angelic choice over all possible replies *)
    - sup_intro [ s2' | ].
      + rewrite apply_fmap_cons.
        inf_mor. eapply inf_at.
        inf_mor. apply (inf_at (st m0 s1)).
        inf_mor. eapply finf_at. rc_econstructor; rc_econstructor; eauto.
        unfold int at 2. sup_intro [ [ n' s1' ] | ].
        * apply (sup_at (Some s1')).
          fcd_simpl. sup_mor. sup_mor. apply join_lub.
          -- fcd_simpl. destruct p; cbn.
             ++ fcd_simpl. apply join_l. reflexivity.
             ++ fcd_simpl. apply join_l. reflexivity.
             ++ unfold FCD.map. sup_mor.
                apply (sup_at None). fcd_simpl.
                apply join_l. reflexivity.
          (* an angelic choice by R *)
          -- sup_intro [ [ n'' s2'' ] Hx ].
             destruct Hx. cbn [fst snd] in *. subst. fcd_simpl.
             apply join_lub.
             ++ destruct p; cbn.
                ** fcd_simpl. apply join_l. reflexivity.
                ** fcd_simpl. apply join_l. reflexivity.
                ** unfold FCD.map. sup_mor.
                   apply (sup_at None). fcd_simpl.
                   apply join_l. reflexivity.
             ++ sup_intro Heq. inversion Heq. subst. clear Heq.
                specialize (IHp _ _ H0). rewrite IHp. clear IHp.
                unfold FCD.map, bind, t. cbn. rewrite !FCD.ext_ext.
                {
                  apply ext_proper_ref'.
                  - split. intros p1 p2 Hp.
                    apply ext_proper_ref; try typeclasses eauto.
                    + intros px. reflexivity.
                    + rewrite Hp. reflexivity.
                  - split. intros p1 p2 Hp.
                    apply ext_proper_ref; try typeclasses eauto.
                    + intros px. reflexivity.
                    + rstep. now constructor.
                  - intros pc. fcd_simpl. apply join_r. reflexivity.
                }
        * apply (sup_at None). fcd_simpl. reflexivity.
      + apply (sup_at None). fcd_simpl.
        inf_mor. eapply inf_at.
        inf_mor. apply (inf_at (st m0 s1)).
        inf_mor. eapply finf_at. rc_econstructor; rc_econstructor; eauto.
        unfold int. sup_intro [ [ n' s1' ] | ].
        * fcd_simpl. sup_mor. sup_mor.
          apply join_lub.
          -- fcd_simpl. reflexivity.
          -- sup_intro [ [ n'' s2' ] Hx ].
             destruct Hx. cbn [fst snd] in *. subst.
             fcd_simpl. apply join_lub.
             ++ reflexivity.
             ++ sup_mor. apply bot_lb.
        * fcd_simpl. reflexivity.
  Qed.

End PARAMETRICITY.

(*
Lemma lift_strategy_simulation {E1 E2} {S1 S2 U} {L1: 0 ~> E1 # S1} {L2: 0 ~> E2 # S2}
      (C: strategy_layer U L1 L2) (K: Type):
  slift_layer (U:=K) L2 [=
    right_arrow (rc_id * rel_rc (rel_compose (eq * (R C)) assoc))
                @ slift' (right_arrow st_comm @ slift' (M C) @ left_arrow st_comm)
                @ slift_layer L1.
Proof.
  intros ar m. unfold slift_layer. cbn.
  destruct m as [ ? ? m2 [ [ k s2 ] ] ].
  unfold compose at 1. unfold rc_adj_right at 2.
  inf_mor. eapply inf_at.
  inf_mor. eapply (inf_at (m2 # (s2, k))).
  inf_mor. eapply finf_at.
  { rc_econstructor; rc_econstructor. constructor. }
  intm.
  unfold compose at 3. unfold rc_adj_right at 2.
  inf_mor. eapply inf_at.
  inf_mor. eapply (inf_at (m2 # s2 # k)).
  inf_mor. eapply finf_at.
  { rc_econstructor. }
  intm.
  unfold compose at 4.
  pose proof (simulation C) as HC.
  eapply slift_proper_ref in HC.
  specialize (HC _ (m2 # s2 # k)). rewrite HC. clear HC.
Admitted.
*)

Require Import compcert.lib.Coqlib.

Instance map_mor {A B: poset} (f: A -> B) :
  CDL.Morphism (@FCD.map A B f).
Proof. unfold FCD.map. typeclasses eauto. Qed.

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

Lemma bar {E F: esig} {S1 S2} (f: E ~> F):
  slift(S:=S1*S2) f [= right_arrow sig_assoc @ slift (slift f) @ left_arrow sig_assoc.
Proof.
  intros ? [? ? m [[s1 s2]]]. cbn.
  unfold compose, rc_adj_right, rc_adj_left.
  inf_intro ?. inf_intro m'. inf_intro [ R HR ].
  rc_inversion HR. depsubst. clear_hyp. clear Hrel. intm.
  generalize (f _ m). intros t.
  edestruct (FCD.join_meet_dense t) as (I & J & c & Hc). subst t.
  sup_intro i. apply (sup_at i).
  inf_intro j. apply (inf_at j). fcd_simpl.
  revert s1 s2. induction (c i j); intros s1 s2.
  - fcd_simpl. sup_mor. eapply fsup_at.
    { apply Hsub. constructor. }
    fcd_simpl. reflexivity.
  - fcd_simpl.
    sup_mor. eapply sup_at. sup_mor. eapply sup_at. sup_mor. eapply fsup_at.
    { rc_econstructor. }
    intm. sup_mor. sup_mor.
    apply (sup_at None). fcd_simpl. reflexivity.
  - cbn. apply sup_iff. intros [ [ x1 x2 ] | ].
    + sup_mor. apply (sup_at (Some x1)).
      rewrite IHp.
      generalize (stateful_play x1 p). intros px.
      edestruct (FCD.join_meet_dense px) as (I' & J' & c' & Hc'). subst px.
      sup_intro i'. apply (sup_at i').
      inf_intro j'. apply (inf_at j'). fcd_simpl.
      sup_mor. apply (sup_at (Some x2)).
      generalize (stateful_play x2 (c' i' j')). intros py.
      edestruct (FCD.join_meet_dense py) as (I'' & J'' & c'' & Hc''). subst py.
      sup_intro i''. apply (sup_at i'').
      inf_intro j''. apply (inf_at j''). fcd_simpl.
      match goal with
      | [ |- context[ papply ?f (c'' i'' j'') ] ] => set (fx := papply f (c'' i'' j''))
      end.
      sup_mor. eapply sup_at. sup_mor. eapply sup_at. sup_mor. eapply fsup_at.
      { rc_econstructor. }
      intm. unfold int at 3.
      sup_mor. apply (sup_at (Some (n, (x1, x2)))). fcd_simpl. apply join_r.
      inf_intro [ n' Hn ]. inv Hn. fcd_simpl.
      sup_mor. eapply (sup_at eq_refl). reflexivity.
    + sup_mor. apply (sup_at None). fcd_simpl.
      sup_mor. eapply sup_at. sup_mor. eapply sup_at. sup_mor. eapply fsup_at.
      { rc_econstructor. }
      intm. sup_mor. sup_mor. apply (sup_at None). fcd_simpl. reflexivity.
Qed.

Lemma baz {E F: esig} {S1 S2} (f: E ~> F):
  slift(S:=S1) (slift(S:=S2) f) [= right_arrow sig_comm @ slift(S:=S2) (slift(S:=S1) f) @ right_arrow sig_comm.
Proof.
Admitted.

Lemma xxx {E F: esig} {S1 S2} (f: E ~> F):
  slift(S:=S1) (slift(S:=S2) f) [=
    left_arrow sig_comm @ left_arrow sig_assoc @ (slift f) @ right_arrow sig_assoc @ right_arrow sig_comm.
Proof.
Admitted.
