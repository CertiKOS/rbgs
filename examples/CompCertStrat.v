Require Import Classical.
Require Import Program.Equality.
Require Import LogicalRelations.
Require Import Poset.
Require Import Lattice.
Require Import Downset.
Require Import IntStrat.
Require Import Classical_Prop.
Require Import Coqlib.

Ltac xsubst :=
  repeat progress
   (match goal with
    | H : ?x = ?x |- _ =>
      clear H
    | H : existT _ _ _ = existT _ _ _ |- _ =>
      apply inj_pair2 in H
    end;
    subst).

Ltac xinv H := inversion H; clear H; subst; xsubst.

(** * §6.1 Embedding CompCertO Semantics *)

From compcert Require Import Smallstep Globalenvs.
Require LanguageInterface.
Import -(notations) LanguageInterface.

(* Inductive query_se_prod {li: language_interface} := *)
(* | query_se_pair: Genv.symtbl -> query li -> query_se_prod. *)

(* https://coq.discourse.group/t/overload-list-notation/1450/2 *)

Declare Scope embed_scope.
Delimit Scope embed_scope with embed.
Inductive prod (A B : Type) : Type :=  pair : A -> B -> prod A B.
Arguments prod (A B)%type_scope.
Arguments pair {A B}%type_scope _ _.
Notation "x * y" := (prod x y) : embed_scope.
Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z) : embed_scope.

(** ** Embedding CompCertO's language interface into effect signatures *)

Canonical Structure li_sig li: esig :=
  {|
    op := (Genv.symtbl * query li)%embed;
    ar _ := reply li;
  |}.
Coercion li_sig: language_interface >-> esig.

(** ** Definition 6.1 (Embedding CompCertO's simulation conventions into
refinement conventions )*)

Section CONV.
  Local Open Scope embed.
  Obligation Tactic := cbn.

  Context {liA liB: language_interface} (cc: callconv liA liB).

  (** *** Definition *)

  Inductive cc_conv_has: rcp liA liB -> Prop :=
  | cc_conv_has_allow m1 m2 se1 se2 w
    (HSE: match_senv cc w se1 se2) (HM: match_query cc w m1 m2):
    cc_conv_has (rcp_allow (se1, m1) (se2, m2))
  | cc_conv_has_forbid m1 m2 n1 n2 se1 se2 w
    (HSE: match_senv cc w se1 se2) (HM: match_query cc w m1 m2)
    (HN: ~ match_reply cc w n1 n2):
    cc_conv_has (rcp_forbid (se1, m1) (se2, m2) n1 n2)
  | cc_conv_has_cont m1 m2 n1 n2 se1 se2 k w
    (HSE: match_senv cc w se1 se2) (HM: match_query cc w m1 m2)
    (HK: match_reply cc w n1 n2 -> cc_conv_has k):
    cc_conv_has (rcp_cont (se1, m1) (se2, m2) n1 n2 k).

  Hint Constructors cc_conv_has.
  Hint Constructors rcp_ref.

  Program Canonical Structure cc_conv: conv liA liB :=
    {| Downset.has s := cc_conv_has s |}.
  Next Obligation.
    intros x y H1. induction H1; intros Hx; try (xinv Hx; eauto).
    econstructor; eauto.
    intros. exfalso. eauto.
  Qed.

  (** [cc_conv_at] allows the choice of world to happen before the simulation,
      so that the world used in the simulation is consistent.  *)

  Inductive cc_conv_at_has: option (ccworld cc) -> rcp liA liB -> Prop :=
  | cc_conv_at_has_allow m1 m2 se1 se2 w
    (HSE: match_senv cc w se1 se2) (HM: match_query cc w m1 m2):
    cc_conv_at_has (Some w) (rcp_allow (se1, m1) (se2, m2))
  | cc_conv_at_has_forbid m1 m2 n1 n2 se1 se2 w
    (HSE: match_senv cc w se1 se2) (HM: match_query cc w m1 m2)
    (HN: ~ match_reply cc w n1 n2):
    cc_conv_at_has (Some w) (rcp_forbid (se1, m1) (se2, m2) n1 n2)
  | cc_conv_at_has_cont m1 m2 n1 n2 se1 se2 k w
    (HSE: match_senv cc w se1 se2) (HM: match_query cc w m1 m2)
    (HK: match_reply cc w n1 n2 -> cc_conv_has k):
    cc_conv_at_has (Some w) (rcp_cont (se1, m1) (se2, m2) n1 n2 k).

  Hint Constructors cc_conv_at_has.

  Program Definition cc_conv_at w: conv liA liB :=
    {| Downset.has s := cc_conv_at_has w s |}.
  Next Obligation.
    intros w x y H1. revert w. induction H1; intros w Hx; try (xinv Hx; eauto).
    - constructor; eauto.
      intros. eapply cc_conv_obligation_1; eauto.
    - constructor; eauto.
      intros. exfalso. eauto.
  Qed.

  (** *** Properties *)

  Lemma cc_conv_expand:
    cc_conv = sup w, cc_conv_at w.
  Proof.
    apply antisymmetry; intros x; cbn.
    - intros Hx. dependent destruction Hx; eauto.
    - intros (w & Hw). dependent destruction Hw; eauto.
  Qed.

  Lemma rcp_forbid_mr se1 se2 w q1 q2:
    match_senv cc w se1 se2 -> match_query cc w q1 q2 ->
    forall r1 r2, ~ Downset.has cc_conv
               (rcp_forbid (se1, q1) (se2, q2) r1 r2) ->
             match_reply cc w r1 r2.
  Proof.
    intros Hse Hq * Hr.
    apply NNPP. intros Hnr.
    apply Hr. econstructor; eauto 10.
  Qed.

  Global Instance cc_regular: RegularConv cc_conv.
  Proof.
    split. intros * Hm Hn. apply antisymmetry.
    - intros x Hx. cbn in *.
      dependent destruction Hx.
      apply HK. eapply rcp_forbid_mr; eauto.
    - intros x Hx. cbn in *.
      dependent destruction Hm.
      econstructor; eauto.
  Qed.

End CONV.

Coercion cc_conv: callconv >-> conv.

(** ** Embedding preserves identity *)

Lemma cc_conv_id {li}: @cc_conv li _ cc_id = (@vid li).
Proof.
  apply antisymmetry.
  - intros c Hc. induction c; cbn in *.
    + dependent destruction Hc. inv HSE. inv HM. eauto.
    + dependent destruction Hc. inv HSE. inv HM.
      split; eauto. cbn in HN. intros Hn. apply HN.
      apply JMeq_eq. eauto.
    + dependent destruction Hc. inv HSE. inv HM.
      split; eauto. intros HN. apply IHc.
      apply HK. apply JMeq_eq. eauto.
  - intros c Hc. induction c; cbn in *.
    + destruct m1, m2. inv Hc. econstructor; easy.
    + destruct m1, m2. destruct Hc as [Hc1 Hc2]. inv Hc1.
      econstructor; try easy. cbn.
      intros <-. apply Hc2. apply JMeq_refl.
    + destruct m1, m2. destruct Hc as [Hc1 Hc2]. inv Hc1.
      econstructor; try easy. cbn.
      intros <-. eauto.
      Unshelve. all: exact tt.
Qed.

(** ** Embedding CompCertO's transition systems *)

Close Scope list_scope.

Section LTS.
  Local Open Scope embed.
  Obligation Tactic := cbn.

  Context {liA liB: language_interface} (L: semantics liA liB).

  (** *** Definition *)

  Inductive state_strat_has (se: Genv.symtbl) (q: query liB) (s: state L): forall {i}, @play liA liB i -> Prop :=
  | state_strat_has_external_suspend m
    (* this is to make the strategy downward closed *)
    (EXT: at_external (L se) s m):
    @state_strat_has se q s (running (se, q)) (pq (se, m) :: pnil_suspended (se, q) (se, m))
  | state_strat_has_external s1 k m n
    (EXT: at_external (L se) s m) (AFT: after_external (L se) s n s1)
    (HK: state_strat_has se q s1 k):
    @state_strat_has se q s (running (se, q)) (pq (se, m) :: @oa _ _ (se, q) (se, m) n :: k)
  | state_strat_has_final r
    (FIN: final_state (L se) s r):
    @state_strat_has se q s (running (se, q)) (@pa liA liB (se, q) r :: pnil_ready)
  | state_strat_has_internal s1 k
    (STAR: Star (L se) s Events.E0 s1) (HK: state_strat_has se q s1 k):
    @state_strat_has se q s (running (se, q)) k.

  Hint Constructors state_strat_has.

  Program Definition state_strat se q s i: @strat liA liB i :=
    {| Downset.has w := @state_strat_has se q s i w |}.
  Next Obligation.
    intros *. intros Href H. revert Href. induction H; intros Href;
      simple inversion Href; try discriminate; subst; xsubst; intros Href'.
    - inv H2. xsubst. xinv Href'. eauto.
    - inv H3. xsubst. simple inversion Href'; try discriminate.
      + inv H0. xsubst. eauto.
      + subst. xsubst. inv H3. xsubst. intros Href''. eauto.
    - inv H2. xsubst. xinv Href'. eauto.
    - eauto.
  Qed.

  (** The skeleton is given as an extra parameter. When the symbol table that
      comes together with the question does not match the skeleton, the strategy
      is empty *)

  Inductive lts_strat_has sk: forall {i}, @play liA liB i -> Prop :=
  | lts_strat_has_nil: @lts_strat_has sk ready pnil_ready
  | lts_strat_has_intro se q s k
    (HVF: Genv.valid_for sk se)
    (INIT: initial_state (L se) q s)
    (HS: state_strat_has se q s k):
    @lts_strat_has sk ready (@oq liA liB (se, q) :: k).

  Program Definition lts_strat' sk i: strat liA liB i :=
    {| Downset.has w := @lts_strat_has sk i w |}.
  Next Obligation.
    intros. xinv H0.
    - xinv H. constructor.
    - simple inversion H; try discriminate.
      + xsubst. constructor.
      + intros. subst. xsubst. xinv H3.
        econstructor; eauto.
        eapply state_strat_obligation_1; eauto.
  Qed.

End LTS.

Local Hint Constructors state_strat_has lts_strat_has : core.

Definition lts_strat_sk sk {liA liB} (L: semantics liA liB): strat liA liB ready :=
  closure (lts_strat' L sk ready).
Definition lts_strat {liA liB} (L: semantics liA liB): strat liA liB ready := lts_strat_sk (skel L) L.

(** The transition system semantics in CompCertO is single-shot, so it will not
    be re-executed once it's done *)

Class NonRecur {E F p} (σ: @strat E F p): Prop :=
  { non_recur: forall s, Downset.has σ s -> no_reentrancy_play s; }.

Global Instance lts_strat_nonrecur sk {liA liB} (L: semantics liA liB) i: NonRecur (lts_strat' L sk i).
Proof.
  split. intros s Hs. cbn in Hs. dependent destruction Hs.
  { constructor. }
  constructor. clear HVF INIT. dependent induction HS.
  - constructor; eauto. constructor.
  - repeat constructor. apply IHHS; eauto.
  - constructor.
  - apply IHHS; eauto.
Qed.

(** ** Deterministic property *)

(** deterministic transition system corresponds to deterministic strategy *)

Section DETERM.

  Context {liA liB} (L: semantics liA liB) (HL: determinate L).

  Lemma state_strat_has_star i se q s1 s2 (k: play i):
    lts_determinate (L se) se ->
    state_strat_has L se q s1 k ->
    Star (L se) s1 Events.E0 s2 -> state_strat_has L se q s2 k.
  Proof.
    intros HLX H1. revert s2. dependent induction H1; intros.
    - dependent destruction H.
      + eapply state_strat_has_external_suspend; eauto.
      + exfalso. eapply sd_at_external_nostep; eauto.
    - dependent destruction H.
      + eapply state_strat_has_external; eauto.
      + exfalso. eapply sd_at_external_nostep; eauto.
    - dependent destruction H.
      + eapply state_strat_has_final; eauto.
      + exfalso. eapply sd_final_nostep; eauto.
    - exploit @star_determinacy. apply HLX. apply STAR. apply H.
      intros [X | X].
      + eauto.
      + eapply state_strat_has_internal; eauto.
  Qed.

  Instance lts_strat_determ' sk i: Deterministic (lts_strat' L sk i).
  Proof.
    split. intros s t Hs Ht. cbn in *.
    dependent destruction Hs. { constructor. }
    dependent destruction Ht. { constructor. }
    destruct (classic (se0 = se /\ q0 = q)).
    - destruct H. subst.
      apply pcons_pcoh.
      assert (s0 = s). eapply sd_initial_determ; eauto. subst.
      clear HVF HVF0 INIT INIT0. revert k0 HS0.
      specialize (HL se). dependent induction HS.
      + intros. dependent induction HS0.
        * assert (m0 = m). eapply sd_at_external_determ; eauto. subst.
          eapply pcons_pcoh. apply pnil_suspended_pcoh_l.
        * assert (m0 = m). eapply sd_at_external_determ; eauto. subst.
          eapply pcons_pcoh. apply pnil_suspended_pcoh_l.
        * exfalso. eapply sd_final_noext; eauto.
        * destruct STAR.
          -- apply IHHS0; eauto.
          -- exfalso. eapply sd_at_external_nostep; eauto.
      + intros. dependent induction HS0.
        * assert (m0 = m). eapply sd_at_external_determ; eauto. subst.
          eapply pcons_pcoh. apply pnil_suspended_pcoh_r.
        * assert (m0 = m). eapply sd_at_external_determ; eauto. subst.
          eapply pcons_pcoh.
          destruct (classic (n0 = n)).
          -- subst. eapply pcons_pcoh.
             assert (s1 = s0). eapply sd_after_external_determ; eauto. subst.
             eauto.
          -- apply pcons_pcoh_oa. eauto.
        * exfalso. eapply sd_final_noext; eauto.
        * destruct STAR.
          -- eapply IHHS0; eauto.
          -- exfalso. eapply sd_at_external_nostep; eauto.
      + intros. dependent induction HS0.
        * exfalso. eapply sd_final_noext; eauto.
        * exfalso. eapply sd_final_noext; eauto.
        * assert (r0 = r). eapply sd_final_determ; eauto.
          subst. apply pcons_pcoh. apply pnil_ready_pcoh_l.
        * destruct STAR.
          -- apply IHHS0; eauto.
          -- exfalso. eapply sd_final_nostep; eauto.
      + dependent destruction STAR.
        * apply IHHS; eauto.
        * symmetry in H0. apply app_eq_nil in H0 as [-> ->].
          intros. dependent induction HS0.
          -- exfalso. eapply sd_at_external_nostep; eauto.
          -- exfalso. eapply sd_at_external_nostep; eauto.
          -- exfalso. eapply sd_final_nostep; eauto.
          -- exploit @star_determinacy. apply HL. apply STAR0.
             eapply star_step; eauto.
             intros [X | X].
             ++ eapply IHHS; eauto.
                eapply state_strat_has_star; eauto.
             ++ eapply IHHS; eauto.
    - apply pcons_pcoh_oq.
      intros Hx. inv Hx. eauto.
  Qed.

  Inductive is_pnil_ready {E F}: forall {i}, @play E F i -> Prop :=
  | is_pnil_ready_intro: is_pnil_ready pnil_ready.

  Definition pcoh_dep {E F i} (s: @play E F i) (t: @play E F ready): Prop.
  Proof. destruct i. refine (pcoh s t). 1-2: refine True. Defined.

  Lemma seq_comp_pcoh {E F i} (s1 s t1 t: @play E F i) s2 t2:
    seq_comp_has s1 s2 s -> seq_comp_has t1 t2 t ->
    pcoh s1 t1 -> pcoh s2 t2 ->
    (is_pnil_ready s1 -> pcoh_dep t s2) -> (is_pnil_ready t1 -> pcoh_dep s t2) ->
    no_reentrancy_play s1 -> no_reentrancy_play t1 ->
    pcoh s t.
  Proof.
    intros Hs Ht Hc1 Hc2 Hd1 Hd2 Ho1 Ho2. revert t1 t2 t Ht Hc1 Hc2 Hd1 Hd2 Ho1 Ho2.
    dependent induction Hs; intros.
    - apply symmetry. apply Hd1. constructor.
    - dependent destruction Hc1.
      + dependent destruction Ht. apply Hd2. constructor.
      + dependent destruction Ht.
        apply pcons_pcoh. eapply IHHs; eauto. easy. easy.
        xinv Ho1; eauto. xinv Ho2; eauto.
      + dependent destruction Ht. apply pcons_pcoh_oq. eauto.
    - dependent destruction Hc1. dependent destruction Ht.
      apply pcons_pcoh. eapply IHHs; eauto. easy. easy.
      xinv Ho1; eauto. xinv Ho2; eauto.
    - apply pnil_suspended_pcoh_l.
    - dependent destruction Hc1.
      + dependent destruction Ht. apply pnil_suspended_pcoh_r.
      + dependent destruction Ht.
        apply pcons_pcoh. eapply IHHs; eauto. easy. easy.
        xinv Ho1; eauto. xinv Ho2; eauto.
      + dependent destruction Ht. apply pcons_pcoh_oa. eauto.
    - dependent destruction Hc1. dependent destruction Ht.
      apply pcons_pcoh.
      dependent destruction Ho1. dependent destruction Ho2.
      dependent destruction Hs. dependent destruction Ht. eauto.
  Qed.

  Hint Constructors closure_has : core.

  Lemma closure_determ {E F} (σ: @strat E F ready):
    Deterministic σ -> NonRecur σ ->
    Deterministic (closure σ).
  Proof.
    intros Hd Ho. split.
    intros s t Hs Ht. cbn in *.
    revert t Ht.
    dependent induction Hs. { constructor. }
    rename s into s0. rename t into s1. rename w into s.
    intros t Ht.
    dependent induction Ht. { constructor. }
    rename s2 into t0. rename t into t1. rename w into t.
    assert (pcoh s0 t0). apply determinism; eauto.
    assert (pcoh s1 t1). eauto.
    assert (pcoh t s1). symmetry. eapply IHHs; eauto.
    assert (pcoh s t1). eapply IHHt; eauto.
    eapply seq_comp_pcoh; eauto.
    apply non_recur; eauto. apply non_recur; eauto.
  Qed.

  Instance lts_strat_determ sk: Deterministic (lts_strat_sk sk L).
  Proof.
    apply closure_determ. typeclasses eauto. apply lts_strat_nonrecur.
  Qed.

End DETERM.

(** ** Soundness of CompCertO's simulation *)

(** CompCertO’s compiler correctness corresponds to the refinement square *)

Section FSIM.
  Local Open Scope embed_scope.

  Context {liA1 liA2 liB1 liB2: language_interface}
    (ccA: callconv liA1 liA2) (ccB: callconv liB1 liB2)
    (L1: semantics liA1 liB1) (L2: semantics liA2 liB2) (DL2: determinate L2)
    (FSIM: forward_simulation ccA ccB L1 L2).

  Lemma fsim_rsq_sk sk:
    Linking.linkorder (skel L1) sk ->
    rsq ccA ccB (lts_strat_sk sk L1) (lts_strat_sk sk L2).
  Proof.
    intros Hsk. apply rsq_closure; try apply cc_regular.
    setoid_rewrite cc_conv_expand at 2. apply rsq_sup.
    { apply lts_strat_determ'. apply DL2. }
    { constructor. eauto using None. }
    intros w. destruct w as [w|].
    2: { intros p Hp. xinv Hp; repeat constructor.
         intros q2 Hq2. xinv Hq2. }
    intros p Hp. cbn in Hp. xinv Hp. { repeat constructor. }
    constructor. { constructor. }
    intros q2 Hq2. cbn in Hq2.
    rename q into q1. destruct q2 as (se2 & q2).
    xinv Hq2. destruct FSIM. destruct X.
    assert (HVF1: Genv.valid_for (skel L1) se).
    { eapply Genv.valid_for_linkorder; eauto. }
    specialize (fsim_lts _ _ _ HSE HVF1).
    rename s into s1. rename se into se1.
    edestruct (@fsim_match_initial_states) as (i & s2 & A & B); eauto.
    assert (Hs: state_strat L2 se2 q2 s2 (running (se2, q2))
                  [= (next (oq (se2, q2)) (lts_strat' L2 sk ready))).
    { intros p Hp. cbn in *. econstructor; eauto.
      eapply match_senv_valid_for in HSE. apply HSE. eauto. }
    rewrite <- Hs. clear Hs fsim_skel fsim_footprint A HVF INIT.
    revert i s2 B. dependent induction HS; intros i ts Hts.
    - edestruct @fsim_match_external as (wx & tq2 & A & B & C & D); eauto.
      eapply rsp_pq. econstructor; eauto.
      eapply rsp_suspended. cbn. econstructor; eauto.
    - edestruct @fsim_match_external as (wx & tq2 & A & B & C & D); eauto.
      eapply rsp_pq. econstructor; eauto.
      eapply rsp_oa. cbn. econstructor; eauto.
      intros n2 Hn.
      rewrite @regular_conv. 2: apply cc_regular.
      2: { econstructor; eauto. }
      2: apply Hn.
      cbn in Hn. eapply rcp_forbid_mr in Hn; eauto.
      specialize (D _ _ _ Hn AFT) as (i' & ts2 & X & Y).
      exploit IHHS; eauto. intros Z.
      assert (Hs: state_strat L2 se2 q2 ts2 (running (se2, q2))
               [= next (oa n2) (next (pq (se2, tq2)) (state_strat L2 se2 q2 ts (running (se2, q2))))).
      { intros p Hp. cbn in *. econstructor; eauto. }
      rewrite <- Hs. apply Z.
    - edestruct (@fsim_match_final_states) as (r2 & A & B); eauto.
      eapply rsp_pa with (r2 := r2).
      + intros Hr. xinv Hr. eauto.
      + constructor. cbn. econstructor; eauto.
    - edestruct @simulation_star as (i1 & ts1 & A & B); eauto.
      assert (Hs: state_strat L2 se2 q2 ts1 (running (se2, q2))
                    [= state_strat L2 se2 q2 ts (running (se2, q2))).
      { intros p Hp. cbn in *. eapply state_strat_has_internal; eauto. }
      rewrite <- Hs. eauto.
    Qed.

  Local Coercion lts_strat: semantics >-> strat.

  Lemma fsim_rsq: rsq ccA ccB L1 L2.
  Proof.
    unfold lts_strat. destruct FSIM as [[X]]. rewrite <- fsim_skel.
    eapply fsim_rsq_sk. apply Linking.linkorder_refl.
  Qed.

End FSIM.

(** The strategy that corresponds to transition system are regular strategies *)

Section REGULAR.

  Hint Constructors pref play_suspended seq_comp_has play_suspended no_reentrancy_play : core.

  Lemma lts_strat_no_reentrancy sk {liA liB} (L: semantics liA liB) i:
    no_reentrancy (lts_strat' L sk i).
  Proof.
    intros s Hs. cbn in Hs. dependent destruction Hs; eauto.
    constructor 3. clear HVF INIT. dependent induction HS; eauto.
  Qed.

  Instance lts_regular sk {liA liB} (L: semantics liA liB):
    Regular (lts_strat_sk sk L).
  Proof.
    split. eexists; split. reflexivity. apply lts_strat_no_reentrancy.
  Qed.

End REGULAR.

(** Properties of regular strategies and properties between sequential
    composition and horizontal composotion. These are used when proving the
    embedding preserves the composition *)

Arguments play_suspended {E F i} _.

Section REGULAR.

  Hint Constructors pref play_suspended seq_comp_has play_suspended no_reentrancy_play : core.

  Lemma no_reentrancy_play_ref {E F i} (s t: @play E F i):
    s [= t -> no_reentrancy_play t -> no_reentrancy_play s.
  Proof.
    intros Href Ht. revert s Href. dependent induction Ht;
      intros; cbn in *; dependent destruction Href; eauto.
    xinv Href. eauto.
  Qed.

  Lemma comp_has_suspended {E F G i j k} (p: cpos i j k) (s: @play F G i) (t: @play E F j) w:
    comp_has p s t w -> play_suspended w -> play_suspended t.
  Proof.
    intros H. dependent induction H; intros Hp; dependent destruction Hp; eauto.
  Qed.

  Lemma seq_comp_has_suspended1' {E F i} (s1: @play E F i) s2 s t2:
    seq_comp_has s1 s2 s -> play_suspended s1 -> seq_comp_has s1 t2 s.
  Proof.
    intros H. dependent induction H; intros Hp; dependent destruction Hp; eauto.
  Qed.

  Lemma seq_comp_has_suspended1 {E F i} (s1: @play E F i) s2 s:
    seq_comp_has s1 s2 s -> play_suspended s1 -> s = s1.
  Proof.
    intros H. dependent induction H; intros Hp; dependent destruction Hp; eauto.
    all: f_equal; eauto.
  Qed.

  Lemma seq_comp_has_suspended2 {E F i} (s1: @play E F i) s2 s:
    seq_comp_has s1 s2 s -> play_suspended s2 -> play_suspended s.
  Proof.
    intros H. dependent induction H; intros Hp; dependent destruction Hp; eauto.
  Qed.

  Lemma seq_comp_has_suspended3 {E F i} (s1: @play E F i) s2 s:
    seq_comp_has s1 s2 s -> ~ play_suspended s -> ~ play_suspended s1 /\ ~ play_suspended s2.
  Proof.
    intros. apply NNPP. intros HX. apply H0.
    apply not_and_or in HX as [HX | HX]; apply NNPP in HX.
    - exploit @seq_comp_has_suspended1; eauto. congruence.
    - eauto using seq_comp_has_suspended2.
  Qed.

  Lemma seq_comp_has_nil1 {E F i} (s1: @play E F i) s:
    seq_comp_has s1 pnil_ready s -> s1 = s.
  Proof. intros. dependent induction H; f_equal; eauto. Qed.

  Lemma seq_comp_has_nil2 {E F i} (s1: @play E F i) s:
    s1 = s -> seq_comp_has s1 pnil_ready s.
  Proof.
    revert s. dependent induction s1; intros; subst; eauto.
    dependent destruction m; constructor; eauto.
  Qed.

  Lemma play_suspended_cons_contrapos {E F i j} (t: @play E F i) (m: move j i):
    ~ play_suspended (m :: t) -> ~ play_suspended t.
  Proof.
    intros Hs Hs'. apply Hs. constructor; eauto.
  Qed.

  Lemma seq_comp_split1 {E F i} (s: @play E F i) s1 s2 t1 t2:
    seq_comp_has s1 s2 s -> seq_comp_has t1 t2 s ->
    t1 [= s1 -> ~ play_suspended t1 ->
    exists x, seq_comp_has t1 x s1 /\ seq_comp_has x s2 t2.
  Proof.
    intros Hs Ht Hst Hp. revert s1 s2 Hs Hst Hp.
    dependent induction Ht; intros.
    Ltac seq_comp_split Hst Hs Hp IHHt H1 x :=
      xinv Hst; dependent destruction Hs;
      apply play_suspended_cons_contrapos in Hp;
      specialize (IHHt _ _ Hs H1 Hp) as (x & A & B);
      exists x; split; eauto.
    - intros. exists s1. split; eauto.
    - seq_comp_split Hst Hs Hp IHHt H1 x.
    - seq_comp_split Hst Hs Hp IHHt H1 x.
    - intros. xinv Hs. exfalso. apply Hp. constructor.
    - seq_comp_split Hst Hs Hp IHHt H1 x.
    - seq_comp_split Hst Hs Hp IHHt H1 x.
  Qed.

  (* TODO: cleanup the copy-and-paste *)
  Lemma seq_comp_split2 {E F i} (s: @play E F i) s1 s2 t1 t2:
    seq_comp_has s1 s2 s -> seq_comp_has t1 t2 s ->
    t1 [= s1 -> ~ play_suspended s1 ->
    exists x, seq_comp_has t1 x s1 /\ seq_comp_has x s2 t2.
  Proof.
    intros Hs Ht Hst Hp. revert s1 s2 Hs Hst Hp.
    dependent induction Ht; intros.
    - intros. exists s1. split; eauto.
    - seq_comp_split Hst Hs Hp IHHt H1 x.
    - seq_comp_split Hst Hs Hp IHHt H1 x.
    - intros. xinv Hs. exfalso. apply Hp. constructor.
    - seq_comp_split Hst Hs Hp IHHt H1 x.
    - seq_comp_split Hst Hs Hp IHHt H1 x.
  Qed.

  Lemma seq_comp_has_incr {E F i} (s1: @play E F i) s2 s:
    seq_comp_has s1 s2 s -> s1 [= s.
  Proof.
    intros Hs. dependent induction Hs; constructor; eauto.
  Qed.

  Lemma no_reentrancy_seq_decomp {E F i} (s: @play E F i) s1 s2:
    no_reentrancy_play s -> seq_comp_has s1 s2 s -> ~ play_suspended s1 ->
    match i with
    | ready => s1 ~= (@pnil_ready E F) \/ s2 = pnil_ready
    | _ => s2 = pnil_ready
    end.
  Proof.
    intros Hs. revert s1 s2. dependent induction Hs.
    - intros. xinv H. right. easy.
    - intros. xinv H. exfalso. eauto.
    - intros. dependent destruction H.
      + left. apply JMeq_refl.
      + right. apply play_suspended_cons_contrapos in H0. eauto.
    - intros. dependent destruction H.
      apply play_suspended_cons_contrapos in H0. eauto.
    - intros. dependent destruction H.
      apply play_suspended_cons_contrapos in H0. eauto.
    - intros. dependent destruction H. xinv H. reflexivity.
  Qed.

  Lemma pref_or {E F i} (s t: @play E F i) w:
    s [= w -> t [= w -> s [= t \/ t [= s.
  Proof.
    intros H1. revert t. induction H1; intros; cbn; eauto.
    cbn in *. dependent destruction H; eauto.
    specialize (IHpref _ H) as [A | A]; eauto.
  Qed.

  Lemma regular_seq_decomp {E F} (σ: strat E F ready) s1 s2 s:
    Regular σ -> Downset.has σ s -> seq_comp_has s1 s2 s ->
    ~ play_suspended s1 -> Downset.has σ s2.
  Proof.
    intros [Hr] Hs1 Hs2 Hp. destruct Hr as (σ0 & Hx & Hy). subst.
    revert s1 s2 Hs2 Hp. cbn in Hs1. dependent induction Hs1.
    { intros. xinv Hs2. apply closure_has_nil. }
    intros * Hs Hp. rename s into t1. rename t into t2.
    edestruct (pref_or t1 s1) as [Hq | Hq].
    1-2: eapply seq_comp_has_incr; eauto.
    - assert (exists w1, seq_comp_has t1 w1 s1 /\ seq_comp_has w1 s2 t2)
        as (w1 & Hw1 & Hw2).
      { eapply seq_comp_split2; eauto. }
      assert (HW: ~ play_suspended w1); eauto.
      { intros Hx. apply Hp. eapply seq_comp_has_suspended2; eauto. }
    - edestruct @seq_comp_split1 as (w1 & Hw1 & Hw2).
      3: eauto. 1-3: eauto.
      exploit @no_reentrancy_seq_decomp. 2: apply Hw1. 1-2: eauto.
      intros [ Hxs | -> ].
      + apply JMeq_eq in Hxs. subst.
        dependent destruction Hw1. 
        eapply closure_has_cons. 3: eauto. 1-2: eauto.
      + dependent destruction Hw2. eauto.
  Qed.

  Lemma regular_seq_comp {E F}  (σ: strat E F ready) s1 s2 s:
    Regular σ -> Downset.has σ s1 -> Downset.has σ s2 ->
    seq_comp_has s1 s2 s -> Downset.has σ s.
  Proof.
    intros [Hr] Hs1 Hs2 Hs. destruct Hr as (σ0 & Hx & Hy). subst.
    eapply closure_seq_comp. 3: eauto. 1-2: eauto.
  Qed.

  Lemma regular_non_empty {E F}  (σ: strat E F ready):
    Regular σ -> exists s, Downset.has σ s.
  Proof.
    intros [Hr]. destruct Hr as (σ0 & Hx & Hy). subst.
    exists pnil_ready. constructor.
  Qed.

End REGULAR.

(** A few more properties between sequential composition and horizontal
    composotion. *)

Section PROPERTY.

  Hint Constructors play_suspended seq_comp_has comp_has closure_has : core.

  Lemma closure_has_cons_inv {E F i} (σ: strat E F ready) p (s: play i):
    closure_has σ (p :: s) ->
    exists s1 s2, Downset.has σ (p :: s1) /\ closure_has σ s2 /\ seq_comp_has s1 s2 s.
  Proof.
    remember (p :: s) as w. intros H. revert p s Heqw.
    dependent induction H.
    - intros. xinv Heqw.
    - intros. xinv Heqw. xinv H1; eauto 10; try easy.
  Qed.

  Lemma comp_has_exists {E: esig} {F G i j k} (p: cpos i j k) (s: @play F G i):
    inhabited E -> exists (t: @play E F j) w, comp_has p s t w .
  Proof.
    intros HE. revert j k p. dependent induction s; dependent destruction p.
    - exists pnil_ready, pnil_ready. eauto.
    - inversion HE.
      eexists (pq X :: pnil_suspended _ _), (pq X :: pnil_suspended _ _); eauto.
    - eauto.
    - dependent destruction m.
      specialize (IHs HE _ _ (cpos_left q)) as (t & w & H).
      exists t, (oq q :: w). eauto.
    - dependent destruction m.
      + specialize (IHs HE _ _ (cpos_right q m)) as (t & w & H).
        exists (oq m :: t), w. eauto.
      + specialize (IHs HE _ _ cpos_ready) as (t & w & H).
        exists t, (pa r :: w). eauto.
    - dependent destruction m.
      specialize (IHs HE _ _ (cpos_left q)) as (t & w & H).
      exists (pa n :: t), w. eauto.
    - eauto.
  Qed.

  Lemma decompose_comp {E F G i j k}
    p1 (s: @play F G i) (t: @play E F j) (w: play k) s1 s2:
    comp_has p1 s t w -> seq_comp_has s1 s2 s ->
    exists t1 t2 w1 w2,
      comp_has p1 s1 t1 w1 /\ comp_has cpos_ready s2 t2 w2 /\
      seq_comp_has t1 t2 t /\ seq_comp_has w1 w2 w /\
      (play_suspended t1 -> play_suspended w1).
  Proof.
    intros Hc Hs. revert s1 s2 Hs. dependent induction Hc.
    - intros. xinv Hs.
      exists pnil_ready, t, pnil_ready, pnil_ready.
      firstorder eauto. xinv H.
    - intros. dependent destruction Hs.
      + eexists pnil_ready, _, pnil_ready, _.
        firstorder eauto 10. xinv H.
      + specialize (IHHc _ _ Hs)
          as (t1 & t2 & w1 & w2 & A & B & C & D & P).
        eauto 20.
    - intros. dependent destruction Hs.
      specialize (IHHc _ _ Hs)
        as (t1 & t2 & w1 & w2 & A & B & C & D & P).
      eexists _, _, _, _. firstorder eauto.
      xinv H. eauto.
    - intros.
      specialize (IHHc _ _ Hs) as (t1 & t2 & w1 & w2 & A & B & C & D).
      exists (pq u :: t1), t2, (pq u :: w1), w2. firstorder eauto 10.
      xinv H1. eauto.
    - intros.
      assert (exists tx (wx: @play E G ready), comp_has cpos_ready s2 tx wx)
        as (t2 & w2 & Hw2); eauto 10.
      apply comp_has_exists. eauto.
    - intros.
      specialize (IHHc _ _ Hs) as (t1 & t2 & w1 & w2 & A & B & C & D).
      exists (oa v :: t1), t2, (oa v :: w1), w2. firstorder eauto 10.
      xinv H1. eauto.
    - intros. dependent destruction Hs; eauto 10.
      specialize (IHHc _ _ Hs) as (t1 & t2 & w1 & w2 & A & B & C & D & P).
      eexists _, _, _, _. firstorder eauto 10.
      xinv H. eauto.
    - intros. dependent destruction Hs; eauto 10.
      specialize (IHHc _ _ Hs) as (t1 & t2 & w1 & w2 & A & B & C & D & P).
      eauto 20.
  Qed.

  Lemma decompose_seq_comp {E F G i j k}
    p1 (w1: @play E G k) w2 w (s1: @play F G i) s2 (t1: @play E F j) t2:
    seq_comp_has w1 w2 w -> comp_has p1 s1 t1 w1 -> comp_has cpos_ready s2 t2 w2 ->
    exists s t1_head t1_trail t,
      seq_comp_has s1 s2 s /\ seq_comp_has t1_head t1_trail t1 /\
        seq_comp_has t1_head t2 t /\ comp_has p1 s t w.
  Proof.
    intros Hw Hw1 Hw2. revert w w2 s2 t2 Hw Hw2.
    dependent induction Hw1.
    - intros. dependent induction Hw.
      eexists s2, _, _, _. firstorder eauto.
    - intros. dependent destruction Hw.
      edestruct IHHw1 as (sx & t1_head & t1_trail & tx & A & B & C & D); eauto.
      eexists _, _, _, _. firstorder eauto.
    - intros.
      edestruct IHHw1 as (sx & t1_head & t1_trail & tx & A & B & C & D); eauto.
      eexists (pq m :: sx), (oq m :: t1_head), _, _. firstorder eauto.
    - intros. dependent destruction Hw.
      edestruct IHHw1 as (sx & t1_head & t1_trail & tx & A & B & C & D); eauto.
      eexists _, _, _, _. firstorder eauto.
    - intros. dependent destruction Hw.
      edestruct @seq_comp_has_exists as (si & Hsi).
      eexists si, _, _, _. firstorder eauto.
    - intros. dependent destruction Hw.
      edestruct IHHw1 as (sx & t1_head & t1_trail & tx & A & B & C & D); eauto.
      eexists _, _, _, _. firstorder eauto.
    - intros.
      edestruct IHHw1 as (sx & t1_head & t1_trail & tx & A & B & C & D); eauto.
      eexists _, _, _, _. firstorder eauto.
    - intros. dependent destruction Hw.
      edestruct IHHw1 as (sx & t1_head & t1_trail & tx & A & B & C & D); eauto.
      eexists _, _, _, _. firstorder eauto.
    Unshelve. eauto.
  Qed.

End PROPERTY.

(** ** The embedding preserves composition *)

(** In the sense that [L1] ⊙ [L2] ⊑ [L1 ⊙ L2] *)

Require Import CategoricalComp.

Section CC_COMP.

  Hint Constructors play_suspended seq_comp_has comp_has closure_has : core.

  (** The interaction between the closure operator and composition:
        s* ∘ t = (s ∘ t)*
   *)
  Lemma closure_comp {E F G} (σ: strat F G ready) (τ: strat E F ready)
    (Hτ: Regular τ):
    (closure σ) ⊙ τ = closure (σ ⊙ τ).
  Proof.
    apply antisymmetry.
    - intros ? (s & t & Hs & Ht & Hst). cbn in *.
      revert t c Hst Ht. dependent induction Hs.
      { intros. dependent destruction Hst. constructor. }
      rename s into s1. rename t into s2. rename w into s.
      intros. edestruct @decompose_comp as
        (t1 & t2 & w1 & w2 & A & B & C & D & P); eauto.
      specialize (IHHs _ _ B).
      destruct (classic (play_suspended t1)) as [Hp | Hp].
      + specialize (P Hp).
        eapply closure_has_cons with (s := c) (t := pnil_ready).
        * exists s1, t1. repeat apply conj.
          -- apply H.
          -- eapply Downset.closed; eauto.
             eapply seq_comp_has_incr; eauto.
          -- exploit @seq_comp_has_suspended1. apply D. apply P. congruence.
        * apply closure_has_nil.
        * apply seq_comp_has_nil2; eauto.
      + eapply closure_has_cons. 3: eauto.
        * cbn. exists s1, t1. repeat apply conj; eauto.
          eapply Downset.closed; eauto.
          eapply seq_comp_has_incr; eauto.
        * eapply IHHs. eauto.
          exploit @regular_seq_decomp; eauto.
    - intros ? H. cbn in *. dependent induction H.
      { exists pnil_ready, pnil_ready. repeat apply conj; eauto.
        edestruct @regular_non_empty as (s & Hs); eauto.
        eapply Downset.closed; eauto. constructor. }
      destruct H as (s1 & s2 & Hs1 & Hs2 & Hst1).
      edestruct IHclosure_has as (t1 & t2 & Ht1 & Ht2 & Hst2); eauto.
      edestruct @decompose_seq_comp as (si & t1_head & t1_trail & ti & A & B & C & D); eauto.
      exists si, ti. repeat apply conj; eauto.
      eapply regular_seq_comp. 1,4: eauto. 2: eauto.
      eapply Downset.closed.
      eapply seq_comp_has_incr. apply B. eauto.
  Qed.

  (** We first show the embedding preserves composition of single-shot execution *)

  Context {liA liB liC} (L1: semantics liB liC) (L2: semantics liA liB).

  Lemma cc_comp_ref_once sk1 sk2:
    (lts_strat' L1 sk1 ready) ⊙ (lts_strat_sk sk2 L2) [= lts_strat' (comp_semantics' L1 L2 sk1) sk1 ready.
  Proof.
    intros ? (s & t & Hs & Ht & Hst). cbn in *.
    dependent destruction Hs.
    { dependent destruction Hst. constructor. }
    dependent destruction Hst.
    eapply lts_strat_has_intro with (s := st1 L1 L2 s0); eauto.
    { constructor; eauto. }
    clear HVF INIT. revert t Ht w Hst.
    dependent induction HS; intros.
    - (* L1 calls L2 but no return *)
      xinv Hst. apply closure_has_cons_inv in Ht.
      destruct Ht as (ts1 & ts2 & Hs1 & Hs2 & Hss).
      xinv Hs1.
      eapply state_strat_has_internal.
      apply star_one. eapply step_push; eauto.
      clear EXT Hs2 HVF INIT.
      dependent induction HS.
      + (* L2 makes a call but no return *)
        xinv Hss. xinv H4. xinv H5. xinv H7.
        eapply state_strat_has_external_suspend.
        constructor. eauto.
      + (* L2 makes a call and receives return value *)
        xinv Hss. xinv H4. xinv H5. xinv H8.
        eapply state_strat_has_external; try constructor; eauto.
      + (* L2 returns, which leads to contradiction *)
        xinv Hss. xinv H3. xinv H5.
      + (* L2 internal steps *)
        eapply state_strat_has_internal. apply star_internal2. eauto.
        eauto.
    - (* L1 calls L2 and L2 returns to L1 *)
      specialize (IHHS L2 k0 eq_refl JMeq_refl).
      xinv Hst. apply closure_has_cons_inv in Ht.
      destruct Ht as (ts1 & ts2 & Hs1 & Hs2 & Hss).
      specialize (IHHS _ Hs2). xinv Hs1.
      eapply state_strat_has_internal.
      apply star_one. eapply step_push; eauto.
      clear EXT Hs2 HVF INIT. dependent induction HS0.
      + (* L2 makes a call but no return, which should be a contradiction? *)
        xinv Hss. xinv H4. xinv H5. xinv H7.
        eapply state_strat_has_external_suspend.
        constructor. eauto.
      + (* L2 makes a call and receives return value *)
        xinv Hss. xinv H4. xinv H5. xinv H8.
        eapply state_strat_has_external; try constructor; eauto.
      + (* L2 returns *)
        xinv Hss. xinv H5. xinv H3.
        eapply state_strat_has_internal.
        apply star_one. eapply step_pop; eauto.
        eauto.
      + (* L2 internal steps *)
        eapply state_strat_has_internal. apply star_internal2. eauto.
        eauto.
    - (* L1 returns *)
      xinv Hst. xinv H4.
      apply state_strat_has_final. constructor. apply FIN.
    - (* L1 internal step *)
      eapply state_strat_has_internal. apply star_internal1. eauto.
      eauto.
  Qed.

  Global Instance closure_ref:
    Monotonic (@closure) (forallr -, forallr -, ref ++> ref).
  Proof.
    intros E F x y H s Hs.
    cbn in *. revert y H. dependent induction Hs.
    - constructor.
    - intros. eauto.
  Qed.

  (** The embedding of transition systems preserve composition comes as a
      corollary *)

  Lemma cc_comp_ref sk1 sk2:
    (lts_strat_sk sk1 L1) ⊙ (lts_strat_sk sk2 L2) [= lts_strat (comp_semantics' L1 L2 sk1).
  Proof.
    unfold lts_strat.
    replace (skel (comp_semantics' L1 L2 sk1)) with sk1 by reflexivity.
    unfold lts_strat_sk.
    rewrite <- cc_comp_ref_once.
    rewrite closure_comp. unfold lts_strat_sk. reflexivity.
    apply lts_regular.
  Qed.

End CC_COMP.

(** The interaction between the closure operator and the spacial composition.
    Particularly,

      (σ @ U)* = σ* @ U.
 *)

Section CLOSURE_SCOMP.

 Hint Constructors seq_comp_has tstrat_has lens_has closure_has : core.

  Lemma seq_comp_tstrat {E1 F1 E2 F2 i j k} (tp: tpos i j k)
    (s1: @play (tens E1 F1) (tens E2 F2) k) s2 s
    (es1: @play E1 E2 i) (fs1: @play F1 F2 j) es2 fs2:
    seq_comp_has s1 s2 s -> tstrat_has tp es1 fs1 s1 -> tstrat_has tp_ready es2 fs2 s2 ->
    exists e f,
      seq_comp_has es1 es2 e /\ seq_comp_has fs1 fs2 f /\ tstrat_has tp e f s.
  Proof.
    intros Hs Ht1 Ht2. revert s2 s Hs es2 fs2 Ht2.
    Ltac tstrat_seq_comp_solve1 :=
      dependent destruction Hs; eexists _, _; repeat apply conj; eauto.
    Ltac tstrat_seq_comp_solve2 IHHt1 :=
      dependent destruction Hs;
      edestruct IHHt1 as (e & f & He & Hf & Hef); eauto;
      eexists _, _; repeat apply conj; eauto.
    induction Ht1; intros; try solve [ tstrat_seq_comp_solve1 | tstrat_seq_comp_solve2 IHHt1 ].
  Qed.

  (* This could be generalized to any (stateful?) lens *)
  Lemma tstrat_has_exists {E F U i} (s: @play E F i):
    inhabited U ->
    exists j sp k (tp: tpos i j k) t st,
      @lens_has U U lid _ sp t /\ tstrat_has tp s t st /\
        (match sp with
         | lready _ _ => True
         | lrunning _ _ v u | lsuspended _ _ v u => v = u
         end).
  Proof.
    intros [u]. dependent induction s.
    - eexists _, _, _, tp_ready, _, _. split; eauto.
    - eexists _, _, _, _, _, _. split; eauto.
    - dependent destruction m;
        destruct (IHs u) as (j & sp & k & tp & t & ts & HA & HB & HC);
        dependent destruction tp; dependent destruction sp; destruct p; subst.
      + eexists _, _, _, _, (oq u0 :: _), _. eauto.
      + eexists _, _, _, _, (pq m2 :: _), _. eauto.
      + eexists _, _, _, _, (oa _ :: _), _. eauto.
      + eexists _, _, _, _, (pa _ :: _), _.
        split. apply lens_pa with (p := tt) (p' := tt). eauto.
        cbn. reflexivity. split; eauto.
        Unshelve. 1,3: exact tt. all: exact u.
  Qed.

  Lemma tstrat_seq_comp {E1 E2 U i j k} (tp: tpos i j k)
    es fs es1 es2 (s: @play (E1@U) (E2@U) _) st1:
    tstrat_has tp es fs s ->
    seq_comp_has es1 es2 es ->
    lens_has lid st1 fs ->
    exists s1 s2 st2 fs1 fs2,
      lens_has lid st1 fs1 /\ lens_has lid st2 fs2 /\
      tstrat_has tp es1 fs1 s1 /\ tstrat_has tp_ready es2 fs2 s2 /\
      seq_comp_has s1 s2 s.
  Proof.
    intros Ht Hs Hf. revert es1 es2 Hs st1 Hf.
    induction Ht; intros.
    - dependent destruction Hs.
      eexists _, _, _, _, _; eauto.
    - dependent destruction Hs; dependent destruction Hf.
      + eexists pnil_ready, _, _, pnil_ready, (oq _ :: _); repeat apply conj; eauto.
      + edestruct IHHt as (xs1 & xs2 & st2 & fs1 & fs2 & HA & HB & HC & HD & HE); eauto.
        eexists _, _, _, (oq _ :: _), _; repeat apply conj; eauto.
    - dependent destruction Hs; dependent destruction Hf.
      edestruct IHHt as (xs1 & xs2 & st2 & fs1 & fs2 & HA & HB & HC & HD & HE); eauto.
      eexists _, _, _, _, _; repeat apply conj; eauto.
    - dependent destruction Hs.
      edestruct (tstrat_has_exists (U:=U) t) as (j & sp & k & tp & xt & ts & HA & HB & HC).
      split. exact q2. dependent destruction tp.
      eexists _, _, _, _, xt; repeat apply conj; eauto.
    - dependent destruction Hs; dependent destruction Hf.
      edestruct IHHt as (xs1 & xs2 & st2 & fs1 & fs2 & HA & HB & HC & HD & HE); eauto.
      eexists _, _, _, (oa _ :: _), _; repeat apply conj; eauto.
    - dependent destruction Hs; dependent destruction Hf.
      edestruct IHHt as (xs1 & xs2 & st2 & fs1 & fs2 & HA & HB & HC & HD & HE); eauto.
      eexists _, _, _, (pa _ :: _), _; repeat apply conj; eauto.
      econstructor; eauto.
  Qed.

  Lemma lens_seq_comp {U V i} (l: bijection U V) (sp: lpos l i) tp s t st:
    seq_comp_has s t st ->
    lens_has l sp s ->
    lens_has l tp t ->
    lens_has l sp st.
  Proof.
    intros Hst Hs Ht. revert sp tp Hs Ht. dependent induction Hst.
    - intros. dependent destruction sp. dependent destruction tp.
      destruct p, p0. eauto.
    - intros. dependent destruction Hs. eauto.
    - intros. dependent destruction Hs. eauto.
    - intros. eauto.
    - intros. dependent destruction Hs. eauto.
    - intros. dependent destruction Hs. eauto.
  Qed.

  Lemma closure_lift {E F} {U: Type} (σ: strat E F ready):
    closure (σ@U) = (closure σ)@U.
  Proof.
    apply antisymmetry.
    - intros s Hs. cbn in *.
      dependent induction Hs.
      + exists pnil_ready, pnil_ready. firstorder eauto.
        constructor.
      + edestruct IHHs as (t1 & t2 & Ht1 & Ht2 & Ht3); eauto.
        cbn in H. destruct H as (s1 & s2 & Hs1 & Hs2 & Hs3).
        exploit @seq_comp_tstrat; eauto.
        intros (st1 & st2 & Hst1 & Hst2 & Hst3).
        exists st1, st2. split; eauto. split; eauto.
        eapply lens_seq_comp; eauto.
    - intros s Hs. cbn in *.
      edestruct Hs as (s1 & s2 & Hs1 & Hs2 & Hs3); eauto. clear Hs.
      revert s2 s Hs1 Hs3.
      (* Set Printing Implicit. cbn. *)
      generalize ((@lready U U lid tt)) as st.
      dependent induction Hs2; intros.
      + dependent destruction Hs1. eauto.
      + edestruct @tstrat_seq_comp as (xs1 & xs2 & st2 & fs1 & fs2 & HA & HB & HC & HD & HE); eauto.
        exploit IHHs2; eauto. intros Hc.
        eapply closure_has_cons; eauto.
        exists s, fs1. repeat apply conj; eauto. cbn in *.
        dependent destruction st. cbn in *. destruct p. eauto.
  Qed.

End CLOSURE_SCOMP.

(** ** Theorem 6.2 (The frame property for Clight)  *)

(** A handy way to built stateless refinement convention from the relation on
    questions and answers *)

Record esig_rel {E F: esig} : Type :=
  {
    match_query : op E -> op F -> Prop;
    match_reply (m1: op E) (m2: op F) : ar m1 -> ar m2 -> Prop;
  }.
Arguments esig_rel : clear implicits.

Section ESIG_REL_CONV.
  Obligation Tactic := cbn.
  Context {E F: esig} (R: esig_rel E F).

  Inductive esig_rel_conv_has : rcp E F -> Prop :=
  | esig_rel_conv_has_allow m1 m2 (HM: match_query R m1 m2):
    esig_rel_conv_has (rcp_allow m1 m2)
  | esig_rel_conv_has_forbid m1 m2 (HM: match_query R m1 m2)
      n1 n2 (HA: ~ match_reply R m1 m2 n1 n2):
    esig_rel_conv_has (rcp_forbid m1 m2 n1 n2)
  | esig_rel_conv_has_cont m1 m2 (HM: match_query R m1 m2)
      n1 n2 k (HK: match_reply R m1 m2 n1 n2 -> esig_rel_conv_has k):
    esig_rel_conv_has (rcp_cont m1 m2 n1 n2 k).
  Hint Constructors esig_rel_conv_has : core.

  Program Definition esig_rel_conv : conv E F :=
    {| Downset.has s := esig_rel_conv_has s |}.
  Next Obligation.
    intros x y H1. induction H1; intros Hx; try (xinv Hx; eauto).
    econstructor; eauto.
    intros. exfalso. eauto.
  Qed.

  Lemma esig_rel_mr_elim q1 q2:
    match_query R q1 q2 ->
    forall r1 r2, ~ esig_rel_conv_has (rcp_forbid q1 q2 r1 r2) ->
             match_reply R q1 q2 r1 r2.
  Proof.
    intros Hse Hq * Hr.
    apply NNPP. intros Hnr.
    apply Hr. econstructor; eauto 10.
  Qed.

  Lemma esig_rel_mr_intro q1 q2 r1 r2:
    match_reply R q1 q2 r1 r2 ->
    ~ esig_rel_conv_has (rcp_forbid q1 q2 r1 r2).
  Proof.
    intros Hr Hx. dependent destruction Hx; eauto.
  Qed.

End ESIG_REL_CONV.

Coercion esig_rel_conv : esig_rel >-> conv.

Global Instance esig_rel_conv_regular {E F} (R: esig_rel E F): RegularConv R.
Proof.
  split. intros * Hm Hn. apply antisymmetry.
  - intros x Hx. cbn in *.
    dependent destruction Hx.
    apply HK. eapply esig_rel_mr_elim in Hn; eauto.
  - intros x Hx. cbn in *.
    dependent destruction Hm.
    econstructor; eauto.
Qed.

Require Clight Join Memory ClightPComp Lifting Determ.

Section LIFT_CONVERT.

  Context (li: language_interface) (S: Type).

  Inductive lift_convert_mq: op (li @ S) -> op (Lifting.lifted_li S li) -> Prop :=
  | lift_convert_mq_intro q se (s: S):
    lift_convert_mq ((se, q)%embed, s) (se, Datatypes.pair q s)%embed.
  Inductive lift_convert_mr: forall (m1: op (li @ S)) (m2: op (Lifting.lifted_li S li)), ar m1 -> ar m2 -> Prop :=
  | lift_convert_mr_intro m1 m2 r s:
    lift_convert_mr m1 m2 (r, s) (r, s).

  Definition lift_convert_rel:
    esig_rel (li @ S) (Lifting.lifted_li S li) :=
      {| CompCertStrat.match_query := lift_convert_mq;
         CompCertStrat.match_reply := lift_convert_mr |}.

End LIFT_CONVERT.

Lemma rsq_lift_convert sk {li S} L:
  rsq (lift_convert_rel li S) (lift_convert_rel li S)
      ((lts_strat_sk sk L) @ S)
      (lts_strat_sk sk (Lifting.lifted_semantics S L)).
Proof.
  Ltac split_evar := instantiate (1 := (_, _)).
  setoid_rewrite <- closure_lift.
  apply rsq_closure; eauto with typeclass_instances.
  intros p (s & t & Hs & Ht & Hst). cbn in *.
  dependent destruction Ht. { xinv Hs. apply rsp_ready. constructor. }
  dependent destruction Hs. apply rsp_oq. { constructor. }
  intros qx Hq. xinv Hq. inv HM. rename q2 into d1.
  simple inversion Hst; try congruence. xsubst; congruence.
  clear Hst. xsubst. inv H2. inv H3. xsubst. intros Hst Hu.
  eapply rsp_ref. 1-3: reflexivity.
  { instantiate (1 := state_strat _ _ _ _ _).
    cbn. intros. econstructor; eauto.
    split. split_evar.
    instantiate (1 := u).
    all: cbn; eauto. } clear Hu.
  (* assert ((IntStrat.get slens_id (d1, tt)) = d1). reflexivity. *)
  (* setoid_rewrite H in Hst. clear H. *)
  clear HVF INIT. revert d1 u s2 s Hs Hst.
  dependent induction HS; intros.
  - dependent destruction Hs. eapply rsp_pq. { repeat constructor. }
    dependent destruction Hs. apply rsp_suspended.
    econstructor. split; cbn; eauto.
    xinv Hst. easy.
  - dependent destruction Hs. eapply rsp_pq. { repeat constructor. }
    dependent destruction Hs. apply rsp_oa.
    { econstructor. split; cbn; eauto. xinv Hst. easy. }
    cbn. intros [r xs] Hr. eapply esig_rel_mr_elim in Hr.
    2: { constructor. } inv Hr. xinv Hst.
    rewrite regular_conv.
    2: { repeat constructor. }
    2: { intros Hr. xinv Hr. apply HA. inv HM. constructor. }
    dependent destruction H1.
    eapply rsp_ref. 1-3: reflexivity.
    2: { eapply IHHS; eauto. }
    intros p Hp. cbn. econstructor 2.
    { split; eauto. }
    { split. split_evar. all: cbn; eauto. }
    apply Hp.
  - dependent destruction Hs. dependent destruction Hs.
    dependent destruction Hst.
    eapply rsp_pa.
    { intros Hr. xinv Hr. apply HA. constructor. }
    apply rsp_ready. cbn.
    econstructor 3. split; eauto.
  - eapply rsp_ref. 1-3: reflexivity.
    2: { eapply IHHS; eauto. }
    intros p Hp. econstructor 4. split_evar. 2: apply Hp.
    apply Lifting.lifting_step_star; eauto.
Qed.

Section FRAME.
  Import Clight Join Memory.Mem ClightPComp.
  Import -(notations) Lifting.

  Inductive join_query : query (lifted_li mem li_c) -> query li_c -> Prop :=
  | join_query_intro vf sg vargs m msrc mtgt
      (MJOIN: Join.join m msrc mtgt):
    join_query (cq vf sg vargs msrc, m) (cq vf sg vargs mtgt).

  Inductive join_reply: reply (lifted_li mem li_c) -> reply li_c -> Prop :=
  | join_reply_intro rv m msrc mtgt
      (MJOIN: Join.join m msrc mtgt):
    join_reply (cr rv msrc, m) (cr rv mtgt).

  Program Definition join_cc : callconv (lifted_li mem li_c) li_c :=
    {|
      ccworld := unit;
      match_senv _ se1 se2 := se1 = se2;
      LanguageInterface.match_query _ := join_query;
      LanguageInterface.match_reply _ := join_reply;
    |}.
  Next Obligation. reflexivity. Qed.
  Next Obligation. inv H0. reflexivity. Qed.
  Next Obligation. inv H. reflexivity. Qed.

  Context (p: program).
  Inductive join_ms : state * mem -> state -> Prop :=
  | clightp_ms_State:
    forall f s k e le mx m1 m2 (HJ: join mx m1 m2),
      join_ms (State f s k e le m1, mx) (State f s k e le m2)
  | join_ms_Callstate:
    forall vf args k mx m1 m2 (HJ: join mx m1 m2),
      join_ms (Callstate vf args k m1, mx) (Callstate vf args k m2)
  | join_ms_Returnstate:
    forall rv k mx m1 m2 (HJ: join mx m1 m2),
      join_ms (Returnstate rv k m1, mx) (Returnstate rv k m2).

  Lemma join_step ge mx:
    forall s1 t s1',
    Clight.step2 ge s1 t s1' ->
    forall s2, join_ms (s1, mx) s2 ->
    exists s2', Clight.step2 ge s2 t s2' /\
    join_ms (s1', mx) s2'.
  Proof with (eexists _; split; econstructor; eauto).
    induction 1; intros S1 HS; inv HS;
      try solve [ eexists _; split; econstructor; eauto ].
    - exploit clight_lvalue_join; eauto. intros A.
      exploit clight_expr_join; eauto. intros B.
      exploit sem_cast_join; eauto.
      rewrite H1. intros C. inv C.
      exploit assign_loc_join; eauto. intros (? & D & E)...
    - exploit clight_expr_join; eauto. intros A...
    - exploit clight_expr_join; eauto. intros A.
      exploit clight_exprlist_join; eauto; intros B...
    - exploit clight_exprlist_join; eauto. intros A.
      exploit ClightP.external_call_join; eauto. intros (? & B & C)...
    - exploit clight_expr_join; eauto. intros A.
      exploit bool_val_join; eauto.
      rewrite H0. intros B. inv B...
    - exploit free_list_join; eauto.
      rewrite H. intros A. inv A...
    - exploit clight_expr_join; eauto. intros A.
      exploit sem_cast_join; eauto.
      rewrite H0. intros B. inv B.
      exploit free_list_join; eauto.
      rewrite H1. intros C. inv C...
    - exploit free_list_join; eauto.
      rewrite H0. intros A. inv A...
    - exploit clight_expr_join; eauto. intros A...
    - exploit clight_function_entry_join; eauto. intros (? & A & B)...
    - exploit ClightP.external_call_join; eauto. intros (? & A & B)...
  Qed.

  Lemma frame_property :
    forward_simulation join_cc join_cc (lifted_semantics mem (semantics2 p)) (semantics2 p).
  Proof.
    constructor. econstructor. reflexivity. firstorder.
    instantiate (1 := fun _ _ _ => _). cbn beta.
    intros se1 se2 w Hse Hse1. cbn -[semantics2] in *. subst se2.
    rename w into mx.
    eapply forward_simulation_step with (match_states := join_ms).
    - intros [q1 mq] q2 [s1 ms] Hq Hi. cbn in *. eprod_crush.
      inv Hq. inv H.
      eexists. split; econstructor; eauto.
      apply mjoin_nextblock in MJOIN.
      rewrite MJOIN. unfold Ple in *.
      etransitivity; eauto.
      apply Pos.le_max_r.
    - intros [s1 ms1] s2 [r1 mr1] Hjoin Hf.
      inv Hf. cbn in *. subst. inv H. inv Hjoin.
      eexists. split; constructor; eauto.
    - intros [s1 ms1] s2 [q1 mq1] Hjoin He.
      inv He. cbn in *. subst. inv H. inv Hjoin.
      eexists tt, _. repeat apply conj; eauto.
      + econstructor; eauto.
      + constructor; eauto.
      + intros [r1 mr1] r2 [s1' ms1'] Hjoin Hr.
        eprod_crush. inv H. inv Hjoin.
        eexists. split; constructor; eauto.
    - intros [s1 ms1] t [s1' ms1'] [HS <-] s2 Hjoin.
      eapply join_step; eauto.
    - apply well_founded_ltof.
  Qed.

  Definition join_conv : conv (li_c @ mem) li_c :=
    lift_convert_rel li_c mem ;; join_cc.

  Import Determ.

  Lemma frame_property_ref_sk sk:
    Linking.linkorder (skel (semantics2 p)) sk ->
    rsq join_conv join_conv (lts_strat_sk sk (semantics2 p) @ mem) (lts_strat_sk sk (semantics2 p)).
  Proof.
    intros Hlink. unfold join_conv. eapply rsq_vcomp.
    3: apply rsq_lift_convert.
    apply lts_strat_determ. apply lifting_determinate. apply clight_determinate.
    apply lts_strat_determ. apply clight_determinate.
    apply fsim_rsq_sk. apply clight_determinate.
    apply frame_property. apply Hlink.
  Qed.

  Lemma frame_property_ref:
    rsq join_conv join_conv (lts_strat (semantics2 p) @ mem) (lts_strat (semantics2 p)).
  Proof.
    apply frame_property_ref_sk.
    apply Linking.linkorder_refl.
  Qed.

End FRAME.

(* --------------------------------------------------------------- *)
(** Some useful RegularConv instances *)

Global Instance conv_id_regular {E}: RegularConv (@vid E).
Proof.
  split. intros. apply Downset.has_eq_ext. cbn. firstorder.
  apply H2. apply NNPP. eauto.
Qed.

Global Instance rel_conv_regular {U V} (R: rel U V): RegularConv R.
Proof.
  split. intros * Hm Hn. apply antisymmetry.
  - intros x Hx. cbn in *.
    dependent destruction Hx.
    apply HK. apply NNPP. intros Hx. apply Hn.
    constructor; eauto.
  - intros x Hx. cbn in *.
    dependent destruction Hm.
    econstructor; eauto.
Qed.

Global Instance tconv_regular {E1 E2 F1 F2} R S (HR: RegularConv R) (HS: RegularConv S) :
  RegularConv (@tconv E1 E2 F1 F2 R S).
Proof.
  split. intros [ma1 mb1] [ma2 mb2] [na1 nb1] [na2 nb2] [Hm1 Hm2] Hn.
  cbn in Hn.
  apply not_and_or in Hn as [Hn | Hn]; try easy.
  apply not_and_or in Hn as [Hn | Hn]; try easy.
  apply not_or_and in Hn as [Hn1 Hn2].
  rewrite rcnext_tconv; cbn; eauto.
  rewrite !regular_conv; eauto.
Qed.

Lemma not_imply_or (P Q: Prop): (~ P -> Q) -> P \/ Q.
Proof. intros. destruct (classic P); firstorder. Qed.

Lemma or_commut (P Q: Prop): P \/ Q -> Q \/ P.
Proof. intros [H|H]; firstorder. Qed.

Global Instance vcomp_regular {E1 E2 E3} R S
  (HR: RegularConv R) (HS: RegularConv S):
  RegularConv (@vcomp E1 E2 E3 R S).
Proof.
  split. intros m1 m3 n1 n3 Hm Hn.
  apply antisymmetry.
  - intros c Hc. cbn in Hc.
    destruct Hc as (m2 & Hc). destruct Hc as (Hm12 & Hm23 & Hc).
    cbn in Hn.
    eapply not_ex_all_not with (n := m2) in Hn.
    apply not_and_or in Hn as [Hn | Hn]. easy.
    apply not_and_or in Hn as [Hn | Hn]. easy.
    apply not_all_ex_not in Hn as [n2 Hn].
    apply not_or_and in Hn as [Hn1 Hn2].
    specialize (Hc n2) as [Hc|[Hc|Hc]]; try easy.
    rewrite !regular_conv in Hc; eauto.
  - intros c Hc. cbn in *.
    destruct Hm as (m2 & Hm12 & Hm23). exists m2.
    repeat apply conj; eauto. intros n2.
    apply not_imply_or. intros Hn12.
    apply not_imply_or. intros Hn23.
    rewrite !regular_conv; eauto.
Qed.

(* --------------------------------------------------------------- *)
(** Some useful Monotonic instances *)

Global Instance fcomp_when_monotonic {E1 E2 F1 F2 i1 i2 i p}:
  Monotonic (@fcomp_when E1 E2 F1 F2 i1 i2 i p) (ref ++> ref ++> ref).
Proof.
  intros s1 s2 Hs t1 t2 Ht st (u1 & u2 & Hu1 & Hu2 & Hu). cbn in *.
  eexists _, _. repeat apply conj; eauto.
Qed.

Global Instance fcomp_params : Params (@fcomp_when) 2 := { }.

Global Instance compose_when_monotonic {E F G i j k p}:
  Monotonic (@compose_when E F G i j k p) (ref ++> ref ++> ref).
Proof.
  intros s1 s2 Hs t1 t2 Ht st (u1 & u2 & Hu1 & Hu2 & Hu). cbn in *.
  eexists _, _. repeat apply conj; eauto.
Qed.

Global Instance compose_params : Params (@compose_when) 2 := { }.
