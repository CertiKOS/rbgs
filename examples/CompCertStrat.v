Require Import Classical.
Require Import Program.Equality.
Require Import LogicalRelations.
Require Import Poset.
Require Import Lattice.
Require Import Downset.
Require Import IntStrat.
Require Import Classical_Prop.

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

Class RegularConv {E F} (R : conv E F) :=
  {
    regular_conv m1 m2 n1 n2:
    Downset.has R (rcp_allow m1 m2) ->
    ~ Downset.has R (rcp_forbid m1 m2 n1 n2) ->
    rcnext m1 m2 n1 n2 R = R;
  }.

Global Hint Constructors pref comp_has : core.

(** * Sequential composition *)

Section SEQ_COMP.

  Section DEF.

    Obligation Tactic := cbn.

    Context {E F: esig}.

    Inductive seq_comp_has: forall {i}, @play E F i -> @play E F ready -> @play E F i -> Prop :=
    | seq_comp_ready t:
      seq_comp_has pnil_ready t t
    | seq_comp_oq q s t w:
      seq_comp_has s t w ->
      seq_comp_has (oq q :: s) t (oq q :: w)
    | seq_comp_pq q m s t w:
      seq_comp_has s t w ->
      @seq_comp_has (running q) (pq m :: s) t (pq m :: w)
    | seq_comp_suspend q m t:
      seq_comp_has (pnil_suspended q m) t (pnil_suspended q m)
    | seq_comp_oa q m n s t w:
      seq_comp_has s t w ->
      @seq_comp_has (suspended q m) (oa n :: s) t (oa n :: w)
    | seq_comp_pa q r s t w:
      seq_comp_has s t w ->
      @seq_comp_has (running q) (pa r :: s) t (pa r :: w).

    Hint Constructors seq_comp_has.
    Hint Constructors pref.
    Hint Resolve (fun E F i => reflexivity (R := @pref E F i)).

    Lemma seq_comp_has_pref {i} (s: @play E F i) t w :
      seq_comp_has s t w ->
      forall w', w' [= w -> exists s' t', s' [= s /\ t' [= t /\ seq_comp_has s' t' w'.
    Proof.
      induction 1; cbn in *.
      - intros w' Hw'. xinv Hw'; eauto 10.
      - intros w' Hw'.
        dependent destruction w'; eauto. xinv Hw'.
        edestruct IHseq_comp_has as (s' & t' & Hs' & Ht' & Hw'); eauto 10.
      - intros w' Hw'.
        dependent destruction w'. xinv Hw'.
        edestruct IHseq_comp_has as (s' & t' & Hs' & Ht' & Hw'); eauto 10.
      - intros w' Hw'. xinv Hw'; eauto 10.
      - intros w' Hw'.
        dependent destruction w'; eauto. xinv Hw'.
        edestruct IHseq_comp_has as (s' & t' & Hs' & Ht' & Hw'); eauto 10.
      - intros w' Hw'.
        dependent destruction w'; eauto. xinv Hw'.
        edestruct IHseq_comp_has as (s' & t' & Hs' & Ht' & Hw'); eauto 10.
    Qed.

    Program Definition seq_compose {i} (σ : strat E F i) (τ : strat E F ready) : strat E F i :=
      {| Downset.has w :=
          exists s t, Downset.has σ s /\ Downset.has τ t /\ seq_comp_has s t w |}.
    Next Obligation.
      intros i σ τ x y Href (s & t & Hs & Ht & Hw).
      edestruct @seq_comp_has_pref as (s' & t' & Hs' & Ht' & Hw''); eauto.
      eauto 10 using Downset.closed.
    Qed.

    Lemma seq_comp_has_exists i (s1: @play E F i) s2:
      exists (s: @play E F i), seq_comp_has s1 s2 s.
    Proof.
      revert s2. dependent induction s1; intros s2. 1-2:eexists; eauto.
      edestruct IHs1 as (s & Hs).
      exists (m :: s). dependent destruction m; eauto.
    Qed.

    Lemma seq_comp_assoc {i} (s1: @play E F i) s2 s3 s12 s123:
      seq_comp_has s1 s2 s12 -> seq_comp_has s12 s3 s123 ->
      exists s23, seq_comp_has s1 s23 s123 /\ seq_comp_has s2 s3 s23.
    Proof.
      intros Ha Hb. revert s3 s123 Hb. dependent induction Ha; intros;
        try (dependent destruction Hb; edestruct IHHa as (s23 & A & B); eauto).
      - eexists _. split; eauto.
      - dependent destruction Hb.
        edestruct seq_comp_has_exists as (s23 & A).
        eexists. split; eauto.
    Qed.

  End DEF.

  Hint Constructors seq_comp_has : core.

  Lemma rsp_seq_comp {E1 E2 F1 F2} (R S: conv _ _)
    `{!RegularConv R} `{!RegularConv S}
    i1 j1 (pi: rspos i1 j1) (s: @play E1 F1 i1)
    (τ1: @strat E2 F2 j1) (τ2: @strat E2 F2 ready):
    (exists s1 s2, seq_comp_has s1 s2 s /\
      rsp R S pi s1 τ1 /\ rsp R S rs_ready s2 τ2) ->
    match pi with
    | rs_suspended q1 q2 m1 m2 =>
         Downset.has S (rcp_allow q1 q2) ->
         Downset.has R (rcp_allow m1 m2) ->
         rsp R S pi s (seq_compose τ1 τ2)
    | rs_running q1 q2 =>
        Downset.has S (rcp_allow q1 q2) ->
        rsp R S pi s (seq_compose τ1 τ2)
    | rs_ready => rsp R S pi s (seq_compose τ1 τ2)
    end.
  Proof.
    intros (s1 & s2 & Hs & Hs1 & Hs2).
    revert j1 pi τ1 τ2 Hs1 Hs2.
    dependent induction Hs.
    - intros. xinv Hs1.
      assert (Ht : τ2 [= seq_compose τ1 τ2).
      { intros k Hk. exists pnil_ready, k. eauto. }
      rewrite <- Ht. eauto.
    - intros. xinv Hs1. constructor.
      + xinv Hs2; cbn; eauto.
      + intros q2 Hq.
        assert (Ht: seq_compose (next (oq q2) τ1) τ2 [= next (oq q2) (seq_compose τ1 τ2)).
        { intros k (k1 & k2 & Hk1 & Hk2 & Hk3). cbn in *; eauto 10. }
        rewrite <- Ht.
        specialize (IHHs _ (rs_running q q2)); eauto.
    - intros. xinv Hs1. econstructor; eauto.
      assert (Ht: seq_compose (next (pq m2) τ1) τ2 [= next (pq m2) (seq_compose τ1 τ2)).
      { intros k (k1 & k2 & Hk1 & Hk2 & Hk3). cbn in *; eauto 10. }
      rewrite <- Ht.
      specialize (IHHs _ (rs_suspended q q2 m m2)). eauto.
    - intros. xinv Hs1. intros HS HR. eapply rsp_suspended.
      exists (pnil_suspended q2 m2), pnil_ready. repeat apply conj; eauto.
      xinv Hs2; eauto.
    - intros. xinv Hs1. intros HR. econstructor.
      + xinv Hs2; cbn; eauto.
      + intros n2 Hn.
        assert (Ht: seq_compose (next (oa n2) τ1) τ2 [= next (oa n2) (seq_compose τ1 τ2)).
        { intros k (k1 & k2 & Hk1 & Hk2 & Hk3). cbn in *; eauto 10. }
        rewrite <- Ht. specialize (H9 _ Hn).
        rewrite regular_conv in *; eauto.
        specialize (IHHs _ (rs_running q q2)); eauto.
    - intros. xinv Hs1. intros HS. econstructor; eauto.
      assert (Ht: seq_compose (next (pa r2) τ1) τ2 [= next (pa r2) (seq_compose τ1 τ2)).
      { intros k (k1 & k2 & Hk1 & Hk2 & Hk3). cbn in *; eauto 10. }
      rewrite <- Ht. rewrite regular_conv in *; eauto.
      specialize (IHHs _ rs_ready); eauto.
  Qed.

  Lemma rsq_seq_comp {E1 E2 F1 F2} (R S: conv _ _)
    `{!RegularConv R} `{!RegularConv S}
    i j p (σ1: @strat E1 F1 i) σ2 (τ1: @strat E2 F2 j) τ2:
    rsq R S p σ1 τ1 ->
    rsq R S rs_ready σ2 τ2 ->
    rsq R S p (seq_compose σ1 σ2) (seq_compose τ1 τ2).
  Proof.
  Abort.

End SEQ_COMP.

Global Hint Constructors seq_comp_has : core.

(** * Clousure operator *)

Section CLOSURE.

  Obligation Tactic := cbn.

  Context {E F: esig}.

  Inductive closure_has: @strat E F ready -> play ready -> Prop :=
  | closure_has_nil σ: closure_has σ pnil_ready
  | closure_has_cons σ s t w:
    Downset.has σ s -> closure_has σ t -> seq_comp_has s t w ->
    closure_has σ w.

  Hint Constructors closure_has.

  Program Definition closure (σ : strat E F ready) : strat E F ready :=
    {| Downset.has w := closure_has σ w |}.
  Next Obligation.
    intros σ x y H1 H2. revert x H1. induction H2.
    - intros. xinv H1; eauto.
    - intros x Hx.
      edestruct @seq_comp_has_pref as (s' & t' & Hs' & Ht' & Hw''); eauto.
      specialize (IHclosure_has _ Ht').
      eauto 10 using Downset.closed.
  Qed.

  Lemma closure_unfold (σ: strat E F ready):
    seq_compose σ (closure σ) [= closure σ .
  Proof.
    intros w Hw. cbn in *.
    destruct Hw as (s & t & Hs & Ht & Hw).
    econstructor; eauto.
  Qed.

  Lemma closure_seq_comp (σ: strat E F ready) s t w:
    closure_has σ s -> closure_has σ t -> seq_comp_has s t w ->
    closure_has σ w.
  Proof.
    intros Hs Ht Hw. revert t w Ht Hw. dependent induction Hs.
    - intros. dependent destruction Hw; eauto.
    - intros. edestruct @seq_comp_assoc as (x & A & B).
      apply H0. apply Hw. eauto.
  Qed.

End CLOSURE.

Global Hint Constructors closure_has : core.

Lemma rsq_closure {E1 E2 F1 F2} (R S: conv _ _)
  `{!RegularConv R} `{!RegularConv S}
  (σ: @strat E1 F1 ready) (τ: @strat E2 F2 ready):
  rsq R S rs_ready σ τ ->
  rsq R S rs_ready (closure σ) (closure τ).
Proof.
  intros Hr. cbn. intros s Hs. cbn in Hs.
  revert τ Hr.
  dependent induction Hs.
  - intros. repeat constructor.
  - intros. specialize (IHHs _ Hr).
    unfold rsq in Hr. specialize (Hr _ H).
    rewrite <- closure_unfold.
    eapply rsp_seq_comp with (pi := rs_ready); eauto.
Qed.

(** * §6.1 Embedding CompCertO Semantics *)

From compcert Require Import LanguageInterface Smallstep Globalenvs.

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

Canonical Structure li_sig li: esig :=
  {|
    op := (Genv.symtbl * query li)%embed;
    ar _ := reply li;
  |}.
Coercion li_sig: language_interface >-> esig.

Section CONV.
  Local Open Scope embed.
  Obligation Tactic := cbn.

  Context {liA liB: language_interface} (cc: callconv liA liB).

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

Coercion cc_conv: callconv >-> poset_carrier.

Require Import Coqlib.
Close Scope list_scope.

Inductive non_recur_play {E F}: forall {i}, @play E F i -> Prop :=
| non_recur_play_nil: non_recur_play pnil_ready
| non_recur_play_suspended q m: non_recur_play (pnil_suspended q m)
| non_recur_play_pa q (r: ar q): non_recur_play (pa r :: pnil_ready)
| non_recur_play_oa q m (r: ar m) (s: play (running q)):
  non_recur_play s -> non_recur_play (oa r :: s)
| non_recur_play_oq q s: non_recur_play s -> non_recur_play (oq q :: s)
| non_recur_play_pq q m (s: play (suspended q m)):
  non_recur_play s -> non_recur_play (pq m :: s).

Class NonRecur {E F p} (σ: @strat E F p): Prop :=
  { non_recur: forall s, Downset.has σ s -> non_recur_play s; }.

Section LTS.
  Local Open Scope embed.
  Obligation Tactic := cbn.

  Context {liA liB: language_interface} (L: semantics liA liB).

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

  Inductive lts_strat_has: forall {i}, @play liA liB i -> Prop :=
  | lts_strat_has_nil: @lts_strat_has ready pnil_ready
  | lts_strat_has_intro se q s k
    (HVF: Genv.valid_for (skel L) se)
    (INIT: initial_state (L se) q s)
    (HS: state_strat_has se q s k):
    @lts_strat_has ready (@oq liA liB (se, q) :: k).

  Program Definition lts_strat' i: strat liA liB i :=
    {| Downset.has w := @lts_strat_has i w |}.
  Next Obligation.
    intros. xinv H0.
    - xinv H. constructor.
    - simple inversion H; try discriminate.
      + xsubst. constructor.
      + intros. subst. xsubst. xinv H3.
        econstructor; eauto.
        eapply state_strat_obligation_1; eauto.
  Qed.

  Program Definition lts_strat: strat liA liB ready :=
    closure (lts_strat' ready).

  Instance lts_strat_nonrecur i: NonRecur (lts_strat' i).
  Proof.
    split. intros s Hs. cbn in Hs. dependent destruction Hs.
    { constructor. }
    constructor. clear HVF INIT. dependent induction HS.
    - constructor; eauto. constructor.
    - repeat constructor. apply IHHS; eauto.
    - constructor.
    - apply IHHS; eauto.
  Qed.

End LTS.

Coercion lts_strat: semantics >-> poset_carrier.

(** * Deterministic *)

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

  Instance lts_strat_determ' i: Deterministic (lts_strat' L i).
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
                eapply state_strat_has_internal; eauto.
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
    non_recur_play s1 -> non_recur_play t1 ->
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
    eapply seq_comp_pcoh; eauto. apply non_recur; eauto. apply non_recur; eauto.
  Qed.

  Instance lts_strat_determ: Deterministic L.
  Proof.
    apply closure_determ. typeclasses eauto. apply lts_strat_nonrecur.
  Qed.

End DETERM.

Section FSIM.
  Local Open Scope embed_scope.

  Context {liA1 liA2 liB1 liB2: language_interface}
    (ccA: callconv liA1 liA2) (ccB: callconv liB1 liB2)
    (L1: semantics liA1 liB1) (L2: semantics liA2 liB2) (DL2: determinate L2)
    (FSIM: forward_simulation ccA ccB L1 L2).

  Hint Constructors state_strat_has lts_strat_has.

  Lemma fsim_rsq: rsq ccA ccB rs_ready L1 L2.
  Proof.
    apply rsq_closure; try apply cc_regular.
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
    specialize (fsim_lts _ _ _ HSE HVF).
    rename s into s1. rename se into se1.
    edestruct (@fsim_match_initial_states) as (i & s2 & A & B); eauto.
    assert (Hs: state_strat L2 se2 q2 s2 (running (se2, q2))
                  [= (next (oq (se2, q2)) (lts_strat' L2 ready))).
    { intros p Hp. cbn in *. econstructor; eauto.
      eapply match_senv_valid_for in HSE. apply HSE.
      rewrite <- fsim_skel. eauto. }
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

End FSIM.

Section REGULAR.

  Inductive play_suspended {E F}: forall i, @play E F i -> Prop :=
  | play_suspended_nil q m: play_suspended (suspended q m) (pnil_suspended q m)
  | play_suspended_cons i j (m: move j i) s:
    play_suspended i s -> play_suspended j (m :: s).

  Arguments play_suspended {E F i}.

  Class Regular {E F} (σ: strat E F ready) :=
    { regular: forall s s1 s2, Downset.has σ s -> seq_comp_has s1 s2 s ->
               Downset.has σ s1 /\ (~ play_suspended s1 -> Downset.has σ s2);
      infinite: forall s1 s2 s, Downset.has σ s1 -> Downset.has σ s2 ->
                seq_comp_has s1 s2 s -> Downset.has σ s;
      non_empty: exists s, Downset.has σ s;
    }.

  Hint Constructors play_suspended.

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

  Lemma pref_or {E F i} (s t: @play E F i) w:
    s [= w -> t [= w -> s [= t \/ t [= s.
  Proof.
    intros H1. revert t. induction H1; intros; cbn; eauto.
    cbn in *. dependent destruction H; eauto.
    specialize (IHpref _ H) as [A | A]; eauto.
  Qed.

  Lemma lts_strat_one_shot {liA liB} (L: semantics liA liB) (s: @play liA liB ready) s1 s2:
    Downset.has (lts_strat' L ready) s -> seq_comp_has s1 s2 s -> ~ play_suspended s1 ->
    s1 = pnil_ready \/ s2 = pnil_ready.
  Proof.
    intros HL HS HP. cbn in HL. dependent destruction HL.
    { dependent destruction HS. left. easy. }
    dependent destruction HS0. { left. easy. }
    right. apply play_suspended_cons_contrapos in HP.
    clear HVF INIT. revert s s2 HS0 HP.
    dependent induction HS.
    - intros. dependent destruction HS0.
      apply play_suspended_cons_contrapos in HP.
      dependent destruction HS0.
      exfalso. apply HP. constructor.
    - specialize (IHHS k0 eq_refl JMeq_refl).
      intros. dependent destruction HS0. dependent destruction HS0.
      apply play_suspended_cons_contrapos in HP.
      apply play_suspended_cons_contrapos in HP.
      eauto.
    - intros. dependent destruction HS0.
      dependent destruction HS0. reflexivity.
    - eauto.
  Qed.

  Instance lts_regular {liA liB} (L: semantics liA liB):
    Regular L.
  Proof.
    split.
    - intros * HL Hs. cbn in *.
      destruct (classic (play_suspended s1)) as [Hp | Hp].
      + split.
        * apply seq_comp_has_incr in Hs.
          eapply closure_obligation_1; eauto.
        * easy.
      + revert s1 s2 Hs Hp. dependent induction HL.
        { intros; xinv Hs. split; intros; apply closure_has_nil. }
        specialize (IHHL liA liB L t eq_refl eq_refl JMeq_refl JMeq_refl).
        intros * Hs Hp. rename s0 into t1. rename t into t2.
        edestruct (pref_or t1 s1) as [Hq | Hq].
        { eapply seq_comp_has_incr; eauto. }
        { eapply seq_comp_has_incr; eauto. }
        * assert (exists w1, seq_comp_has t1 w1 s1 /\ seq_comp_has w1 s2 t2)
            as (w1 & Hw1 & Hw2).
          { eapply seq_comp_split2; eauto. }
          assert (HW: ~ play_suspended w1).
          { intros Hx. apply Hp. eapply seq_comp_has_suspended2; eauto. }
          specialize (IHHL _ _ Hw2 HW) as (IH1 & IH2).
          split; eauto.
        * edestruct @seq_comp_split1 as (w1 & Hw1 & Hw2).
          3: eauto. 1-3: eauto.
          exploit @lts_strat_one_shot; eauto.
          intros [ -> | -> ].
          -- split.
             ++ apply closure_has_nil.
             ++ intros. dependent destruction Hs.
                dependent destruction Hw1. eauto.
          -- dependent destruction Hw2. split.
             ++ apply seq_comp_has_nil1 in Hw1. subst.
                eapply closure_has_cons. apply H.
                apply closure_has_nil.
                apply seq_comp_has_nil2. reflexivity.
             ++ intros. apply HL.
    - intros. cbn. eapply closure_seq_comp. 3: eauto. 1-2: eauto.
    - eexists (pnil_ready); eauto. constructor.
  Qed.

End REGULAR.

Require Import CategoricalComp.

Section CC_COMP.

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

  Arguments play_suspended {E F i}.
  Hint Constructors play_suspended.

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

  (* s* ∘ t ⊑ (s ∘ t)* *)
  Lemma closure_comp_ref {E F G} (σ: strat F G ready) (τ: strat E F ready)
    (Hτ: Regular τ):
    compose cpos_ready (closure σ) τ [= closure (compose cpos_ready σ τ).
  Proof.
    intros ? (s & t & Hs & Ht & Hst). cbn in *.
    revert t c Hst Ht. dependent induction Hs.
    { intros. dependent destruction Hst. constructor. }
    rename s into s1. rename t into s2. rename w into s.
    intros. edestruct @decompose_comp as
      (t1 & t2 & w1 & w2 & A & B & C & D & P); eauto.
    specialize (IHHs _ _ B).
    destruct (classic (play_suspended t1)) as [Hp | Hp].
    - specialize (P Hp).
      eapply closure_has_cons with (s := c) (t := pnil_ready).
      + exists s1, t1. repeat apply conj.
        * apply H.
        * destruct Hτ. edestruct regular0 as (R1 & R2); eauto.
        * exploit @seq_comp_has_suspended1. apply D. apply P. congruence.
      + apply closure_has_nil.
      + apply seq_comp_has_nil2; eauto.
    - eapply closure_has_cons. 3: eauto.
      + cbn. exists s1, t1. repeat apply conj; eauto.
        edestruct Hτ; eauto. exploit regular0. apply Ht. eauto. easy.
      + eapply IHHs. eauto.  edestruct Hτ; eauto.
        exploit regular0. apply Ht. eauto.
        intros [? HX]. eauto.
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

  (* This is used by the bq example, see below *)
  Lemma closure_comp_ref2 {E F G} (σ: strat F G ready) (τ: strat E F ready)
    (Hτ: Regular τ):
    closure (compose cpos_ready σ τ) [= compose cpos_ready (closure σ) τ.
  Proof.
    intros ? H. cbn in *. dependent induction H.
    { exists pnil_ready, pnil_ready. repeat apply conj; eauto.
      destruct Hτ. destruct non_empty0 as (s & Hs).
      eapply Downset.closed; eauto. constructor. }
    destruct H as (s1 & s2 & Hs1 & Hs2 & Hst1).
    edestruct IHclosure_has as (t1 & t2 & Ht1 & Ht2 & Hst2); eauto.
    edestruct @decompose_seq_comp as (si & t1_head & t1_trail & ti & A & B & C & D); eauto.
    exists si, ti. repeat apply conj; eauto.
    destruct Hτ. edestruct regular0 as (R1 & R2). 2: apply B. eauto.
    eapply infinite0. 3: eauto. 1-2: eauto.
  Qed.

  Context {liA liB liC} (L1: semantics liB liC) (L2: semantics liA liB).

  Lemma cc_comp_ref_once sk:
    compose cpos_ready (lts_strat' L1 ready) L2 [= lts_strat' (comp_semantics' L1 L2 sk) ready.
  Proof.
    intros ? (s & t & Hs & Ht & Hst). cbn in *.
    dependent destruction Hs.
    { dependent destruction Hst. constructor. }
    dependent destruction Hst.
    eapply lts_strat_has_intro with (s := st1 L1 L2 s0).
    { admit. }
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
  Admitted.

  Global Instance closure_ref:
    Monotonic (@closure) (forallr -, forallr -, ref ++> ref).
  Proof.
    intros E F x y H s Hs.
    cbn in *. revert y H. dependent induction Hs.
    - constructor.
    - intros. eauto.
  Qed.

  Lemma cc_comp_ref sk:
    compose cpos_ready L1 L2 [= comp_semantics' L1 L2 sk.
  Proof.
    unfold lts_strat.
    rewrite <- cc_comp_ref_once.
    apply closure_comp_ref.
    apply lts_regular.
  Qed.

End CC_COMP.

(* XXX: move to IntStrat.v *)
Section RSVCOMP.
  Context {E1 F1 E2 F2 E3 F3 : esig}.
  Lemma rsq_vcomp {p1 p2 p3 p12 p23 p13} (p : rsvpos p12 p23 p13) :
    forall (R : conv E1 E2) (R' : conv E2 E3) (S : conv F1 F2) (S' : conv F2 F3)
           (σ1 : strat E1 F1 p1) (σ2 : strat E2 F2 p2) (σ3 : strat E3 F3 p3)
           `{Hσ2 : !Deterministic σ2} `{Hσ3 : !Deterministic σ3},
      rsq R S p12 σ1 σ2 ->
      rsq R' S' p23 σ2 σ3 ->
      rsq (vcomp R R') (vcomp S S') p13 σ1 σ3.
  Proof.
  Admitted.
End RSVCOMP.

(* XXX: move to IntStrat.v *)
Section REL.
  Obligation Tactic := cbn.
  Context (U V: Type) (R: rel U V).

  Canonical glob.
  Inductive rel_conv_has : rcp (glob U) (glob V) -> Prop :=
  | rel_conv_has_allow uq vq (HQ: R uq vq):
    rel_conv_has (rcp_allow uq vq)
  | rel_conv_has_forbid uq vq (HQ: R uq vq) ua va (HA: ~ R ua va):
    rel_conv_has (rcp_forbid uq vq ua va)
  | rel_conv_has_cont uq vq (HQ: R uq vq) ua va k (HK: R ua va -> rel_conv_has k):
    rel_conv_has (rcp_cont uq vq ua va k).
  Hint Constructors rel_conv_has.

  Program Definition rel_conv : conv (glob U) (glob V) :=
    {| Downset.has s := rel_conv_has s |}.
  Next Obligation.
    intros x y H1. induction H1; intros Hx; try (xinv Hx; eauto).
    econstructor; eauto.
    intros. exfalso. eauto.
  Qed.
End REL.

Coercion rel_conv : rel >-> poset_carrier.

(* XXX: move to IntStrat.v *)
Section CONV_ID.
  Obligation Tactic := cbn.
  Context {E: esig}.

  Inductive conv_id_has : rcp E E -> Prop :=
  | conv_id_allow m: conv_id_has (rcp_allow m m)
  | conv_id_forbid m n1 n2: n1 <> n2 -> conv_id_has (rcp_forbid m m n1 n2)
  | conv_id_cont m n1 n2 k
      (HK: n1 = n2 -> conv_id_has k): conv_id_has (rcp_cont m m n1 n2 k).
  Hint Constructors conv_id_has.

  Program Definition conv_id : conv E E :=
    {|
      Downset.has s := conv_id_has s;
    |}.
  Next Obligation.
    intros x y H1. induction H1; intros Hx; try (xinv Hx; eauto).
    econstructor; eauto.
    intros. exfalso. eauto.
  Qed.

End CONV_ID.

(* XXX: move to IntStrat.v *)
Record esig_rel {E F: esig} : Type :=
  {
    match_query : op E -> op F -> Prop;
    match_reply (m1: op E) (m2: op F) : ar m1 -> ar m2 -> Prop;
  }.
Arguments esig_rel : clear implicits.

(* XXX: move to IntStrat.v *)
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

Coercion esig_rel_conv : esig_rel >-> poset_carrier.

(* XXX: move to IntStrat.v *)
Section LENS_ID.

  Program Definition lens_id {U} : lens U U :=
    {|
      IntStrat.get := fun u => u;
      IntStrat.set := fun v u => u;
    |}.

  Program Definition embed_lens {U V} (l: @lens U V) : slens V U :=
    {|
      slens_lens :=
        {|
          IntStrat.get := fun '(u, tt) => l.(IntStrat.get) u;
          IntStrat.set := fun '(u, tt) v => (l.(IntStrat.set) u v, tt);
        |};
      slens_state := unit;
      slens_init := tt;
    |}.
  Next Obligation. destruct u0. apply get_set. Qed.
  Next Obligation. destruct u0. rewrite set_get. easy. Qed.
  Next Obligation. destruct u0. rewrite set_set. easy. Qed.

  Definition slens_id {U} : slens U U := embed_lens lens_id.

End LENS_ID.

Coercion sls : slens >-> poset_carrier.

Definition empty_sig : esig :=
  {|
    op := Empty_set;
    ar op := match op with end;
  |}.

Declare Scope esig_scope.
Delimit Scope esig_scope with esig.
Notation "E @ S" := (tens E (glob S)) : esig_scope.
Notation "0" := (empty_sig) : esig_scope.
Bind Scope esig_scope with esig.

Declare Scope strat_scope.
Delimit Scope strat_scope with strat.
Notation "σ @ S" := (tstrat tp_ready σ (@slens_id S)) : strat_scope.
Bind Scope strat_scope with strat.

Program Definition E0_conv {E} : conv 0 E := {| Downset.has s := False |}.

Lemma E0_conv_vcomp {E F} (R: conv E F): E0_conv = vcomp E0_conv R.
Proof.
  apply antisymmetry.
  - intros x Hx. xinv Hx.
  - intros x Hx. cbn in *. destruct x; xinv Hx; easy.
Qed.

Lemma rcp_cont_inv {E1 E2} m1 m2 n1 n2 k q1 q2 r1 r2 c:
  @rcp_cont E1 E2 m1 m2 n1 n2 k = @rcp_cont E1 E2 q1 q2 r1 r2 c ->
  m1 = q1 /\ m2 = q2 /\
    existT (fun m1 : E1 => ar m1) m1 n1 = existT (fun m1 : E1 => ar m1) q1 r1 /\
    existT (fun m2 : E2 => ar m2) m2 n2 = existT (fun m2 : E2 => ar m2) q2 r2 /\
    k = c.
Proof. intros H. inversion H. firstorder eauto. Qed.

Lemma rcp_forbid_inv {E1 E2} m1 m2 n1 n2 q1 q2 r1 r2:
  @rcp_forbid E1 E2 m1 m2 n1 n2 = @rcp_forbid E1 E2 q1 q2 r1 r2 ->
  m1 = q1 /\ m2 = q2 /\
    existT (fun m1 : E1 => ar m1) m1 n1 = existT (fun m1 : E1 => ar m1) q1 r1 /\
    existT (fun m2 : E2 => ar m2) m2 n2 = existT (fun m2 : E2 => ar m2) q2 r2.
Proof. intros H. inversion H. firstorder eauto. Qed.

(* XXX: move to IntStrat.v *)
Section ENCAP.
  Obligation Tactic := cbn.
  Context {U: Type} (u0 : U).

  Inductive e_has {E: esig} : forall {i}, U -> @play (E@U) E i -> Prop :=
  | e_has_ready u: e_has u pnil_ready
  | e_has_q u m s:
    e_has u s -> e_has u (oq m :: pq (m, u) :: s)
  | e_has_suspended u m:
    e_has u (@pnil_suspended (E@U) E m (m, u))
  | e_has_a m u n u' s:
    e_has u' s -> e_has u (@oa _ _ m (m, u) (n, u') :: pa n :: s).
  Hint Constructors e_has : core.
  Lemma e_has_ref {E i} (x y: @play (E@U) E i):
    pref x y -> e_has u0 y -> e_has u0 x.
  Proof.
    intros Href Hy. revert Href.
    dependent induction Hy; intros; eauto.
    - dependent destruction Href. eauto.
    - dependent destruction Href. eauto.
      dependent destruction Href.
      constructor. eapply IHHy. eauto.
    - dependent destruction Href. eauto.
    - dependent destruction Href. eauto.
      dependent destruction Href.
      constructor. eapply IHHy. eauto.
  Qed.
  (* Ideally, we would define the encap primitive as [e: U → 1] and use it as
     [E@e : E@U → E] but then we have to handle the isomorphism between 1 × E and E
     all the time. *)
  Program Definition e {E:esig} : strat (E@U) E ready :=
    {| Downset.has s := e_has u0 s |}.
  Next Obligation. intros. eapply e_has_ref; eauto. Qed.
  Definition encap {E F} (σ: strat E (F@U) ready) : strat E F ready :=
    compose cpos_ready e σ.

  Inductive de_has {E: esig} : U -> rcp E (E@U) -> Prop :=
  | de_has_allow u m: de_has u (rcp_allow m (m, u))
  | de_has_forbid u m n1 n2 u':
    n1 <> n2 -> de_has u (rcp_forbid m (m, u) n1 (n2, u'))
  | de_has_cont u m u' n1 n2 k
    (HK: n1 = n2 -> de_has u' k):
    de_has u (rcp_cont m (m, u) n1 (n2, u') k).
  Hint Constructors de_has : core.
  Program Definition de {E:esig} : conv E (E@U) :=
    {| Downset.has s := de_has u0 s |}.
  Next Obligation.
      intros E x y H1. revert u0; induction H1; intros u0 Hx; try solve [ dependent destruction Hx; eauto ].
      - simple inversion Hx; try congruence. subst.
        apply rcp_cont_inv in H0 as (A & B & C & D & K).
        subst. xsubst. intros HX.
        constructor. eauto.
      - simple inversion Hx; try congruence. subst.
        apply rcp_forbid_inv in H1 as (A & B & C & D).
        subst. xsubst. intros. constructor. easy.
      - simple inversion Hx; try congruence.
  Qed.
  Definition deencap {E F} (R: conv E F) : conv E (F@U) :=
    vcomp R de.

End ENCAP.

(* The encapsulated strategy is refined by the original strategy using the
   "deencap" refinement convention.

   This should follow from the conjoint property.
   XXX: move to IntStrat.v *)
Lemma deencap_rsq {E F: esig} {S: Type} (σ: strat E (F@S) ready) (s0: S):
  rsq conv_id (deencap s0 conv_id) rs_ready (encap s0 σ) σ.
Proof.
Admitted.

(* E@[s0> ⊙ σ@S ⊑ σ ⊙ E@[s0>
   XXX: move to IntStrat.v *)
Lemma encap_lift {E F} {S: Type} (σ: strat E F ready) (s0: S):
  compose cpos_ready (e s0) (σ @ S)%strat [= compose cpos_ready σ (e s0).
Admitted.

(* R s0 t0 → E@[s0> ⊑_{E@R → 1} E@[t0>
   XXX: move to IntStrat.v *)
Lemma representation_independence {E} {S T: Type} (R: rel S T) s0 t0:
  R s0 t0 -> rsq (tconv (@conv_id E) R) conv_id rs_ready (e s0) (e t0).
Proof.
Admitted.

Lemma closure_lift {E F U} (σ: strat E F ready):
  closure (σ@U)%strat [= ((closure σ)@U)%strat.
Proof.
  intros s Hs. cbn in *. dependent induction Hs.
  - exists pnil_ready, pnil_ready. firstorder eauto. constructor. constructor.
  - edestruct IHHs as (t1 & t2 & Ht1 & Ht2 & Ht3); eauto.
    cbn in H. destruct H as (s1 & s2 & Hs1 & Hs2 & Hs3).
Admitted.

(* XXX: move to IntStrat.v *)
Global Instance compose_monotonic {E F G i j k p}:
  Monotonic (@compose E F G i j k p) (ref ++> ref ++> ref).
Admitted.

(* XXX: move to IntStrat.v *)
Lemma compose_assoc {E F G H i j k ij jk ijk}
  (σ: strat G H i) (τ: strat F G j) (υ: strat E F k)
  (p1: cpos i j ij) (p2: cpos ij k ijk) (p3: cpos j k jk) (p4: cpos i jk ijk):
  compose p2 (compose p1 σ τ) υ = compose p4 σ (compose p3 τ υ).
Admitted.

Lemma vcomp_assoc {E F G H} (σ: conv E F) (τ: conv F G) (υ: conv G H):
  vcomp (vcomp σ τ) υ = vcomp σ (vcomp τ υ).
Admitted.

Lemma vcomp_left_id {E F} (σ: conv E F):
  vcomp conv_id σ = σ.
Admitted.

Lemma vcomp_right_id {E F} (σ: conv E F):
  vcomp σ conv_id = σ.
Admitted.

(* XXX: move to IntStrat.v *)
Lemma rsq_id_conv {E F i} p (σ τ: strat E F i):
  rsq conv_id conv_id p σ τ <-> σ [= τ.
Admitted.

Lemma rsq_id_strat {E F} p (R S: conv E F):
  rsq S R p id id <-> R [= S.
Admitted.

Global Instance compose_params : Params (@compose) 2 := { }.

Lemma tstrat_sup_l {I} {E1 E2 F1 F2 i1 i2 i} (p: tpos i1 i2 i)
  (σ: I -> strat E1 F1 i1) (τ: strat E2 F2 i2) :
  tstrat p (sup i:I, σ i) τ = sup i:I, tstrat p (σ i) τ.
Proof.
  apply antisymmetry.
  - intros x Hx. destruct Hx as (s & t & Hst & (a & Hs) & Ht).
    exists a. exists s, t. firstorder eauto.
  - intros x Hx. destruct Hx as (a & (s & t & Hs & Ht & Hst)).
    exists s, t. firstorder eauto.
Qed.

Lemma compose_sup_l {I} {E F G i j k} (p: cpos i j k)
  (σ: I -> strat F G i) (τ: strat E F j) :
  compose p (sup i:I, σ i) τ = sup i:I, compose p (σ i) τ.
Proof.
  apply antisymmetry.
  - intros x Hx. destruct Hx as (s & t & (a & Hs) & Ht & Hst).
    exists a. exists s, t. firstorder eauto.
  - intros x Hx. destruct Hx as (a & (s & t & Hs & Ht & Hst)).
    exists s, t. firstorder eauto.
Qed.

Lemma rsp_sup_exist {I} {E1 E2 F1 F2 i1 i2} p R S s τ:
  (exists i, @rsp E1 E2 F1 F2 R S i1 i2 p s (τ i)) -> rsp R S p s (sup i:I, τ i).
Proof. intros (i & Hi). rewrite <- sup_ub. apply Hi. Qed.

Global Instance vcomp_ref {E1 E2 E3 : esig}:
  Monotonic (@vcomp E1 E2 E3) (ref ++> ref ++> ref).
Proof.
  intros x y Hxy u v Huv. cbn. intros.
  eapply vcomp_has_ref; eauto. reflexivity.
Qed.

Global Instance vcomp_params : Params (@vcomp) 2 := { }.

(** * Example *)

Ltac eprod_crush :=
  repeat
    (match goal with
     | [ H: ?a * ?b |- _ ] => destruct H;cbn [fst snd] in *; subst
     | [ H: (?a * ?b)%embed |- _ ] => destruct H;cbn [fst snd] in *; subst
     | [ H: (?a, ?b) = (?c, ?d) |- _ ] => inv H
     | [ H: (?x * ?y)%rel _ _ |- _] => destruct H; cbn [fst snd] in *; subst
     | [ H: ?x /\ ?y |- _] => destruct H
     | [ H: (exists _, _) |- _] => destruct H
     | [ H: unit |- _] => destruct H
     end).

From compcert.clightp Require Import Example.
Import Memory Values Integers ListNotations.

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
      {| match_query := lift_convert_mq;
         match_reply := lift_convert_mr; |}.

End LIFT_CONVERT.

Definition join_conv : conv (li_c @ Mem.mem) li_c :=
  vcomp (lift_convert_rel li_c Mem.mem) join_cc.

(** * Strategy-level definitions *)

Definition val := Values.val.
Definition N := Example.N.

Inductive bq_op := enq: val -> bq_op | deq: bq_op.
Canonical Structure E_bq : esig :=
  {|
    op := bq_op;
    ar op := match op with | enq _ => unit | deq => val end;
  |}.
Inductive rb_op :=
| set : nat -> val -> rb_op | get : nat -> rb_op
| inc1 : rb_op | inc2 : rb_op.
Canonical Structure E_rb : esig :=
  {|
    op := rb_op;
    ar op :=
      match op with
      | set _ _ => unit | get _ => val | inc1 | inc2 => nat
      end;
  |}.

Definition M_enq_play (v: val) (i: nat): @play E_rb E_bq ready :=
  oq (enq v) ::
  pq inc2 ::
  @oa _ _ _ inc2 i ::
  pq (set i v) ::
  @oa _ _ _ (set i v) tt ::
  @pa _ _ (enq v) tt :: pnil_ready.
Definition M_deq_play (v: val) (i: nat): @play E_rb E_bq ready :=
  oq deq ::
  pq inc1 ::
  @oa _ _ _ inc1 i ::
  pq (get i) ::
  @oa _ _ _ (get i) v ::
  @pa _ _ deq v :: pnil_ready.
Definition M_enq_strat: strat E_rb E_bq ready := sup v, sup i, down (M_enq_play v i).
Definition M_deq_strat: strat E_rb E_bq ready := sup v, sup i, down (M_deq_play v i).
Definition M_bq : strat E_rb E_bq ready := closure (join M_enq_strat M_deq_strat).

Definition S_bq : Type := bq_state.
Definition S_rb : Type := rb_state.
Definition bq_rb_rel : rel S_bq S_rb := rb_bq.

Definition L_enq_play (v: val) (q: S_bq): @play 0 (E_bq @ S_bq) ready :=
  oq (enq v, q) :: @pa _ _ (enq v, q) (tt, app q (cons v nil)) :: pnil_ready.
Definition L_deq_play (v: val) (q: S_bq): @play 0 (E_bq @ S_bq) ready :=
  oq (deq, cons v q) :: @pa _ _ (deq, cons v q) (v, q) :: pnil_ready.
Definition L_enq_strat: strat 0 (E_bq @ S_bq) ready :=
  sup {v | Cop.val_casted v tint}, sup {q | (List.length q < N)%nat}, down (L_enq_play v q).
Definition L_deq_strat: strat 0 (E_bq @ S_bq) ready := sup v, sup q, down (L_deq_play v q).
Definition L_bq : strat empty_sig (E_bq @ S_bq) ready := closure (join L_enq_strat L_deq_strat).

Definition L_inc1_play (f: nat -> val) (c1 c2: nat): @play 0 (E_rb @ S_rb) ready :=
  oq (inc1, (f, c1, c2)) :: @pa _ _ (inc1, (f, c1, c2)) (c1, (f, ((S c1) mod N)%nat, c2)) :: pnil_ready.
Definition L_inc2_play (f: nat -> val) (c1 c2: nat): @play 0 (E_rb @ S_rb) ready :=
  oq (inc2, (f, c1, c2)) :: @pa _ _ (inc2, (f, c1, c2)) (c2, (f, c1, ((S c2) mod N)%nat)) :: pnil_ready.
Definition L_get_play (f: nat -> val) (c1 c2: nat) (i: nat): @play 0 (E_rb @ S_rb) ready :=
  oq (get i, (f, c1, c2)) :: @pa _ _ (get i, (f, c1, c2)) (f i, (f, c1, c2)) :: pnil_ready.
Definition L_set_play (f: nat -> val) (c1 c2: nat) (i: nat) (v: val): @play 0 (E_rb @ S_rb) ready :=
  oq (set i v, (f, c1, c2)) :: @pa _ _ (set i v, (f, c1, c2)) (tt , (fun j => if Nat.eq_dec i j then v else f j, c1, c2)) :: pnil_ready.
Definition L_inc1_strat: strat 0 (E_rb @ S_rb) ready := sup f, sup c1, sup c2, down (L_inc1_play f c1 c2).
Definition L_inc2_strat: strat 0 (E_rb @ S_rb) ready := sup f, sup c1, sup c2, down (L_inc2_play f c1 c2).
Definition L_get_strat: strat 0 (E_rb @ S_rb) ready := sup f, sup c1, sup c2, sup i, down (L_get_play f c1 c2 i).
Definition L_set_strat: strat 0 (E_rb @ S_rb) ready := sup f, sup c1, sup c2, sup i, sup v, down (L_set_play f c1 c2 i v).
Definition L_rb : strat empty_sig (E_rb @ S_rb) ready := closure (join (join L_inc1_strat L_inc2_strat) (join L_get_strat L_set_strat)).

Global Hint Constructors tstrat_has id_has: core.

Global Instance conv_id_regular {E}: RegularConv (@conv_id E).
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

Local Instance L_rb_regular : Regular L_rb. Admitted.

Local Transparent join.

(* L_bq ⊑ (M_bq @ S_rb) ∘ L_rb *)
Lemma ϕ1 :
  rsq conv_id (tconv conv_id bq_rb_rel) rs_ready
    L_bq (compose cpos_ready (M_bq @ S_rb)%strat L_rb).
Proof.
  unfold M_bq. rewrite <- closure_lift.
  rewrite <- @closure_comp_ref2. 2: typeclasses eauto.
  apply rsq_closure; eauto with typeclass_instances.
  intros s (i & Hs). destruct i.
  - (* enq *)
    destruct Hs as ((v & Hv) & (bq & Hbq) & Hs). cbn in Hs. rewrite Hs. clear Hs.
    setoid_rewrite tstrat_sup_l. setoid_rewrite compose_sup_l.
    apply rsp_sup_exist. exists true.
    unfold L_enq_play. apply rsp_oq.
    { repeat econstructor. Unshelve. refine v. refine 0%nat. }
    intros (q & rb) (Hq1 & Hq2).
    cbn in Hq1. dependent destruction Hq1.
    cbn in Hq2. dependent destruction Hq2.
    destruct rb as [[f c1] c2].
    set (fx := (fun j : nat => if Nat.eq_dec c2 j then v else f j)).
    eapply rsp_pa with (r2 := (tt, (fx, c1, S c2 mod N)%nat)).
    { (* match reply *)
      intros HX. Local Opaque N. cbn in HX.
      destruct HX as (? & ? & HX). clear - HX Hv Hbq. destruct HX as [HX|HX].
      - dependent destruction HX. congruence.
      - dependent destruction HX. apply HA.
        apply refine_correct2; eauto. }
    clear HQ. apply rsp_ready.
    cbn - [compose tstrat M_enq_strat].
    eexists _, _. repeat apply conj.
    3: { (* incoming question *) apply comp_oq.
      (* call inc *) apply comp_lq. apply comp_ra.
      (* call set *) apply comp_lq. apply comp_ra.
      (* return *) apply comp_la. instantiate (1 := pnil_ready). apply comp_ready. }
    2: { eapply closure_has_cons; [ | | apply seq_comp_oq; apply seq_comp_pa; eauto ].
      2: eapply closure_has_cons; [ | | apply seq_comp_oq; apply seq_comp_pa; eauto ].
      3: eauto.
      - exists true. exists false. cbn. exists f, c1, c2. repeat econstructor.
      - exists false. exists false. cbn. exists f, c1, (S c2 mod N)%nat, c2, v. repeat econstructor. }
    eexists _, _. repeat apply conj.
    + repeat econstructor.
    + exists v, c2. cbn. reflexivity.
    + cbn. repeat econstructor.
  - (* deq *)
    destruct Hs as (v & bq & Hs). cbn in Hs. rewrite Hs. clear Hs.
    setoid_rewrite tstrat_sup_l. setoid_rewrite compose_sup_l.
    apply rsp_sup_exist. exists false.
    unfold L_deq_play. apply rsp_oq.
    { repeat econstructor. Unshelve. refine v. refine 0%nat. }
    intros (q & rb) (Hq1 & Hq2).
    cbn in Hq1. dependent destruction Hq1.
    cbn in Hq2. dependent destruction Hq2.
    destruct rb as [[f c1] c2].
    eapply rsp_pa with (r2 := (f c1, (f, (S c1 mod N)%nat, c2))).
    { (* match reply *)
      intros HX. cbn in HX.
      destruct HX as (? & ? & HX). apply refine_correct1 in HQ.
      destruct HX as [HX|HX].
      - dependent destruction HX. destruct HQ. congruence.
      - dependent destruction HX. apply HA. apply HQ. }
    clear HQ. apply rsp_ready.
    cbn - [compose tstrat M_enq_strat].
    eexists _, _. repeat apply conj.
    3: { (* incoming question *) apply comp_oq.
      (* call inc *) apply comp_lq. apply comp_ra.
      (* call get *) apply comp_lq. apply comp_ra.
      (* return *) apply comp_la. instantiate (1 := pnil_ready). apply comp_ready. }
    2: { eapply closure_has_cons; [ | | apply seq_comp_oq; apply seq_comp_pa; eauto ].
      2: eapply closure_has_cons; [ | | apply seq_comp_oq; apply seq_comp_pa; eauto ].
      3: eauto.
      - exists true. exists true. cbn. exists f, c1, c2. repeat econstructor.
      - exists false. exists true. cbn. exists f, (S c1 mod N)%nat, c2, c1. repeat econstructor. }
    eexists _, _. repeat apply conj.
    + repeat econstructor.
    + exists (f c1), c1. reflexivity.
    + cbn. repeat econstructor.
Qed.

Definition rb0: rb_state := (fun _ => Vint (Int.zero), 0, 0)%nat.
Definition bq0: bq_state := nil.

Definition Π_rb := encap rb0 L_rb.
Definition Π_bq := encap bq0 L_bq.

(* Π_bq ⊑ M_bq ∘ Π_rb *)
Lemma ϕ1' : Π_bq [= compose cpos_ready M_bq Π_rb.
Proof.
  unfold Π_bq, Π_rb. unfold encap.
  rewrite <- compose_assoc with (p1 := cpos_ready) (p2 := cpos_ready).
  rewrite <- encap_lift.
  rewrite compose_assoc with (p3 := cpos_ready) (p4 := cpos_ready).
  apply rsq_id_conv with (p := rs_ready).
  eapply rsq_comp. constructor.
  (* deterministic *) admit.
  (* deterministic *) admit.
  apply representation_independence with (R := rb_bq).
  { eapply bq_rb_intro with (n := 0%nat).
    Local Transparent N.
    all: eauto; unfold N, Example.N; try lia. }
  apply ϕ1.
Admitted.

(** * Proving strategies are implemented by Clight programs *)

Import Maps.

Context trb (HT2: ClightP.transl_program rb_program = Errors.OK trb).

Definition ce := ClightP.ClightP.prog_comp_env rb_program.
Definition sk := skel bq_spec.
Definition se_valid1 se := Genv.valid_for sk se.
Context (penv0 : PEnv.penv) (Hpenv0 : rb_penv_rel rb0 penv0).
Context (m0 : Mem.mem) (arr_b cnt1_b cnt2_b: positive).
Definition se_valid2 se :=
  Genv.find_symbol se arr_id = Some arr_b /\
  Genv.find_symbol se cnt1_id = Some cnt1_b /\
  Genv.find_symbol se cnt2_id = Some cnt2_b.
Definition id_in_penv id := id = arr_id \/ id = cnt1_id \/ id = cnt2_id.
Context (Hm0: forall se, se_valid2 se -> PEnv.penv_mem_match ce se penv0 m0)
  (Hse_valid2_inv: forall se pe m, PEnv.penv_mem_match ce se pe m -> se_valid2 se).
Context (match_rb_id_in_penv:
  forall rb pe id v, rb_penv_rel rb pe -> pe!id = Some v -> id_in_penv id).

Lemma se_valid2_in_penv_agree se1 se2 id:
  se_valid2 se1 -> se_valid2 se2 -> id_in_penv id ->
  Genv.find_symbol se1 id = Genv.find_symbol se2 id.
Proof.
  intros (A & B & C) (D & E & F) [H1|[H1|H1]]; congruence.
Qed.

(** ** Bq correctness *)

Section C_CONV.
  Import ListNotations.
  Local Open Scope embed_scope.
  Import Values Integers Memory.

  Inductive E_bq_conv_mq : op E_bq -> op li_c -> Prop :=
  | E_bq_conv_mq_enq v vf sg (se: Genv.symtbl) m b
    (HVF: vf = Vptr b Ptrofs.zero) (HB: Genv.find_symbol se enq_id = Some b)
    (HLE: Ple (Genv.genv_next se) (Mem.nextblock m))
    (HV: Cop.val_casted v tint) (HSG: sg = enq_sg)
    (HSE1: se_valid1 se) (HSE2: se_valid2 se):
    E_bq_conv_mq (enq v) (se, cq vf sg [ v ] m)
  | E_bq_conv_mq_deq vf sg (se: Genv.symtbl) m b
    (HVF: vf = Vptr b Ptrofs.zero) (HB: Genv.find_symbol se deq_id = Some b)
    (HLE: Ple (Genv.genv_next se) (Mem.nextblock m)) (HSG: sg = deq_sg)
    (HSE1: se_valid1 se) (HSE2: se_valid2 se):
    E_bq_conv_mq deq (se, cq vf sg [ ] m).

  Inductive E_bq_conv_mr : forall (m1: op E_bq) (m2: op li_c), ar m1 -> ar m2 -> Prop :=
  | E_bq_conv_mr_enq v se q m (HM: m = cq_mem q):
    E_bq_conv_mr (enq v) (se, q) tt (cr Vundef m)
  | E_bq_conv_mr_deq v se q m (HM: m = cq_mem q):
    E_bq_conv_mr deq (se, q) v (cr v m).

  Inductive E_rb_conv_mq : op E_rb -> op li_c -> Prop :=
  | E_rb_conv_mq_set i v vf sg (se: Genv.symtbl) c_i m b
    (HVF: vf = Vptr b Ptrofs.zero) (HB: Genv.find_symbol se set_id = Some b)
    (HLE: Ple (Genv.genv_next se) (Mem.nextblock m))
    (HI: c_i = Vint (Int.repr (Z.of_nat i)))
    (HV: Cop.val_casted v tint) (HSG: sg = set_sg) (HSE: se_valid2 se):
    E_rb_conv_mq (set i v) (se, cq vf sg [ c_i; v ] m)
  | E_rb_conv_mq_get i vf sg (se: Genv.symtbl) c_i m b
    (HVF: vf = Vptr b Ptrofs.zero) (HB: Genv.find_symbol se get_id = Some b)
    (HLE: Ple (Genv.genv_next se) (Mem.nextblock m))
    (HSG: sg = get_sg) (HSE: se_valid2 se):
    E_rb_conv_mq (get i) (se, cq vf sg [ c_i ] m)
  | E_rb_conv_mq_inc1 vf sg (se: Genv.symtbl) m b
    (HVF: vf = Vptr b Ptrofs.zero) (HB: Genv.find_symbol se inc1_id = Some b)
    (HLE: Ple (Genv.genv_next se) (Mem.nextblock m))
    (HSG: sg = inc1_sg) (HSE: se_valid2 se):
    E_rb_conv_mq inc1 (se, cq vf sg [ ] m)
  | E_rb_conv_mq_inc2 vf sg (se: Genv.symtbl) m b
    (HVF: vf = Vptr b Ptrofs.zero) (HB: Genv.find_symbol se inc2_id = Some b)
    (HLE: Ple (Genv.genv_next se) (Mem.nextblock m))
    (HSG: sg = inc2_sg) (HSE: se_valid2 se):
    E_rb_conv_mq inc2 (se, cq vf sg [ ] m).

  Inductive E_rb_conv_mr : forall (m1: op E_rb) (m2: op li_c), ar m1 -> ar m2 -> Prop :=
  | E_rb_conv_mr_set i v se q m (HM: m = cq_mem q):
    E_rb_conv_mr (set i v) (se, q) tt (cr Vundef m)
  | E_rb_conv_mr_get i v se q m (HM: m = cq_mem q):
    E_rb_conv_mr (get i) (se, q) v (cr v m)
  | E_rb_conv_mr_inc1 se q c_i i m (HM: m = cq_mem q)
      (HI: c_i = Vint (Int.repr (Z.of_nat i))):
    E_rb_conv_mr inc1 (se, q) i (cr c_i m)
  | E_rb_conv_mr_inc2 se q c_i i m (HM: m = cq_mem q)
      (HI: c_i = Vint (Int.repr (Z.of_nat i))):
    E_rb_conv_mr inc2 (se, q) i (cr c_i m).

End C_CONV.

Definition E_bq_conv : esig_rel E_bq li_c :=
  {| match_query := E_bq_conv_mq; match_reply := E_bq_conv_mr |}.
Definition E_rb_conv : esig_rel E_rb li_c :=
  {| match_query := E_rb_conv_mq; match_reply := E_rb_conv_mr |}.

Lemma ϕ_bq0 : rsq E_rb_conv E_bq_conv rs_ready M_bq bq_spec.
Proof.
  apply rsq_closure; eauto with typeclass_instances.
  intros s (i & Hs). destruct i.
  - (* enq *)
    cbn in Hs. destruct Hs as (v & i & Hs). rewrite Hs. clear Hs.
    unfold M_enq_play. apply rsp_oq.
    { repeat econstructor. }
    intros cq Hq. cbn in Hq. dependent destruction Hq. inv HM.
    exploit inc2_block. apply HSE1.
    intros (b1 & Hb1 & Hbb1).
    eapply rsp_pq with (m2 := (se, cq (Vptr b1 Ptrofs.zero) inc2_sg nil m)%embed).
    { constructor. econstructor; eauto. }
    eapply rsp_oa.
    { cbn. admit. }
    cbn. intros r Hr. destruct r as [c_i rm].
    apply esig_rel_mr_elim in Hr. 2: { econstructor; eauto. }
    cbn in Hr. dependent destruction Hr.
    rewrite regular_conv; eauto.
    2: { constructor. econstructor; eauto. }
    2: { apply esig_rel_mr_intro. constructor; eauto. }
    exploit set_block. apply HSE1.
    intros (b2 & Hb2 & Hbb2).
    eapply rsp_pq with
      (m2 := (se, cq (Vptr b2 Ptrofs.zero) set_sg [Vint (Int.repr (Z.of_nat i)); v] rm)%embed).
    { constructor. econstructor; eauto. }
    eapply rsp_oa.
    { cbn. admit. }
    cbn. intros r2 Hr2.
    apply esig_rel_mr_elim in Hr2. 2: { econstructor; eauto. }
    cbn in Hr2. dependent destruction Hr2.
    eapply rsp_pa with (cr Vundef rm).
    { apply esig_rel_mr_intro. constructor; eauto. }
    apply rsp_ready. cbn.
    eapply lts_strat_has_intro; eauto.
    { eapply initial_state_enq; eauto. admit. }
Admitted.

Definition E_rb_m0_conv_explicit : conv E_rb (li_c @ Mem.mem) := deencap m0 E_rb_conv.
Definition E_bq_m0_conv_explicit : conv E_bq (li_c @ Mem.mem) := deencap m0 E_bq_conv.

Definition E_rb_m0_conv : conv E_rb li_c := vcomp E_rb_m0_conv_explicit join_conv.
Definition E_bq_m0_conv : conv E_bq li_c := vcomp E_bq_m0_conv_explicit join_conv.

Lemma rsq_deencap_target {E1 E2 F1 F2 U}
  (R: conv E1 F1) (S: conv E2 F2) σ τ u0:
  rsq R S rs_ready σ τ ->
  rsq (deencap u0 R) (deencap u0 S) rs_ready σ (τ @ U)%strat.
Proof.
  unfold deencap. intros.
  eapply rsq_vcomp. constructor. 1-2: admit.
  apply H.
  (* TODO: some conjoint property? *)
Admitted.

Lemma rsq_lift_convert {li S} L:
  rsq (lift_convert_rel li S) (lift_convert_rel li S)
      rs_ready ((lts_strat L) @ S)%strat (Lifting.lifted_semantics S L).
Admitted.

Definition ϕ_bq_conv_1 :=
  vcomp (vcomp (deencap m0 E_rb_conv) (lift_convert_rel li_c mem)) join_cc.
Definition ϕ_bq_conv_2 :=
  vcomp (vcomp (deencap m0 E_bq_conv) (lift_convert_rel li_c mem)) join_cc.
Lemma ϕ_bq_with_internals : rsq ϕ_bq_conv_1 ϕ_bq_conv_2 rs_ready M_bq (Clight.semantics2 BQ.bq_program).
Proof.
Admitted.

(** ** Rb correctness *)

Definition E_rb_S_rb_conv : conv (E_rb @ S_rb) (Lifting.lifted_li rb_state li_c) :=
  vcomp (tconv E_rb_conv conv_id) (lift_convert_rel li_c rb_state).

Lemma ϕ_rb0 : rsq E0_conv E_rb_S_rb_conv rs_ready L_rb rb_spec.
Proof.
  apply rsq_closure; eauto with typeclass_instances. admit. 
  intros s (i & Hs). destruct i; destruct Hs as [[|] Hs].
Admitted.

Definition E_rb_rb0_conv : conv E_rb (li_c @ S_rb) := deencap rb0 E_rb_conv.
Definition E_rb_rb0_conv' : conv E_rb (Lifting.lifted_li S_rb li_c) :=
  vcomp E_rb_rb0_conv (lift_convert_rel li_c S_rb).

Lemma ϕ_rb1 : rsq E0_conv E_rb_rb0_conv' rs_ready Π_rb rb_spec.
Proof.
  replace E_rb_rb0_conv' with (vcomp (deencap rb0 conv_id) E_rb_S_rb_conv).
  2: {
    unfold E_rb_rb0_conv', E_rb_rb0_conv, E_rb_S_rb_conv.
    rewrite <- vcomp_assoc. f_equal.
    unfold deencap. admit.
  }
  rewrite <- (vcomp_left_id (@E0_conv li_c)).
  eapply rsq_vcomp. constructor. admit. admit.
  apply deencap_rsq.
  apply ϕ_rb0.
Admitted.

Definition ϕ_rb_conv := vcomp (vcomp E_rb_rb0_conv' rb_cc) (ClightP.pin ce).

Lemma ϕ_rb_with_internals : rsq E0_conv ϕ_rb_conv rs_ready Π_rb (Clight.semantics2 trb).
Proof.
Admitted.

(** ** Putting things together *)

Inductive rb_m_mq : op (li_c @ S_rb) -> op (li_c @ mem) -> Prop :=
| rb_m_mq_intro rb m q se pe
    (HRB: rb_penv_rel rb pe) (HM: PEnv.penv_mem_match ce se pe m):
  rb_m_mq ((se, q)%embed, rb) ((se, q)%embed, m).
Inductive rb_m_mr (m1: op (li_c @ S_rb)) (m2: op (li_c @ mem)): ar m1 -> ar m2 -> Prop :=
| rb_m_mr_intro rb m r se q pe (HRB: rb_penv_rel rb pe)
    (HM: PEnv.penv_mem_match ce se pe m):
  (se, q)%embed = fst m1 ->
  rb_m_mr m1 m2 (r, rb) (r, m).
Definition rb_m_esig_rel : esig_rel (li_c @ S_rb) (li_c @ mem) :=
  {| match_query := rb_m_mq; match_reply := rb_m_mr |}.

Definition m_rb_ref:
  vcomp E_rb_conv (de m0) [= vcomp (vcomp E_rb_conv (de rb0)) rb_m_esig_rel.
Proof.
  cbn. intros c.
  assert (rb_penv_rel rb0 penv0 /\
            forall se, se_valid2 se -> PEnv.penv_mem_match ce se penv0 m0) as H.
  { split. apply Hpenv0. intros se Hse. apply Hm0. eauto. }
  revert H. generalize rb0 penv0 m0. induction c.
  - intros rb pe m [Hpe1 Hpe2].
    cbn. intros ((se & q) & Hq1 & Hq2). xinv Hq1. xinv Hq2. 
    exists ((se, q)%embed, rb). split.
    2: { constructor. econstructor; eauto. xinv HM; eauto. }
    exists (se, q)%embed. split. constructor. eauto. constructor.
  - intros rb pe m [Hpe1 Hpe2].
    cbn. intros ((se & q) & Hq1 & Hq2 & Ha). xinv Hq1. xinv Hq2.
    exists ((se, q)%embed, rb). split.
    exists (se, q)%embed. split. constructor. eauto. constructor.
    split. { constructor. econstructor; eauto. xinv HM; eauto. }
    intros [cr rb1]. apply or_commut. apply not_imply_or. intros Hr.
    exists (se, q)%embed. split. { constructor. eauto. }
    split. { constructor. }
    intros cr1. apply or_commut. apply not_imply_or. intros Hr1.
    specialize (Ha cr1) as [Ha|Ha]; eauto.
    eapply esig_rel_mr_elim in Hr.
    2: { econstructor; eauto. xinv HM; eauto. }
    xinv Hr. cbn in *. inv H2.
    xinv Ha. constructor. cbn. eauto.
    intros Hx. apply Hr1. constructor. eauto.
  - intros rb pe m [Hpe1 Hpe2].
    cbn. intros ((se & q) & Hq1 & Hq2 & Ha). xinv Hq1. xinv Hq2.
    exists ((se, q)%embed, rb). split.
    exists (se, q)%embed. split. constructor. eauto. constructor.
    split. { constructor. econstructor; eauto. xinv HM; eauto. }
    intros [cr rb1]. apply not_imply_or. intros Hr.
    apply not_imply_or. intros Hr1.
    eapply esig_rel_mr_elim in Hr1.
    2: { econstructor; eauto. xinv HM; eauto. }
    xinv Hr1. cbn in *. inv H2.
    specialize (Ha cr) as [Ha|[Ha|Ha]].
    + exfalso. xinv Ha. apply Hr.
      exists (se, q)%embed. split. { constructor. eauto. }
      split. { constructor. }
      intros cr1. apply or_commut. apply not_imply_or.
      intros Ha. constructor; eauto.
      intros Hra. apply Ha. constructor. intros <-. easy.
    + exfalso. xinv Ha. easy.
    + assert (Hrc1: rcnext ((se, q)%embed, rb) ((se, q)%embed, m) (cr, rb1) (cr, m2) rb_m_esig_rel = rb_m_esig_rel).
      { apply regular_conv.
        - econstructor. econstructor; eauto. xinv HM; eauto. 
        - intros Hx. xinv Hx. apply HA. econstructor; eauto. reflexivity. }
      rewrite Hrc1.
      assert (Hrc2: rcnext (se, q)%embed ((se, q)%embed, m) cr (cr, m2) (de m) = de m2).
      { clear. apply antisymmetry.
        - intros c Hc. cbn in *. xinv Hc. eauto.
        - intros c Hc. constructor. eauto. }
      rewrite Hrc2 in Ha.
      assert (Hrc3: rcnext m1 (se, q)%embed n1 cr E_rb_conv = E_rb_conv).
      { apply regular_conv.
        - constructor. cbn. easy.
        - intros Hra. xinv Hra. apply Hr.
          exists (se, q)%embed. split. { constructor. eauto. }
          split. { constructor. }
          intros cr1. apply or_commut. apply not_imply_or.
          intros Hxa. constructor; eauto.
          intros Hra. apply Hxa. constructor. intros <-. easy. }
      rewrite Hrc3 in Ha. 
      assert (Hrc4: rcnext (se, q)%embed ((se, q)%embed, rb) cr (cr, rb1) (de rb) = de rb1).
      { clear. apply antisymmetry.
        - intros c Hc. cbn in *. xinv Hc. eauto.
        - intros c Hc. constructor. eauto. }
      assert (Hrc5: rcnext m1 ((se, q)%embed, rb) n1 (cr, rb1) (vcomp E_rb_conv (de rb)) = vcomp E_rb_conv (de rb1)).
      { apply antisymmetry.
        - intros d Hd. cbn in Hd. cbn. 
          eprod_crush. xinv H. cbn in HM. xinv H0. inv H4.
          specialize (H1 cr).
          destruct H1 as [H1|[H1|H1]].
          + exfalso. xinv H1. apply Hr.
            exists (se, q)%embed. split. { constructor. eauto. }
            split. { constructor. }
            intros cr1. apply or_commut. apply not_imply_or.
            intros Hxa. constructor; eauto.
            intros Hra. apply Hxa. constructor. intros <-. easy.
          + exfalso. xinv H1. easy.
          + congruence.
        - intros d Hd. cbn.
          exists (se, q)%embed. split. { constructor. now cbn. }
          split. { constructor. }
          intros cr1. apply not_imply_or. intros Hxa.
          apply not_imply_or. intros Hxb.
          assert (cr = cr1).
          { apply NNPP. intros HA. apply Hxb. constructor. congruence. }
          eapply esig_rel_mr_elim in Hxa.
          2: { cbn. eauto. } subst cr1.
          rewrite Hrc3. rewrite Hrc4. apply Hd. }
      rewrite Hrc5. eapply IHc; eauto.
      split; eauto. intros. clear - HM0 HRB H.
      exploit Hse_valid2_inv. eauto. intros Hx.
      constructor. intros id v Hv.
      inv HM0. specialize (MPE _ _ Hv) as (b & Hb & Hbb).
      exists b. split; eauto.
      rewrite <- Hb. apply se_valid2_in_penv_agree; eauto.
      eapply match_rb_id_in_penv; eauto.
Qed.


Section PIN_NO_JOIN.

  Import Lifting PEnv.
  Inductive pin_query R: Memory.mem * Genv.symtbl -> query (li_c @ penv) -> query (li_c @ mem) -> Prop :=
  | pin_query_intro se m q pe (MPE: R se pe m):
    pin_query R (m, se) (q, pe) (q, m).
  Inductive pin_reply R: Memory.mem * Genv.symtbl -> reply (li_c @ penv) -> reply (li_c @ mem) -> Prop :=
  | pin_reply_intro se r m pe (MPE: R se pe m):
    pin_reply R (m, se) (r, pe) (r, m).
  Program Definition pin_no_join ce: callconv (li_c @ penv) (li_c @ mem) :=
    {|
      ccworld := Memory.mem * Genv.symtbl;
      match_senv '(_, se) se1 se2 := se = se1 /\ se = se2;
      LanguageInterface.match_query := pin_query (penv_mem_match ce);
      LanguageInterface.match_reply '(_, se) r1 r2 := exists m, pin_reply (penv_mem_match ce) (m, se) r1 r2;
    |}.
  Next Obligation. reflexivity. Qed.
  Next Obligation. inv H0. reflexivity. Qed.
  Next Obligation. inv H. reflexivity. Qed.

End PIN_NO_JOIN.

Local Opaque ce.

Lemma pin_join_ref :
  vcomp (pin_no_join ce) join_cc [= ClightP.pin ce.
Proof.
  intros c Hc. induction c.
  - cbn in *. eprod_crush. xinv H. xinv H0.
    xinv HM. xinv HM0. xinv HSE0. xinv HSE.
    econstructor. instantiate (1 := (m, s)).
    cbn. easy. constructor; eauto.
  - cbn in *. eprod_crush. xinv H. xinv H0.
    xinv HM. xinv HM0. xinv HSE0. xinv HSE.
    econstructor. instantiate (1 := (m, s)).
    cbn. easy. constructor; eauto.
    intros Hr. xinv Hr. inv H. cbn in *.
    destruct (H1 (cr rv msrc0, x)) as [Hr|Hr].
    + xinv Hr. destruct w. destruct HSE. subst.
      apply HN. econstructor. econstructor. eauto.
    + xinv Hr. apply HN. constructor. eauto.
  -  cbn in *. eprod_crush. xinv H. xinv H0.
    xinv HM. xinv HM0. xinv HSE0. xinv HSE.
    econstructor. instantiate (1 := (m, s)).
    cbn. easy. constructor; eauto.
    intros Hr. xinv Hr. inv H. cbn in *.
    apply IHc. clear IHc.
    destruct (H1 (cr rv msrc0, x)) as [Hr|[Hr|Hr]].
    + exfalso. xinv Hr. destruct w. destruct HSE. subst.
      apply HN. econstructor. econstructor. eauto.
    + exfalso. xinv Hr. apply HN. constructor. eauto.
    + erewrite !regular_conv in Hr; eauto.
      * econstructor. econstructor. econstructor; eauto.
      * intros Hx. xinv Hx. apply HN. econstructor. eauto.
      * econstructor. instantiate (1 := (m, s)).
        constructor; eauto. constructor. eauto.
      * intros Hx. xinv Hx. apply HN.
        destruct w. inv HSE. econstructor. econstructor. eauto.
        Unshelve.
        cbn. exact tt.
Qed.

Lemma ϕ_rb_conv_ref1: ϕ_bq_conv_1 [= ϕ_rb_conv.
Proof.
  unfold ϕ_bq_conv_1, ϕ_rb_conv, E_rb_rb0_conv', E_rb_rb0_conv, deencap.
  rewrite <- pin_join_ref.
  rewrite <- !vcomp_assoc.
  apply vcomp_ref. 2: reflexivity.
  rewrite m_rb_ref.
  rewrite !vcomp_assoc.
  apply vcomp_ref. reflexivity.
  apply vcomp_ref. reflexivity.
  intros c Hc. induction c.
  - cbn in *. eprod_crush. xinv H. xinv HM. xinv H0. xinv HM.
    exists (s, Datatypes.pair c r)%embed. split. repeat constructor.
    exists (s, Datatypes.pair c pe)%embed. split.
    + econstructor; econstructor; eauto.
    + econstructor. instantiate (1 := (_, s)). cbn. easy.
      cbn. econstructor; eauto.
  - cbn in *. eprod_crush. xinv H. xinv HM. xinv H0. xinv HM.
    exists (s, Datatypes.pair c1 r0)%embed. split. repeat constructor.
    split. exists (s, Datatypes.pair c1 pe)%embed. split.
    { econstructor; econstructor; eauto. }
    { econstructor. instantiate (1 := (_, s)). cbn. easy.
      cbn. econstructor; eauto. }
    intros [cr rb1]. apply not_imply_or. intros Hr.
    exists (s, Datatypes.pair c1 pe)%embed. split.
    { econstructor; econstructor; eauto. } split.
    { econstructor. instantiate (1 := (_, s)). cbn. easy.
      cbn. econstructor; eauto. }
    intros [cr1 p1]. apply not_imply_or. intros Hr1.
    econstructor. instantiate (1 := (_, s)). cbn. easy.
    cbn. constructor. eauto.
    intros Hr2. cbn in *. destruct Hr2 as (mx & Hmx). inv Hmx.
    eapply esig_rel_mr_elim in Hr. 2: { econstructor.  }
    eapply @rcp_forbid_mr with (w := tt) in Hr1.
    2: { cbn. easy. } 2: { constructor. eauto. }
    xinv Hr. xinv Hr1.
    specialize (H1 (c, m)) as [H1 | H1].
    + xinv H1. apply HA. econstructor; eauto. reflexivity.
    + xinv H1. apply HA. econstructor.
  - cbn in *. eprod_crush. xinv H. xinv HM. xinv H0. xinv HM.
    exists (s, Datatypes.pair c2 r0)%embed. split. repeat constructor.
    split. exists (s, Datatypes.pair c2 pe)%embed. split.
    { econstructor; econstructor; eauto. }
    { econstructor. instantiate (1 := (_, s)). cbn. easy.
      cbn. econstructor; eauto. }
    intros [cr rb1]. apply not_imply_or. intros Hr.
    eapply esig_rel_mr_elim in Hr. 2: { econstructor. }
    xinv Hr. apply not_imply_or. intros Hx.
    eapply not_ex_all_not with (n := (s, Datatypes.pair c2 pe)%embed) in Hx.
    apply not_and_or in Hx as [Hx | Hx].
    { exfalso. apply Hx. econstructor. now cbn.
      cbn. econstructor; eauto. }
    apply not_and_or in Hx as [Hx | Hx].
    { exfalso. apply Hx. econstructor.
      instantiate (1 := (_, s)). now cbn.
      cbn. econstructor; eauto. }
    apply not_all_ex_not in Hx as ((cr3 & p3) & Hx).
    apply not_or_and in Hx as [Hx1 Hx2].
    eapply @rcp_forbid_mr with (w := tt) in Hx1. xinv Hx1.
    2: { now cbn. } 2: { constructor; eauto. }
    eapply @rcp_forbid_mr with (w := (_, s)) in Hx2. xinv Hx2. inv H.
    2: { now cbn. } 2: { constructor; eauto. }
    specialize (H1 (c0, m)) as [H1|[H1|H1]].
    + exfalso. xinv H1. apply HA.
      econstructor; eauto. reflexivity.
    + exfalso. xinv H1. apply HA. econstructor.
    + rewrite !regular_conv in H1.
      rewrite !regular_conv. eauto.
      * econstructor. split. econstructor. cbn. eauto.
        constructor. eauto. econstructor.
        instantiate (1 := (_, s)). now cbn. constructor. eauto.
      * intros HA. cbn in HA.
        eprod_crush. specialize (H2 (c0, p3)) as [A | B].
        xinv A. apply HN. constructor. eauto.
        xinv B. apply HN. destruct w. econstructor.
        constructor. eauto. cbn in HSE. destruct HSE. subst. eauto.
      * repeat constructor.
      * intros HA. xinv HA. apply HA0. repeat constructor.
      * repeat constructor.
      * intros Hx. xinv Hx. apply HA. constructor.
      * constructor. econstructor; eauto.
      * intros HA. xinv HA. apply HA0.
        cbn. econstructor; eauto. reflexivity.
        Unshelve. all: cbn; exact tt.
Qed.

Lemma ϕ_bq_conv_ref1: ϕ_bq_conv_2 [= E_bq_m0_conv.
Proof.
  unfold ϕ_bq_conv_2, E_bq_m0_conv, E_bq_m0_conv_explicit, join_conv, deencap.
  rewrite <- !vcomp_assoc. reflexivity.
Qed.

Lemma ϕ_bq_rb:
  rsq E0_conv ϕ_bq_conv_2 rs_ready Π_bq
    (compose cpos_ready (Clight.semantics2 BQ.bq_program) (Clight.semantics2 trb)).
Proof.
  rewrite ϕ1'.
  eapply rsq_comp. constructor.
  1-2: admit.
  - apply ϕ_bq_with_internals.
  - rewrite ϕ_rb_conv_ref1.
    apply ϕ_rb_with_internals.
Admitted.

(* --------------------------------------- *)

Lemma ϕ_bq : rsq E_rb_m0_conv E_bq_m0_conv rs_ready M_bq (Clight.semantics2 BQ.bq_program).
Proof.
  pose proof BQ.bq_correct0 as HA.
  apply fsim_rsq in HA. 2: admit.
  eapply @rsq_vcomp in HA. 5: apply ϕ_bq0. 2: constructor. 2-3: admit.

  (* pose proof (ClightP.transl_program_correct _ _ HT1). *)
  (* assert (rsq (vcomp (vcomp E_rb_conv flag_cc) ClightP.pout) *)
  (*             (vcomp (vcomp E_bq_conv bq_cc) (ClightP.pin ce)) *)
  (*             rs_ready M_bq (Clight.semantics2 tbq)) as HX. *)
  (* { *)
  (*   eapply rsq_vcomp. constructor. admit. admit. 2: apply fsim_rsq; eauto. 2: admit. *)
  (*   eapply rsq_vcomp. constructor. admit. admit. apply ϕ_bq0. *)
  (*   apply fsim_rsq; eauto. admit. *)
  (* } *)
  eapply (rsq_deencap_target _ _ _ _ m0) in HA.
  pose proof (@rsq_lift_convert _ mem (Clight.semantics2 BQ.bq_program)) as HB.
  eapply @rsq_vcomp in HB. 5: apply HA. 2: constructor. 2-3: admit.
  pose proof (fp BQ.bq_program) as HC. apply fsim_rsq in HC. 2: admit.
  eapply @rsq_vcomp in HC. 5: apply HB. 2: constructor. 2-3: admit.
  (* rewrite ϕ_rb_conv_ref. *)
  (* rewrite <- !E0_conv_vcomp in HX. apply HX. *)
Admitted.

Lemma ϕ_rb_conv_ref:
  E_rb_m0_conv [= (vcomp (vcomp E_rb_rb0_conv' rb_cc) (ClightP.pin ce)).
Proof.
  unfold E_rb_m0_conv. unfold E_rb_m0_conv_explicit. unfold deencap.
  unfold E_rb_rb0_conv'. unfold E_rb_rb0_conv. unfold deencap.
  unfold join_conv.
  rewrite !vcomp_assoc.
  intros c Hc. revert Hc.

  (* destruct c. *)
  (* - cbn in *. *)
  (*   (* destruct Hc as [Hc1 Hc2]. *) *)
  (*   (* destruct Hc2 as ((se3 & (cq & m_frag1)) & Hc2 & Hc3). *) *)
  (*   (* xinv Hc2. xinv Hc3. cbn in *. subst. xinv HM. xinv Hc1. *) *)
  (*   admit. *)
  (* - cbn in *. *)
  (*   admit. *)
  (* -  *)

  (* rewrite vcomp_expand. intros c (((se1 & q1) & m_frag) & Hc). cbn in Hc. *)
  (* rewrite vcomp_expand. cbn. *)
  (* exists ((se1, q1)%embed, rb0). intros [[cr rb1]|]. *)
  (* 2: { *)
  (*   specialize (Hc None). destruct c; cbn in *. *)
  (*   - cbn. admit. *)
  (*   - admit. *)
  (*   - admit. *)
  (* } *)
  (* specialize (Hc (Some (cr, m_frag))). *)
  (* - cbn in *. admit. *)
  (* - cbn in *. *)

  (* eapply rsq_vcomp. constructor. admit. admit. *)
  (* assert (R: rel S_rb Mem.mem). admit. *)
  (* set (t := (tstrat tp_ready id R)). *)
  (* instantiate (1 := (tstrat tpos_ready id R)). *)

  (* cbn. intros c Hc. induction c. *)
  (* - rename m1 into mq. cbn in *. destruct m2 as (se & cqm). *)
  (*   destruct Hc as (((se1 & q1) & m_frag) & Hc1 & Hc3). *)
  (*   destruct Hc1 as ((se2 & q2) & Hc1 & Hc2). *)
  (*   destruct Hc3 as ((se3 & (cq & m_frag1)) & Hc3 & Hc4). *)
  (*   xinv Hc3. xinv HM. xinv Hc1. xinv Hc2. inv H2. xinv Hc4. cbn in *. subst. *)
  (*   exists (se, Datatypes.pair cq penv0)%embed. split. *)
  (*   2: { econstructor. instantiate (1 := (m0, se)). *)
  (*        - constructor; eauto. *)
  (*        - cbn. inv HM0. constructor; eauto. *)
  (*          apply Hm0. inv HM; eauto. } *)
  (*   exists (se, Datatypes.pair cq rb0)%embed. split. *)
  (*   2: { econstructor. reflexivity. cbn. *)
  (*        destruct cq. constructor. 2: apply Hpenv0. *)
  (*        inv HM0. eauto. } *)
  (*   exists ((se, cq)%embed, rb0). split. *)
  (*   2: { repeat econstructor. } *)
  (*   exists (se, cq)%embed. split. *)
  (*   { constructor. apply HM. } *)
  (*   constructor. *)
  (* - rename m1 into mq. cbn in Hc. destruct m2 as (se & cqm). *)
  (*   destruct Hc as (((se1 & q1) & m_frag) & Hc1 & Hc3 & Hr1). *)
  (*   destruct Hc1 as ((se2 & q2) & Hc1 & Hc2). *)
  (*   destruct Hc3 as ((se3 & (cq & m_frag1)) & Hc3 & Hc4). *)
  (*   xinv Hc3. xinv HM. xinv Hc1. xinv Hc2. inv H2. xinv Hc4. cbn in * |-. subst. *)
  (*   unfold vcomp_has at 1. *)
  (*   assert (HA: cc_conv_has rb_cc (@rcp_allow (Lifting.lifted_li S_rb li_c) (Lifting.lifted_li PEnv.penv li_c) (se, Datatypes.pair cq rb0)%embed (se, Datatypes.pair cq penv0)%embed)). *)
  (*   { econstructor. reflexivity. cbn. destruct cq. constructor. 2: apply Hpenv0. inv HM0. eauto. } *)
  (*   assert (HB: Downset.has E_rb_rb0_conv' (@rcp_allow E_rb (Lifting.lifted_li S_rb li_c) mq (se, Datatypes.pair cq rb0)%embed)). *)
  (*   { exists ((se, cq)%embed, rb0). split. *)
  (*     - exists (se, cq)%embed. split. { constructor. apply HM. } constructor. *)
  (*     - repeat econstructor. } *)
  (*   assert (HC: Downset.has (vcomp E_rb_rb0_conv' rb_cc) (@rcp_allow E_rb (Lifting.lifted_li PEnv.penv li_c) mq (se, Datatypes.pair cq penv0)%embed)). *)
  (*   { exists (se, Datatypes.pair cq rb0)%embed. split. apply HB. apply HA. } *)
  (*   assert (HD: cc_conv_has (ClightP.pin ce) (@rcp_allow (Lifting.lifted_li PEnv.penv li_c) li_c (se, (Datatypes.pair cq penv0))%embed (se, cqm)%embed)). *)
  (*   { econstructor. instantiate (1 := (m0, se)). { constructor; eauto. } *)
  (*     cbn. inv HM0. constructor; eauto. apply Hm0. inv HM; eauto. } *)
  (*   exists (se, Datatypes.pair cq penv0)%embed. split. apply HC. split. apply HD. *)
  (*   intros (cr & pe1). apply not_imply_or. intros Hx. *)
  (*   eapply @rcp_forbid_mr with (w:= (m0, se)) in Hx. cbn in Hx. *)
  (*   destruct Hx as (mx & Hx). *)
  (*   2: { split; eauto. } *)
  (*   2: { cbn. inv HM0. constructor; eauto. apply Hm0. inv HM; eauto. } *)
  (*   exists (se, Datatypes.pair cq rb0)%embed. split. apply HB. split. apply HA. *)
  (*   intros (cr1 & rrb1). apply not_imply_or. intros Hy. *)
  (*   eapply @rcp_forbid_mr with (w:= tt) in Hy. cbn in Hy. inv Hy. *)
  (*   2: { reflexivity. } *)
  (*   2: { inv HM0. constructor; eauto. apply Hpenv0. } *)
  (*   exists ((se, cq)%embed, rb0). split. 2: split. *)
  (*   { exists (se, cq)%embed. split. { constructor. apply HM. } constructor. } *)
  (*   { repeat econstructor. } *)
  (*   intros (cr2 & rrb2). apply not_imply_or. intros Hz. *)
  (*   eapply esig_rel_mr_elim in Hz. 2: { repeat constructor. } inv Hz. *)
  (*   exists (se, cq)%embed. split. { constructor. apply HM. } split. constructor. *)
  (*   intros cr3. cbn. apply or_commut. apply not_imply_or. intros Hw. *)
  (*   eapply esig_rel_mr_elim in Hw. 2: apply HM.  *)
  (*   remember ({| cr_retval := rv; cr_mem := m |}) as cr. *)
  (*   specialize (Hr1 (cr, mx)) as [Hr1|Hr1]. *)
  (*   + destruct Hr1 as ((?&?) & C1 & C2 & Hr1). xinv C1. xinv C2. inv H2. *)
  (*     specialize (Hr1 cr3) as [Hr1|Hr1]. *)
  (*     * dependent destruction Hr1. easy. *)
  (*     * dependent destruction Hr1. constructor; eauto. *)
  (*   + exfalso. destruct Hr1 as ((?&?) & C1 & C2 & Hr1). *)
  (*     specialize (Hr1 (cr, mx)). xinv C1. xinv C2. xinv HM1. *)
  (*     destruct Hr1 as [Hr1|Hr1]. *)
  (*     * dependent destruction Hr1. apply HA0. constructor. *)
  (*     * dependent destruction Hr1. apply HN. xinv Hx. *)
  (*       econstructor; eauto. *)
  (* - *)


Admitted.

Lemma ϕ_rb : rsq E0_conv E_rb_m0_conv rs_ready Π_rb (Clight.semantics2 trb).
Proof.
  pose proof rb_correct2.
  pose proof (ClightP.transl_program_correct _ _ HT2).
  assert (rsq (vcomp (vcomp E0_conv 1%cc) ClightP.pout)
              (vcomp (vcomp E_rb_rb0_conv' rb_cc) (ClightP.pin ce))
              rs_ready Π_rb (Clight.semantics2 trb)) as HX.
  {
    eapply rsq_vcomp. constructor. admit. admit. 2: apply fsim_rsq; eauto. 2: admit.
    eapply rsq_vcomp. constructor. admit. admit. apply ϕ_rb1.
    apply fsim_rsq; eauto. admit.
  }
  (* rewrite ϕ_rb_conv_ref. *)
  (* rewrite <- !E0_conv_vcomp in HX. apply HX. *)
Admitted.

