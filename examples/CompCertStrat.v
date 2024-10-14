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
    rsq_when R S p σ1 τ1 ->
    rsq_when R S rs_ready σ2 τ2 ->
    rsq_when R S p (seq_compose σ1 σ2) (seq_compose τ1 τ2).
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
Arguments closure {E F} _%strat_scope.

Global Hint Constructors closure_has : core.

Lemma rsq_closure {E1 E2 F1 F2} (R S: conv _ _)
  `{!RegularConv R} `{!RegularConv S}
  (σ: @strat E1 F1 ready) (τ: @strat E2 F2 ready):
  rsq R S σ τ ->
  rsq R S (closure σ) (closure τ).
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

  Instance lts_strat_determ sk: Deterministic (lts_strat_sk sk L).
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

  Local Coercion lts_strat: semantics >-> poset_carrier.

  Lemma fsim_rsq: rsq ccA ccB L1 L2.
  Proof.
    unfold lts_strat. destruct FSIM as [[X]]. rewrite <- fsim_skel.
    eapply fsim_rsq_sk. apply Linking.linkorder_refl.
  Qed.

End FSIM.

Section REGULAR.

  Inductive play_suspended {E F}: forall i, @play E F i -> Prop :=
  | play_suspended_nil q m: play_suspended (suspended q m) (pnil_suspended q m)
  | play_suspended_cons i j (m: move j i) s:
    play_suspended i s -> play_suspended j (m :: s).
  Arguments play_suspended {E F i}.

  Inductive no_reentrancy_play {E F}: forall {i}, @play E F i -> Prop :=
  | no_reentrancy_ready: no_reentrancy_play pnil_ready
  | no_reentrancy_suspended q m: no_reentrancy_play (pnil_suspended q m)
  | no_reentrancy_oq q s:
    no_reentrancy_play s -> no_reentrancy_play (oq q :: s)
  | no_reentrancy_pq q m s:
    no_reentrancy_play s -> no_reentrancy_play (@pq _ _ q m :: s)
  | no_reentrancy_oa q m n s:
    no_reentrancy_play s -> no_reentrancy_play (@oa _ _ q m n :: s)
  | no_reentrancy_pa q r: no_reentrancy_play (@pa _ _ q r :: pnil_ready).
  Definition no_reentrancy {E F i} (σ: strat E F i): Prop :=
    forall s, Downset.has σ s -> no_reentrancy_play s.

  Hint Constructors play_suspended no_reentrancy_play : core.

  Lemma no_reentrancy_play_ref {E F i} (s t: @play E F i):
    s [= t -> no_reentrancy_play t -> no_reentrancy_play s.
  Proof.
    intros Href Ht. revert s Href. dependent induction Ht;
      intros; cbn in *; dependent destruction Href; eauto.
    xinv Href. eauto.
  Qed.

  Class Regular {E F} (σ: strat E F ready) :=
    { regular_closure: exists σ0, σ = closure σ0 /\ no_reentrancy σ0 }.

  Hint Constructors play_suspended : core.

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
Arguments play_suspended {E F i}.
Local Hint Constructors play_suspended : core.

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

  (* s* ∘ t ⊑ (s ∘ t)* *)
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

Lemma cc_conv_id {li}: @cc_conv li _ 1 = (@vid li).
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

Notation "E @ S" := (tens E (glob S)) : esig_scope.
Notation "σ @ S" := (tstrat tp_ready σ (@slens_id S)) : strat_scope.

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
  Definition encap {E F} (σ: strat E (F@U) ready) := e ⊙ σ.

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
  Definition deencap {E F} (R: conv E F) : conv E (F@U) := R ;; de.

End ENCAP.

(* The encapsulated strategy is refined by the original strategy using the
   "deencap" refinement convention.

   This should follow from the conjoint property.
   XXX: move to IntStrat.v *)
Lemma deencap_rsq {E F: esig} {S: Type} (σ: strat E (F@S) ready) (s0: S):
  rsq vid (de s0) (encap s0 σ) σ.
Proof.
Admitted.

(* E@[s0> ⊙ σ@S ⊑ σ ⊙ E@[s0>
   XXX: move to IntStrat.v *)
Lemma encap_lift {E F} {S: Type} (σ: strat E F ready) (s0: S):
  (e s0) ⊙ (σ @ S) [= σ ⊙ (e s0).
Admitted.

(* R s0 t0 → E@[s0> ⊑_{E@R → 1} E@[t0>
   XXX: move to IntStrat.v *)
Lemma representation_independence {E} {S T: Type} (R: rel S T) s0 t0:
  R s0 t0 -> rsq (tconv (@vid E) R) vid (e s0) (e t0).
Proof.
Admitted.

Global Hint Constructors sls_has tstrat_has : core.

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
    sls_has (@slens_id U) sp t /\ tstrat_has tp s t st /\
      (match sp with
      | sls_ready _ => True
      | sls_suspended _ v u | sls_running _ v u => v = u
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
      split. apply sls_has_pa with (p := tt) (p' := tt). eauto. 
      cbn. reflexivity. split; eauto.
      Unshelve. 1,3: exact tt. all: exact u.
Qed.

Lemma tstrat_seq_comp {E1 E2 U i j k} (tp: tpos i j k)
  es fs es1 es2 (s: @play (E1@U) (E2@U) _) st1:
  tstrat_has tp es fs s -> seq_comp_has es1 es2 es -> sls_has (@slens_id U) st1 fs ->
  exists s1 s2 st2 fs1 fs2,
    sls_has slens_id st1 fs1 /\ sls_has slens_id st2 fs2 /\
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
Qed.

Lemma lens_seq_comp {U V i} (l: lens U V) (sp: sls_state i) tp s t st:
  seq_comp_has s t st ->
  sls_has (embed_lens l) sp s ->
  sls_has (embed_lens l) tp t ->
  sls_has (embed_lens l) sp st.
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

Lemma closure_lift {E F U} (σ: strat E F ready):
  closure (σ@U) = (closure σ)@U.
Proof.
  apply antisymmetry.
  - intros s Hs. cbn - [slens_id] in *.
    dependent induction Hs.
    + exists pnil_ready, pnil_ready. firstorder eauto.
    + edestruct IHHs as (t1 & t2 & Ht1 & Ht2 & Ht3); eauto.
      cbn - [slens_id] in H. destruct H as (s1 & s2 & Hs1 & Hs2 & Hs3).
      exploit @seq_comp_tstrat; eauto.
      intros (st1 & st2 & Hst1 & Hst2 & Hst3).
      exists st1, st2. split; eauto. split; eauto.
      eapply lens_seq_comp; eauto.
  - intros s Hs. cbn - [slens_id] in *.
    edestruct Hs as (s1 & s2 & Hs1 & Hs2 & Hs3); eauto. clear Hs.
    revert s2 s Hs1 Hs3.
    (* Set Printing Implicit. cbn. *)
    generalize (@sls_ready U U (@slens_state U U (@slens_id U)) (@slens_init U U (@slens_id U))) as st.
    dependent induction Hs2; intros.
    + dependent destruction Hs1. eauto.
    + edestruct @tstrat_seq_comp as (xs1 & xs2 & st2 & fs1 & fs2 & HA & HB & HC & HD & HE); eauto.
      exploit IHHs2; eauto. intros Hc.
      eapply closure_has_cons; eauto.
      exists s, fs1. repeat apply conj; eauto. cbn - [slens_id] in *.
      dependent destruction st. cbn in *. destruct p. eauto.
Qed.

(* XXX: move to IntStrat.v *)
Global Instance compose_when_monotonic {E F G i j k p}:
  Monotonic (@compose_when E F G i j k p) (ref ++> ref ++> ref).
Admitted.

Global Instance fcomp_when_monotonic {E1 E2 F1 F2 i1 i2 i p}:
  Monotonic (@fcomp_when E1 E2 F1 F2 i1 i2 i p) (ref ++> ref ++> ref).
Admitted.

Global Instance fcomp_params : Params (@fcomp_when) 2 := { }.

Lemma vcomp_assoc {E F G H} (σ: conv E F) (τ: conv F G) (υ: conv G H):
  vcomp (vcomp σ τ) υ = vcomp σ (vcomp τ υ).
Admitted.

(* XXX: move to IntStrat.v *)
Lemma rsq_id_conv {E F i} p (σ τ: strat E F i):
  rsq_when vid vid p σ τ <-> σ [= τ.
Admitted.

Lemma rsq_id_strat {E F} p (R S: conv E F):
  rsq_when S R p (id E) (id F) <-> R [= S.
Admitted.

Global Instance compose_params : Params (@compose_when) 2 := { }.

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
  compose_when p (sup i:I, σ i) τ = sup i:I, compose_when p (σ i) τ.
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

Global Hint Constructors tstrat_has id_has: core.

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
