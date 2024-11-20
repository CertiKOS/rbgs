Require Import Classical.
Require Import Program.Equality.
Require Import LogicalRelations.
Require Import Poset.
Require Import Lattice.
Require Import Downset.
Require Import IntStrat.
Require Import Classical_Prop.
Require Import Coqlib.
Require Import CompCertStrat.
(* From compcert Require Import Smallstep Globalenvs. *)
(* Require LanguageInterface. *)
(* Import -(notations) LanguageInterface. *)

(* ------------------------------------------------------------------- *)
(** ** Various miscellaneous properties *)

Program Definition E0_conv {E} : conv 0 E := {| Downset.has s := False |}.

Lemma E0_conv_vcomp {E F} (R: conv E F): E0_conv = vcomp E0_conv R.
Proof.
  apply antisymmetry.
  - intros x Hx. xinv Hx.
  - intros x Hx. cbn in *. destruct x; xinv Hx; easy.
Qed.

Global Instance E0_conv_regular {E}:
  RegularConv (@E0_conv E).
Proof. split. intros. easy. Qed.

Global Hint Constructors rsp : core.
Global Hint Constructors pcoh : core.

Global Instance emor_determinisitc {E F} f i p:
  Deterministic (@emor_when E F f i p).
Proof.
  split. intros s t Hs Ht. cbn in *. revert Ht. induction Hs; eauto.
  - intros. dependent destruction Ht; eauto.
    destruct (classic (q = q0)); eauto. subst. eauto.
  - intros. dependent destruction Ht; eauto.
    destruct (classic (r = r0)); eauto. subst. eauto.
Qed.

Global Instance scomp_deterministic {E F U V}
  i1 i2 i (σ: strat E F _) (l: bijection U V) (tp: tpos i1 i2 i) lp:
  Deterministic σ ->
  Deterministic (tstrat_when tp σ (lens_strat_when l lp)).
Proof.
  intros Hd. split. cbn.
  intros s t (s1 & s2 & Hs & Hs1 & Hs2) (t1 & t2 & Ht & Ht1 & Ht2).
  destruct Hd as [Hd]. specialize (Hd _ _ Hs1 Ht1).
  clear σ Hs1 Ht1. revert lp t1 t2 t Hd Ht Hs2 Ht2.
  dependent induction Hs; intros; eauto.
  - dependent destruction Hd.
    + dependent destruction Ht. eauto.
    + dependent destruction Ht.
      dependent destruction Hs2. dependent destruction Ht2.
      destruct (classic (q2 = q3)).
      * subst. eauto.
      * apply pcons_pcoh_oq. congruence.
    + dependent destruction Ht.
      apply pcons_pcoh_oq. congruence.
  - dependent destruction Hd. dependent destruction Ht.
    dependent destruction Hs2. dependent destruction Ht2.
    eauto.
  - dependent destruction Hd.
    + dependent destruction Ht. eauto.
    + dependent destruction Ht.
      dependent destruction Hs2. dependent destruction Ht2.
      destruct (classic (n2 = n3)).
      * subst. eauto.
      * apply pcons_pcoh_oa. congruence.
    + dependent destruction Ht.
      apply pcons_pcoh_oa. congruence.
  - dependent destruction Hd. dependent destruction Ht.
    dependent destruction Hs2. dependent destruction Ht2.
    eauto.
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

Lemma rcnext_lcj_encap {U} (u1 u2: U) :
  rcnext tt u1 tt u2 (lcj (encap u1)) = lcj (encap u2).
Proof.
  apply antisymmetry; intros s; cbn.
  - intros [H H']. eauto.
  - intros Hs. split; auto. intros ? ?.
    inv H. red. red in Hs. cbn in *.
    eauto.
Qed.

(* XXX: move to IntStrat.v *)
Section ENCAP.
  Obligation Tactic := cbn.
  Context {U: Type} (u0 : U).

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
      intros E x y H1. revert u0; induction H1; intros u0 Hx;
        try solve [ dependent destruction Hx; eauto ]; eauto.
      - simple inversion Hx; try congruence. subst.
        apply rcp_cont_inv in H0 as (A & B & C & D & K).
        subst. xsubst. intros HX. constructor.
      - simple inversion Hx; try congruence. subst.
        apply rcp_forbid_inv in H1 as (A & B & C & D).
        subst. xsubst. intros. constructor.
      - simple inversion Hx; try congruence; subst.
        apply rcp_cont_inv in H0 as (A & B & C & D & K).
        subst. xsubst. intros. constructor. eauto.
      - simple inversion Hx; try congruence; subst.
        apply rcp_forbid_inv in H1 as (A & B & C & D).
        subst. xsubst. intros. constructor. intros. easy.
  Qed.

  Definition de' {E:esig}: E <=> E @ U := trur ;; E @ (lcj (IntStrat.encap u0)).

  Hint Constructors emor_rc_has : core.

  Lemma de_eq {E}: @de E = de'.
  Proof.
    apply antisymmetry.
    - intros x Hx. cbn in *. revert u0 Hx. induction x; intros; cbn.
      + dependent destruction Hx.
        exists (m1, tt). repeat apply conj; eauto.
        apply (emor_rc_allow trur (m1, tt)).
        apply (emor_rc_allow eid m1).
      + destruct m2 as (m2 & u1).
        destruct n2 as (n2 & u2). cbn in *.
        simple inversion Hx; try congruence.
        apply rcp_forbid_inv in H1 as (A & B & C & D).
        subst. inv B. xsubst. inv D. intros Hn.
        exists (m2, tt). repeat apply conj; eauto.
        apply (emor_rc_allow trur (m2, tt)).
        apply (emor_rc_allow eid m2). cbn in *.
        intros [n3 []].
        destruct (classic (n1 = n3)).
        * subst. right. split. apply (emor_rc_allow eid m2). split; eauto.
          left. apply (emor_rc_forbid eid m2 n3 n2). eauto.
        * left. apply (emor_rc_forbid trur (m2, tt) _ _).
          cbn. congruence.
      + destruct m2 as (m2 & u1).
        destruct n2 as (n2 & u2). cbn in *.
        simple inversion Hx; try congruence; subst.
        apply rcp_cont_inv in H0 as (A & B & C & D & K).
        subst. inv B. xsubst. inv D. intros.
        exists (m2, tt). repeat apply conj; eauto.
        apply (emor_rc_allow trur (m2, tt)).
        apply (emor_rc_allow eid m2). cbn in *.
        intros [n3 []].
        destruct (classic (n1 = n3)).
        * subst. right. destruct (classic (n2 = n3)).
          -- subst. right. exploit IHx; eauto. intros IH.
             setoid_rewrite (rcnext_emor trur (m2, tt) n3).
             setoid_rewrite rcnext_tconv.
             ++ setoid_rewrite (rcnext_emor eid m2 n3).
                unfold scomp_conv in IH.
                setoid_rewrite (rcnext_lcj_encap u1 u2); eauto.
             ++ intros A. cbn in A. dependent destruction A. eauto.
             ++ intros [? A]. eapply A. reflexivity.
          -- left. repeat apply conj; eauto.
             apply (emor_rc_allow eid m2).
             left. apply (emor_rc_forbid eid m2 n3 n2). eauto.
        * left. apply (emor_rc_forbid trur (m2, tt) _ _).
          cbn. congruence.
    - intros x. unfold de'. cbn. revert u0.
      induction x; intros; cbn in *.
      + destruct m2 as (m2 & u1). destruct H as ((m3 & tt) & A1 & A2 & ->).
        dependent destruction A1. dependent destruction A2. econstructor.
      + destruct m2 as (m2 & u1). destruct n2 as (n2 & u2).
        destruct H as ((m3 & []) & A1 & (A2 & <-) & A3).
        dependent destruction A1. dependent destruction A2. cbn in *.
        econstructor. intros <-.
        specialize (A3 (n1, tt)) as [A3 | A3].
        * dependent destruction A3. apply H. eauto.
        * destruct A3 as (A1 & A2 & [A3|(A3 & A4)]).
          -- dependent destruction A3. apply H. eauto.
          -- apply (A4 u2). eauto.
      + destruct m2 as (m2 & u1). destruct n2 as (n2 & u2).
        destruct H as ((m3 & []) & A1 & (A2 & <-) & A3).
        dependent destruction A1. dependent destruction A2. cbn in *.
        econstructor. intros <-. apply IHx. clear IHx.
        specialize (A3 (n1, tt)) as [A3 | A3].
        * dependent destruction A3. exfalso. apply H; eauto.
        * destruct A3 as [A3|A3].
          -- exfalso. destruct A3 as (?&?&A3).
             destruct A3 as [A3|A3].
             ++ dependent destruction A3. eauto.
             ++ destruct A3. apply (H2 u2); eauto.
          -- setoid_rewrite (rcnext_emor trur (m3, tt) n1) in A3.
             setoid_rewrite rcnext_tconv in A3.
             ++ setoid_rewrite (rcnext_emor eid m3 n1) in A3.
                unfold scomp_conv.
                setoid_rewrite (rcnext_lcj_encap u0 u2) in A3; eauto.
             ++ intros A. cbn in A. dependent destruction A. eauto.
             ++ intros [? A]. cbn in A. eapply A. reflexivity.
  Qed.

  Definition deencap {E F} (R: conv E F) : conv E (F@U) := R ;; de.

  Definition e {E:esig} : E @ U ->> E := sru ⊙ (E @ (IntStrat.encap u0)).
  Definition encap {E F} (σ: strat E (F@U) ready) := e ⊙ σ.

End ENCAP.

Global Hint Constructors tstrat_has lens_has: core.

Lemma lsq_id_lcj {U V: Type} i1 i2 (rp: rspos i1 i2)  (f: U ~>> V)
  (lp1 lp2: lpos lid _) (st1 st2: IntStrat.state f):
  match lp1, lp2 with
   | lready _ _, lready _ _ => st1 = st2
   | lrunning _ _ u1 u2, lrunning _ _ v1 v2 =>
       IntStrat.get f (st2, u1) = v1 /\
       IntStrat.get f (st1, u2) = v2 /\ IntStrat.set f (st2, u1) v2 = (st1, u2)
   | lsuspended _ _ u1 u2, lsuspended _ _ v1 v2 =>
       IntStrat.get f (st2, u1) = v1 /\
       IntStrat.get f (st1, u2) = v2 /\ IntStrat.set f (st2, u1) v2 = (st1, u2)
   | _, _ => False end ->
  rsq_when (lcj_when f st1) (lcj_when f st2) rp
    (lens_strat_when lid lp1) (lens_strat_when lid lp2).
Proof.
  intros Hp c Hc. cbn in Hc. revert i2 lp2 st1 st2 Hp rp.
  dependent induction Hc; intros; dependent destruction rp; eauto.
  - dependent destruction lp2. apply rsp_ready. cbn. eauto.
  - dependent destruction lp2. subst.
    apply rsp_oq. cbn. eauto.
    intros q2 Hq2. cbn in Hq2.
    setoid_rewrite lens_strat_next_oq; eauto.
    eapply IHHc. split; cbn; eauto.
    subst. rewrite set_get. easy.
  - dependent destruction lp2. destruct p0.
    eapply rsp_pq. cbn. apply Hp.
    setoid_rewrite lens_strat_next_pq; eauto.
  - dependent destruction lp2. apply rsp_suspended. cbn. eauto.
  - dependent destruction lp2. destruct p0.
    destruct Hp as (Hp1 & Hp2 & Hp3).
    eapply rsp_oa. cbn; eauto.
    intros n2 Hn2. cbn in Hn2.
    apply not_and_or in Hn2 as [Hn2|Hn2]. easy.
    apply not_all_ex_not in Hn2 as [st3 Hst].
    apply NNPP in Hst.
    setoid_rewrite lens_strat_next_oa; eauto.
    setoid_rewrite rcnext_lcj; eauto. apply IHHc.
    repeat split.
    + subst. eauto.
    + setoid_rewrite <- Hst. apply get_set.
    + subst. setoid_rewrite <- Hp3 in Hst.
      rewrite set_set in Hst. eauto.
  - dependent destruction lp2. destruct p0. cbn in H. inv H.
    destruct Hp as (Hp1 & Hp2 & Hp3).
    eapply rsp_pa. cbn; eauto.
    intros [HX1 HX2]. eapply HX2. eauto.
    setoid_rewrite lens_strat_next_pa; eauto. 2: cbn; eauto.
    setoid_rewrite rcnext_lcj; eauto.
Qed.

Lemma lsq_de {U: Type} (u0: U):
  lsq (lcj (IntStrat.encap u0)) (lcj (IntStrat.encap u0)) lid lid.
Proof. apply lsq_id_lcj. reflexivity. Qed.

Lemma tru_rsq {F}: rsq vid trur (@sru F) (id (F @ _)).
Proof.
  pose proof (emor_strat_intro (@trur F)) as A.
  assert (rsq vid vid (@tru F) tru) as B.
  { apply rsq_id_conv. reflexivity. }
  pose proof (rsq_comp _ _ _ _ _ _ _ A B) as C.
  rewrite compose_id_l in C.
  setoid_rewrite (retraction srur) in C. apply C.
Qed.

(* The encapsulated strategy is refined by the original strategy using the
   "deencap" refinement convention.

   This should follow from the conjoint property.
   XXX: move to IntStrat.v *)
Lemma deencap_rsq {E F: esig} {S: Type} (σ: strat E (F@S) ready) (s0: S):
  rsq vid (de s0) (encap s0 σ) σ.
Proof.
  unfold encap. rewrite de_eq. unfold de'. unfold e.
  unfold sru.
  pose proof (lcj_elim (IntStrat.encap s0)) as A.
  rewrite <- (compose_id_l σ) at 2.
  eapply rsq_comp.
  2: apply rsq_id_conv; reflexivity.
  assert (rsq vid vid (id F) (id F)) as B.
  { apply rsq_id_conv; reflexivity. }
  pose proof (scomp_rsq _ _ _ _ _ _ _ _ B A) as C.
  rewrite scomp_id in C. rewrite scomp_vid in C.
  rewrite <- (compose_id_l (id (F @ S))).
  eapply rsq_comp. 2: apply C.
  rewrite <- (vcomp_vid_l (vid @ lcj (IntStrat.encap s0))).
  eapply rsq_vcomp. 3: apply tru_rsq.
  1-2: eauto with typeclass_instances.
  rewrite <- !scomp_id.
  eapply scomp_rsq.
  rewrite emor_rc_id. apply rsq_id_conv. reflexivity.
  apply lsq_de.
Qed.

Lemma id_scomp_comp {E F U V} (σ : E ->> F) (l : U ~>> V):
  id F @ l ⊙ σ @ lid = σ @ lid ⊙ id E @ l.
Proof.
  rewrite <- !scomp_compose.
  rewrite compose_id_l.
  rewrite compose_id_r.
  apply scomp_strat_eq.
  rewrite lcomp_lid_r. rewrite lcomp_lid_l. reflexivity.
Qed.

(* E@[s0> ⊙ σ@S ⊑ σ ⊙ E@[s0>
   XXX: move to IntStrat.v *)
Lemma encap_lift {E F} {S: Type} (σ: strat E F ready) (s0: S):
  (e s0) ⊙ (σ @ S) [= σ ⊙ (e s0).
Proof.
  unfold e. rewrite <- !compose_assoc.
  rewrite sru_natural.
  rewrite !compose_assoc.
  apply compose_when_monotonic. reflexivity.
  rewrite id_scomp_comp. reflexivity.
Qed.

(* R s0 t0 → E@[s0> ⊑_{E@R → 1} E@[t0> *)
Lemma representation_independence {E} {S T: Type} (R: rel S T) s t:
  R s t -> rsq (tconv (@vid E) R) vid (e s) (e t).
Proof.
  intros HR. unfold e. eapply rsq_comp.
  apply rsq_id_conv. reflexivity.
  rewrite <- scomp_vid.
  eapply scomp_rsq. apply rsq_id_conv. reflexivity.
  apply representation_independence0. eauto.
Qed.

Lemma rsq_trur {E F} (τ: E ->> F): rsq trur trur τ (τ @ lid).
Proof.
  pose proof (emor_strat_elim (@trur E)) as A.
  assert (rsq vid vid (@tru E) tru) as B.
  { apply rsq_id_conv. reflexivity. }
  assert (rsq vid vid τ τ) as C.
  { apply rsq_id_conv. reflexivity. }
  pose proof (emor_strat_intro (@trur F)) as D.
  pose proof (rsq_comp _ _ _ _ _ _ _ B A) as H1.
  pose proof (rsq_comp _ _ _ _ _ _ _ C H1) as H2.
  pose proof (rsq_comp _ _ _ _ _ _ _ D H2) as H3.
  clear - H3.
  rewrite compose_id_l in H3.
  rewrite (retraction tru) in H3.
  rewrite !compose_id_r in H3.
  rewrite <- compose_assoc in H3.
  setoid_rewrite  sru_natural in H3.
  assert ((trur ⊙ τ) @ lid = (@trur (F * 1)) ⊙ τ @ lid) as A.
  {
    rewrite <- lcomp_lid_r at 1.
    rewrite scomp_compose.
    f_equal.
    pose proof (srur_natural (@trur F)).
    assert (srur ⊙ trur ⊙ (@sru F)  = trur @ lid ⊙ srur ⊙ sru).
    rewrite <- !compose_assoc. f_equal. apply H.
    setoid_rewrite (retraction srur) in H0.
    rewrite !compose_id_r in H0. symmetry. apply H0.
  }
  rewrite A in H3.
  rewrite <- compose_assoc in H3.
  setoid_rewrite (retraction tru) in H3.
  rewrite compose_id_l in H3.
  apply H3.
Qed.

Lemma rsq_de {E F U} (τ: strat E F ready) (u0: U) :
  Deterministic τ ->
  rsq (de u0) (de u0) τ (τ @ U).
Proof.
  intros Ht. rewrite !de_eq. unfold de'.
  eapply rsq_vcomp.
  3: apply rsq_trur.
  3: {
    eapply scomp_rsq. 2: apply lsq_de.
    rewrite !emor_rc_id.
    apply rsq_id_conv. reflexivity.
  }
  all: eauto with typeclass_instances.
Qed.

Lemma tstrat_sup_l {I} {E1 E2 F1 F2 i1 i2 i} (p: tpos i1 i2 i)
  (σ: I -> strat E1 F1 i1) (τ: strat E2 F2 i2) :
  tstrat_when p (sup i:I, σ i) τ = sup i:I, tstrat_when p (σ i) τ.
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
