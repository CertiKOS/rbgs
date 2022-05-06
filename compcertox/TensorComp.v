From Coq Require Import
     Relations RelationClasses
     List FinFun.
From compcertox Require Import
     Lifting AbRel.
From compcert.lib Require Import
     Coqlib.
From compcert.common Require Import
     LanguageInterface Events
     Globalenvs Smallstep
     Linking Memory Values
     CallconvAlgebra
     CategoricalComp
     FlatComp.

Generalizable All Variables.
Close Scope Z_scope.

(* A li_func convert from one language interface to another. This is useful
   because equivalence on the level of language interfaces can't be defined
   as definitional equality. *)
Record li_func (liA liB: language_interface) :=
  mk_li_func {
      query_func: query liB -> query liA;
      reply_func: reply liB -> reply liA;
    }.
Arguments query_func {liA liB} _ _.
Arguments reply_func {liA liB} _ _.

Class LiSurjective {liA liB} (F: li_func liA liB) :=
  LiSurj: Surjective (query_func F) /\ Surjective (reply_func F).

Arguments LiSurjective {_ _} _.

Section APPLY.

  Context {liA1 liA2 liB1 liB2 S} (L: lts liA1 liB1 S)
          (FA: li_func liA1 liA2) (FB: li_func liB1 liB2).

  Definition lts_map: lts liA2 liB2 S :=
    {|
      genvtype := genvtype L;
      globalenv := globalenv L;
      step := step L;
      initial_state q s := initial_state L (query_func FB q) s;
      at_external s q := at_external L s (query_func FA q);
      after_external s r s' := after_external L s (reply_func FA r) s';
      final_state s r := final_state L s (reply_func FB r);
    |}.

End APPLY.

Definition semantics_map {liA1 liA2 liB1 liB2} (L: semantics liA1 liB1) F G: semantics liA2 liB2 :=
  {|
    skel := skel L;
    activate se := lts_map (L se) F G;
    footprint := footprint L;
  |}.

Definition map_monotonicity {liA1 liA2 liB1 liB2} L1 L2 (F: li_func liA1 liA2) (G: li_func liB1 liB2):
  L1 ≤ L2 -> semantics_map L1 F G ≤ semantics_map L2 F G.
Proof.
  intros [[]]. constructor. econstructor; eauto.
  instantiate (1 := fsim_match_states).
  intros. exploit fsim_lts; eauto. clear. intros HL.
  constructor.
  - intros q1 q2 s1 Hq H. inv Hq.
    edestruct @fsim_match_initial_states as (idx & s2 & Hs2 & Hs); eauto.
    reflexivity. apply H.
    eexists _, _. split. apply Hs2. apply Hs.
  - intros idx s1 s2 r Hs H.
    edestruct @fsim_match_final_states as (r2 & Hr2 & Hr); eauto.
    apply H. inv Hr. eexists. split.
    apply Hr2. reflexivity.
  - intros idx s1 s2 q1 Hs Ht. exists tt.
    edestruct @fsim_match_external as (wx & qx2 & Hqx2 & Hqx & Hsex & H); eauto. apply Ht.
    inv Hqx. inv Hsex. exists q1; repeat apply conj; try constructor. apply Hqx2.
    intros r1 ? ? [ ] He. edestruct H as (idx' & s2' & Hs2' & Hs'); eauto. reflexivity.
    apply He. eexists _, _. split. apply Hs2'. apply Hs'.
  - intros. edestruct @fsim_simulation as (idx' & s2' & Hs2' & Hs'); eauto.
Qed.

Definition id_li_func {liA} := mk_li_func liA liA id id.

Definition mapA {liA1 liA2 liB} (L: semantics liA1 liB) (F: li_func liA1 liA2) := semantics_map L F id_li_func.
Notation "F >> L" := (mapA L F) (at level 50): lts_scope.

Lemma mapA_monotonicity {liA1 liA2 liB} (L1 L2: semantics liA1 liB) (F: li_func liA1 liA2):
  L1 ≤ L2 -> F >> L1 ≤ F >> L2.
Proof. apply map_monotonicity. Qed.

Definition mapB {liA liB1 liB2} (L: semantics liA liB1) (F: li_func liB1 liB2) := semantics_map L id_li_func F.
Notation "L << F" := (mapB L F) (at level 50): lts_scope.

Lemma mapB_monotonicity {liA liB1 liB2} (L1 L2: semantics liA liB1) (F: li_func liB1 liB2):
  L1 ≤ L2 -> L1 << F ≤ L2 << F.
Proof. apply map_monotonicity. Qed.

Definition map_both {li1 li2} (L: semantics li1 li1) (F: li_func li1 li2) := semantics_map L F F.
Notation "F $$ L" := (map_both L F) (at level 50): lts_scope.
Lemma map_both_monotonicity {liA1 liA2} (L1 L2: semantics liA1 liA1) (F: li_func liA1 liA2):
  L1 ≤ L2 -> map_both L1 F ≤ map_both L2 F.
Proof. apply map_monotonicity. Qed.


Section MAPA_COMP.
  Context {liA1 liA2 liB liC} (L1: semantics liB liC) (L2: semantics liA1 liB) (F: li_func liA1 liA2).

  Inductive mapA_ms : comp_state L1 L2 -> comp_state L1 (F >> L2) -> Prop :=
  | mapA_ms1 s: mapA_ms (st1 _ _ s) (st1 _ _ s)
  | mapA_ms2 s1 s2: mapA_ms (st2 _ _ s1 s2) (st2 _ (F >> L2) s1 s2).

  Lemma mapA_comp sk: F >> (comp_semantics' L1 L2 sk) ≤ comp_semantics' L1 (F >> L2) sk.
  Proof.
    constructor. econstructor; eauto. intros i. reflexivity.
    intros se _ [ ] [ ] _. instantiate (1 := fun _ _ _ => _). cbn beta.
    eapply forward_simulation_step with (match_states := mapA_ms);
      cbn; intros; subst; unfold id in *.
    - inv H0. eexists; split; constructor. auto.
    - inv H0; inv H. eexists; split; constructor; auto.
    - inv H0; inv H. eexists _, _. intuition eauto.
      constructor; auto. subst. inv H0. eexists; split; constructor. auto.
    - inv H; inv H0; eexists; split;
        [ apply step1 | | apply step2 | | eapply step_push | | eapply step_pop |  ]; repeat constructor; eauto.
    - apply well_founded_ltof.
      Unshelve. exact tt.
  Qed.
End MAPA_COMP.

Section MAPB_COMP.

  Context {liA liB1 liB2} (L1: semantics liB1 liB1) (L2: semantics liA liB1) (F: li_func liB1 liB2).

  Inductive mapB_ms : comp_state L1 L2 -> comp_state (F $$ L1) (L2 << F) -> Prop :=
  | mapB_ms1 s: mapB_ms (st1 _ _ s) (st1 (F $$ L1) _ s)
  | mapB_ms2 s1 s2: mapB_ms (st2 _ _ s1 s2) (st2 (F $$ L1) (L2 << F) s1 s2).

  Context `{HS: !LiSurjective F}.

  Lemma mapB_comp' sk: (comp_semantics' L1 L2 sk) << F ≤ comp_semantics' (F $$ L1) (L2 << F) sk.
  Proof.
    constructor. econstructor; eauto. intros i. reflexivity.
    intros se _ [ ] [ ] _. instantiate (1 := fun _ _ _ => _). cbn beta.
    eapply forward_simulation_step with (match_states := mapB_ms);
      cbn; intros; subst; unfold id in *.
    - inv H0. eexists; split; constructor. auto.
    - inv H0; inv H. eexists; split; constructor; auto.
    - inv H0; inv H. eexists _, _. intuition eauto.
      constructor; auto. subst. inv H0. eexists; split; constructor. auto.
    - inv H; inv H0; eexists; (split; [ |constructor]).
      + apply step1. apply H1.
      + apply step2. apply H1.
      + specialize ((proj1 HS) q) as [q' Hq']. subst.
        eapply step_push. apply H1. apply H2.
      + specialize ((proj2 HS) r) as [r' Hr']. subst.
        eapply step_pop. apply H1. apply H2.
    - apply well_founded_ltof.
      Unshelve. exact tt.
  Qed.

End MAPB_COMP.

Program Definition li_func_null {K}: li_func (li_null @ K) li_null :=
  {|
    query_func q := match q with end;
    reply_func r := match r with end;
  |}.

Program Definition li_func_k {li K1 K2}: li_func ((li@K1)@K2) (li@(K1*K2)) :=
  {|
    query_func '(q, k) := ((q, fst k), snd k);
    reply_func '(r, k) := ((r, fst k), snd k);
  |}.

Instance li_func_k_surj {li K1 K2}: LiSurjective (@li_func_k li K1 K2).
Proof.
  split; intros [[x k1] k2]; exists (x, (k1, k2)); reflexivity.
Qed.

Program Definition li_func_comm {li K1 K2}: li_func (li@(K1*K2)) (li@(K2*K1)) :=
  {|
    query_func '(q, (k1, k2)) := (q, (k2, k1));
    reply_func '(r, (k1, k2)) := (r, (k2, k1));
  |}.

Instance li_func_comm_surj {li K1 K2}: LiSurjective (@li_func_comm li K1 K2).
Proof.
  split; intros [x [k1 k2]]; exists (x, (k2, k1)); reflexivity.
Qed.

Definition lift_layer {li K} (L: semantics li_null li): semantics li_null (li@K) :=
  li_func_null >> L@K.

Definition lift_layer_k {li K1 K2} (L: semantics li_null (li@K1)): semantics li_null (li@(K1*K2)) :=
  li_func_null >> L@K2 << li_func_k.

Definition layer_comm {li K1 K2} (L: semantics li_null (li@(K2*K1))): semantics li_null (li@(K1*K2)) :=
  L << li_func_comm.

Definition lts_comm {li K1 K2} (L: semantics (li@(K2*K1)) (li@(K2*K1))): semantics (li@(K1*K2)) (li@(K1*K2)) :=
   li_func_comm $$ L.

(** Some simple properties about the product of abstraction relations *)
Section Properties.

  Local Open Scope abrel_scope.

  Context {Ks1 Ks2 Kf1 Kf2} (R1: abrel Ks1 Kf1) (R2: abrel Ks2 Kf2).
  Hypothesis HR: disjoint_abrel R1 R2.
(*
  Lemma prod_match_reply se m1 m2 r1 r2 k1 k2 k3 k4:
    match_reply R1 (mkrelw se (m1, m2)) (r1, k1) (r2, k2) ->
    Rk R2 k3 k4 -> Rr R2 se k3 m2 ->
    no_perm_on m1 (blocks R2 se) -> Mem.extends m1 m2 ->
    match_reply (R1 * R2) (mkrelw se (m1, m2)) (r1, (k1, k3)) (r2, (k2, k4)).
  Proof.
    intros [w' [Hw Hr]] Hk Hkm Hperm Hm.
    exists w'; inv Hw; split.
    - cbn in *.  constructor; eauto.
      eapply Mem.unchanged_on_implies; eauto.
      cbn in *. intros. eapply other_blocks_implies; eauto.
      intros. now left.
    - inv Hr. cbn in *. constructor; eauto.
      + intros b ofs Hb. apply blocks_either in Hb as [Hv|Hv].
        * unfold no_perm_on in *. intuition eauto.
        * unfold no_perm_on in *. intros contra.
          specialize (Hperm b ofs Hv). apply Hperm.
          eapply Mem.perm_unchanged_on_2; intuition eauto.
          destruct Hv as [v [Hv Hb]]. eexists; eauto.
          apply Mem.perm_valid_block in contra.
          erewrite Mem.valid_block_extends; [ | eauto].
          eapply (G_valid R2); eauto.
      + split; eauto. eapply G_unchanged; eauto.
        eapply Mem.unchanged_on_implies. intuition eauto.
        cbn. intros. destruct H as [v [Hv Hb]]. eexists; split; eauto.
        unfold others. intros contra. eapply Hdisjoint; eauto.
      + split; eauto.
  Qed.

  Lemma prod_match_query se m1 m2 q1 q2 k1 k2 k3 k4:
    match_query (R1 * R2) (mkrelw se (m1, m2)) (q1, (k1, k3)) (q2, (k2, k4)) ->
    match_query R1 (mkrelw se (m1, m2)) (q1, k1) (q2, k2) /\ Rk R2 k3 k4 /\ Rr R2 se k3 m2 /\
    no_perm_on m1 (blocks R2 se) /\ Mem.extends m1 m2.
  Proof.
    intros. inv H. repeat apply conj; cbn in *; intuition.
    constructor; eauto.
    - intros b ofs Hg. apply H11. eapply blocks_implies. eauto.
      intuition. now left.
    - intros b ofs Hg. apply H11. eapply blocks_implies. eauto.
      intuition. now right.
  Qed.
*)
  Lemma match_query_comm w qs qf ks1 kf1 ks2 kf2:
    match_query (R2 * R1) w (qs, (ks2, ks1)) (qf, (kf2, kf1)) ->
    match_query (R1 * R2) w (qs, (ks1, ks2)) (qf, (kf1, kf2)).
  Proof.
    intros. inv H. constructor; auto.
    - intros b ofs Hg. apply MPERM.
      cbn in *. rewrite -> locsp_app in Hg |- *.
      now apply or_comm.
    - cbn in *. intuition.
  Qed.

  Lemma match_reply_comm w rs rf ks1 kf1 ks2 kf2:
    match_reply (R2 * R1) w (rs, (ks2, ks1)) (rf, (kf2, kf1)) ->
    match_reply (R1 * R2) w (rs, (ks1, ks2)) (rf, (kf1, kf2)).
  Proof.
    intros [w' [Hw H]]. exists w'. inv Hw. inv H. split.
    - cbn in *. constructor; eauto.
      eapply Mem.unchanged_on_implies; eauto.
      cbn. intros * (A & B) V. split; eauto.
      intros X. apply B. rewrite locsp_app in *. intuition.
    - econstructor; eauto.
      + cbn in *. intros * V. apply MPERM.
        rewrite locsp_app in *. intuition.
      + cbn in *. intuition.
  Qed.

End Properties.

Lemma layer_comm_simulation `(R1: abrel Ks1 Kf1) `(R2: abrel Ks2 Kf2) L1 L2:
  forward_simulation 1 (R1 * R2)%abrel L1 L2 ->
  forward_simulation 1 (R2 * R1)%abrel (layer_comm L1) (layer_comm L2).
Proof.
  intros [[]]. constructor. econstructor; eauto.
  instantiate (1 := fsim_match_states).
  intros. exploit fsim_lts; eauto. clear. intros HL.
  constructor.
  - intros [q1 [k3 k1]] [q [k4 k2]] s1 Hq H.
    edestruct @fsim_match_initial_states as (idx & s2 & Hs2 & Hs); eauto.
    apply match_query_comm; eauto. apply H.
    eexists _, _. split. apply Hs2. apply Hs.
  - intros idx s1 s2 [r [k3 k1]] Hs H.
    edestruct @fsim_match_final_states as (r2 & Hr2 & Hr); eauto.
    apply H. destruct r2 as [r2 [k2 k4]].
    eexists (_, (_, _)). split. apply Hr2.
    apply match_reply_comm. apply Hr.
  - intros ? ? ? [ ].
  - intros. edestruct @fsim_simulation as (idx' & s2' & Hs2' & Hs'); eauto.
Qed.

Ltac prod_crush :=
  repeat
    (match goal with
     | [ H: ?a * ?b |- _ ] => destruct H;cbn [fst snd] in *; subst
     | [ H: (?a, ?b) = (?c, ?d) |- _ ] => inv H
     | [ H: (?x * ?y)%rel _ _ |- _] => destruct H; cbn [fst snd] in *; subst
     | [ H: ?x /\ ?y |- _] => destruct H
  end).

Section LIFT_ASSOC.
  Context (K1 K2: Type) {li} (L: semantics li li).
  Inductive assoc_match: (state L * K1) * K2 -> state L * (K1 * K2) -> Prop :=
  | assoc_match_intro s k1 k2: assoc_match ((s, k1), k2) (s, (k1, k2)).

  Lemma lts_lifting_assoc: li_func_k $$ (L @ K1) @ K2 ≤ L @ (K1 * K2).
  Proof.
    constructor. econstructor; eauto. intros i. reflexivity.
    intros se _ [ ] [ ] _. instantiate (1 := fun _ _ _ => _). cbn beta.
    eapply forward_simulation_step with (match_states := assoc_match);
      cbn; intros; prod_crush.
    - eexists; split; [ | constructor ]. split; auto.
    - inv H. eexists; split; [ | constructor ]. split; auto.
    - inv H. eexists tt, _. intuition eauto. split; auto.
      prod_crush. eexists; split; [ | constructor ]. split; auto.
    - inv H0. eexists (_, (_, _)). split; [ | constructor ]. split; auto.
    - apply well_founded_ltof.
  Qed.

End LIFT_ASSOC.

Section LIFT_COMM.
  Context  (K1 K2: Type) {li} (L: semantics li li).

  Inductive comm_match: state L * (K1 * K2) -> state L * (K2 * K1) -> Prop :=
  | comm_match_intro s k1 k2: comm_match (s, (k1, k2)) (s, (k2, k1)).

  Lemma lts_lifting_comm: li_func_comm $$ L @ (K1 * K2) ≤ L @ (K2 * K1).
  Proof.
    constructor. econstructor; eauto. intros i. reflexivity.
    intros se _ [ ] [ ] _. instantiate (1 := fun _ _ _ => _). cbn beta.
    eapply forward_simulation_step with (match_states := comm_match);
      cbn; intros; prod_crush.
    - eexists; split; [ | constructor ]. split; auto.
    - inv H. eexists; split; [ | constructor ]. split; auto.
    - inv H. eexists tt, _. intuition eauto. split; auto.
      prod_crush. eexists; split; [ | constructor ]. split; auto.
    - inv H0. eexists (_, (_, _)). split; [ | constructor ]. split; auto.
    - apply well_founded_ltof.
  Qed.
End LIFT_COMM.

(* TODO: generalize layer to LTS *)
Section TENSOR.

  Open Scope abrel_scope.
  Context {Ks1 Kf1} (Ls: semantics li_null (li_c@Ks1)) (Lf: semantics li_null (li_c@Kf1)).
  Context {Ks2 Kf2} (R1: abrel Ks1 Kf1) (R2: abrel Ks2 Kf2).
  Context (HL: fsim_components 1 R1 Ls Lf).
  Context (se1 se2: Genv.symtbl) (w : ccworld (R1 * R2)).
  Context (Hse: match_senv (R1 * R2) w se1 se2).
  Context (Hse1: Genv.valid_for (skel Ls) se1).

  Hypothesis HR: disjoint_abrel R1 R2.

  Inductive state_match: fsim_index HL -> state Ls * Ks2 -> state Lf * Kf2 -> Prop :=
  | lift_state_match i ss ks2 sf kf2 se ms mf:
      w = mk_aw se ms mf ->
      fsim_match_states HL se1 se2 w i ss sf ->
      R2 se ks2 (mf, kf2) ->
      (forall b ofs, locsp se (abrel_footprint R2) b ofs -> loc_out_of_bounds ms b ofs) ->
      Mem.extends ms mf ->
      state_match i (ss, ks2) (sf, kf2).

  Lemma lift_layer_semantics_simulation:
    fsim_properties 1 (R1 * R2) se1 se2 w
                    (lift_layer_k Ls se1) (lift_layer_k Lf se2)
                    (fsim_index HL) (fsim_order HL) state_match.
  Proof.
    destruct w as [se ms mf] eqn: Hw.
    assert (HSE: match_senv R1 w se se). { subst. constructor; eauto. }
    inv Hse. pose proof (fsim_lts HL _ _ HSE Hse1) as X.
    clear HSE Hse1.
    split; cbn.
    - intros [qs [ks1 ks2]] [qf [kf1 kf2]] [ss ks1'] Hq [HX Hks]; cbn in *.
      subst ks1'. inversion Hq.  destruct ABS as [HR1 HR2].
      edestruct @fsim_match_initial_states as (idx & sf & Hsf & Hs); eauto.
      (* match_query R1 *)
      + subst. constructor; eauto.
        intros * A. apply MPERM. cbn. rewrite locsp_app. now left.
      (* initial state & match_state *)
      + exists idx, (sf, kf2). split. split; auto.
        (* initial_state *)
        * subst. eauto.
        (* match_state *)
        * econstructor; eauto. subst. eauto.
          intros * A. apply MPERM. cbn. rewrite locsp_app. now right.
    - intros idx [ss ks2] [sf kf2] [rs [ks1 ks2']] Hs [HX Hks].
      inv Hs. cbn [fst snd] in *. subst.
      edestruct @fsim_match_final_states as (rf & Hrf & Hr); eauto.
      destruct rf as [rf kf1].
      eexists (_, (_, _)). split. split; cbn; eauto.
      inv H4. destruct Hr as (w & Hw & Hr).
      exists w; split; eauto.
      (* acc *)
      + inv Hw. constructor; eauto.
        eapply Mem.unchanged_on_implies; eauto.
        intros * (A & B) V. split; eauto.
        intros * C. apply B. cbn. rewrite locsp_app. now left.
      (* match_reply *)
      + inv Hw. inv Hr. constructor; eauto.
        * cbn. intros *. rewrite locsp_app. intros [A|A]; eauto.
          exploit Mem.unchanged_on_perm. exact ACCMS.
          eapply H8; exact A.
          eapply Mem.valid_block_extends; eauto.
          eapply abrel_valid; eauto.
          intros C. intros B. eapply H8. eapply A. eapply C. eauto.
        * split; eauto.
          eapply abrel_invar; eauto.
          eapply Mem.unchanged_on_implies; eauto.
          intros * A V; split; eauto.
    - intros i [ss ks2] [sf kf2] [ ].
    - intros [ss ks2] t [ss' ks2'] H idx [sf kf2] Hs. destruct H as [H <-].
      inv Hs.
      edestruct @fsim_simulation as (idx' & sf' & H' & Hs'); eauto.
      exists idx', (sf', kf2). split.
      + destruct H'; [left | right].
        apply lifting_step_plus; eauto.
        split. apply lifting_step_star; eauto. intuition. intuition.
      + econstructor; subst; eauto.
  Qed.

End TENSOR.

Lemma layer_lifting_simulation `(R1: abrel Ks1 Kf1) `(R2: abrel Ks2 Kf2) Ls Lf:
  disjoint_abrel R1 R2 -> forward_simulation 1 R1 Ls Lf ->
  forward_simulation 1 (R1 * R2)%abrel (lift_layer_k Ls) (lift_layer_k Lf).
Proof.
  intros HR [HL]. constructor.
  eapply Forward_simulation with (fsim_order HL) (state_match Ls Lf R1 R2 HL).
  - eapply (fsim_skel HL).
  - intros. apply (fsim_footprint HL i).
  - intros. eapply lift_layer_semantics_simulation; eauto.
  - apply (fsim_order_wf HL).
Qed.

(* The definition of tensor composition in terms of flat composition *)
Section TENSOR.

  Context {K1 K2: Type} (L1: layer K1) (L2: layer K2).
  Let LK1 := lift_layer_k (K2 := K2) L1.
  Let LK2 := layer_comm (lift_layer_k (K2 := K1) L2).
  Let LK i := match i with true => LK1 | false => LK2 end.

  Definition tensor_comp_semantics' sk := flat_comp_semantics' LK sk.

End TENSOR.

Section MONOTONICITY.

  Context `(R1: abrel Ks1 Kf1) `(R2: abrel Ks2 Kf2).
  Context `(HL1: forward_simulation (@cc_id li_null) R1 Ls1 Lf1)
          `(HL2: forward_simulation (@cc_id li_null) R2 Ls2 Lf2).
  Context sk (Hsk1: linkorder (skel Ls1) sk) (Hsk2: linkorder (skel Ls2) sk).
  Hypothesis (HR: disjoint_abrel R1 R2).

  Lemma tensor_compose_simulation:
    forward_simulation 1 (R1 * R2)%abrel
                       (tensor_comp_semantics' Ls1 Ls2 sk)
                       (tensor_comp_semantics' Lf1 Lf2 sk).
  Proof.
    unfold tensor_comp_semantics'. apply flat_composition_simulation'.
    - intros [|].
      + apply layer_lifting_simulation; eauto.
      + apply layer_comm_simulation.
        apply layer_lifting_simulation; eauto.
        intros se * A B. eapply HR; eauto.
    - intros [|]; auto.
  Qed.

End MONOTONICITY.

Section INTERC.

  Context {I: Type} {liA liB liC: language_interface}.
  Context (L1: I -> semantics liB liC) (L2: I -> semantics liA liB).
  Variable (sk sk1 sk2: AST.program unit unit) (ski: I -> AST.program unit unit).
  Let LC i := comp_semantics' (L1 i) (L2 i) (ski i).
  Let LF1 := flat_comp_semantics' L1 sk1.
  Let LF2 := flat_comp_semantics' L2 sk2.

  Inductive match_inter: flat_state LC -> comp_state LF1 LF2 -> Prop :=
  | match_inter1 i s:
      match_inter (flat_st LC i (st1 _ _ s)) (st1 LF1 _ (flat_st L1 i s))
  | match_inter2 i s1 s2:
      match_inter (flat_st LC i (st2 _ _ s1 s2)) (st2 LF1 LF2 (flat_st _ i s1) (flat_st _ i s2)).

  Lemma categorical_flat_interchangeable:
    flat_comp_semantics' LC sk ≤ comp_semantics' LF1 LF2 sk.
  Proof.
    constructor. econstructor; [ reflexivity | intros; cbn; firstorder | ..].
    intros se _ [ ] [ ] Hse. instantiate (1 := fun _ _ _ => _). cbn beta.
    apply forward_simulation_step with (match_states := match_inter).
    - intros q1 _ s1 [ ] H. inv H. inv H0.
      exists (st1 LF1 _ (flat_st L1 i s0)).
      split; repeat constructor. auto.
    - intros s1 s2 r1 Hs H. inv H. inv H0. inv Hs. SmallstepLinking.subst_dep.
      exists r1. split; repeat constructor. auto.
    - intros s1 s2 q Hs H. exists tt.
      inv H. inv H0. inv Hs. SmallstepLinking.subst_dep.
      exists q. repeat apply conj; try constructor. now constructor.
      intros r1 _ s1' [ ] Ht. inv Ht. inv H4. SmallstepLinking.subst_dep. inv H2.
      eexists. split; repeat constructor. auto.
    - intros. inv H.
      inv H1; inv H0; SmallstepLinking.subst_dep; eexists; split;
        [ apply step1 | | apply step2 | | eapply step_push | | eapply step_pop |  ]; repeat constructor; eauto.
    - apply well_founded_ltof.
  Qed.

End INTERC.
