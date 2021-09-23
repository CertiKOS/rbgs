Require Import Relations RelationClasses Relators.
Require Import List Maps.
Require Import Coqlib.
Require Import CallconvAlgebra_.
Require Import LanguageInterface_ Events Globalenvs Smallstep_ CategoricalComp FlatComp.
Require Import Memory Values.
Require Import Linking.
Require Import Lifting AbstractStateRel.

Generalizable All Variables.

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

Definition semantics_map {liA1 liA2 liB1 liB2} (L: semantics liA1 liB1)
           (F: li_func liA1 liA2) (G: li_func liB1 liB2) :=
  {|
    skel := skel L;
    activate se := lts_map (L se) F G;
    footprint := footprint L;
  |}.

Definition id_li_func {liA} := mk_li_func liA liA id id.

Definition map_outgoing {liA liB1 liB2} (L: semantics liA liB1) (F: li_func liB1 liB2) :=
  semantics_map L id_li_func F.

Definition map_incoming {liA1 liA2 liB} (L: semantics liA1 liB) (F: li_func liA1 liA2) :=
  semantics_map L F id_li_func.

Definition map_both {li1 li2} (L: semantics li1 li1) (F: li_func li1 li2) :=
  semantics_map L F F.

Infix "##" := map_incoming (at level 50): lts_scope.
Infix "$$" := map_outgoing (at level 50): lts_scope.
Infix "%%" := map_both (at level 50): lts_scope.

(* The generated definition looks funky
   Try use idtac as default *)
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

Program Definition li_func_comm {li K1 K2}: li_func (li@(K1*K2)) (li@(K2*K1)) :=
  {|
    query_func '(q, (k1, k2)) := (q, (k2, k1));
    reply_func '(r, (k1, k2)) := (r, (k2, k1));
  |}.

Definition lift_layer {li K} (L: semantics li_null li): semantics li_null (li@K) :=
  L@K ## li_func_null.

Definition lift_layer_k {li K1 K2} (L: semantics li_null (li@K1)): semantics li_null (li@(K1*K2)) :=
  L@K2 ## li_func_null $$ li_func_k.

Definition layer_comm {li K1 K2} (L: semantics li_null (li@(K2*K1))): semantics li_null (li@(K1*K2)) :=
  L $$ li_func_comm.

Definition lts_comm {li K1 K2} (L: semantics (li@(K2*K1)) (li@(K2*K1))): semantics (li@(K1*K2)) (li@(K1*K2)) :=
  L %% li_func_comm.

Section Properties.

  Context {K1 K2 K3 K4} (R1: krel K1 K2) (R2: krel K3 K4).
  Lemma prod_match_reply w r1 r2 k1 k2 k3 k4:
    match_reply R1 w (r1, k1) (r2, k2) ->
    Rk R2 k3 k4 -> Rr R2 k3 (cr_mem r2) ->
    (* kmrel (krel_crel R2) (cr_mem r1, k3) (cr_mem r2, k4) -> *)
    match_reply (R1 * R2) w (r1, (k1, k3)) (r2, (k2, k4)).
  Proof.
    intros [w' [Hw' Hr]] H. exists w'; split.
    - cbn in *. eapply Mem.unchanged_on_implies; eauto.
      cbn in *. intros. intro contra. apply H1. now left.
    - inv Hr. cbn in *. constructor; eauto.
      + split; eauto.
      + split; eauto.
  Qed.

  Lemma prod_match_query w q1 q2 k1 k2 k3 k4:
    match_query (R1 * R2) w (q1, (k1, k3)) (q2, (k2, k4)) ->
    match_query R1 w (q1, k1) (q2, k2) /\ Rk R2 k3 k4 /\ Rr R2 k3 w.
  Proof.
    intros. inv H. repeat apply conj; cbn in *.
    constructor; eauto.
    - intros b ofs Hg. apply H9. now left.
    - firstorder.
    - firstorder.
    - firstorder.
    - firstorder.
  Qed.

End Properties.

Section TENSOR.

  Context {K1 K2} (L1: semantics li_null (li_c@K1)) (L2: semantics li_null (li_c@K2)).
  Context {J1 J2} (jcc: krel J1 J2) (kcc: krel K1 K2).
  Context (HL: fsim_components 1 kcc L1 L2).
  Context (se1 se2: Genv.symtbl) (w : ccworld (kcc * jcc)).
  Context (Hse: match_senv (kcc * jcc) w se1 se2).
  Context (Hse1: Genv.valid_for (skel L1) se1).

  Hypothesis Hdisjoint: forall b ofs, G jcc b ofs -> G kcc b ofs -> False.

  Inductive state_match: fsim_index HL -> state L1 * J1 -> state L2 * J2 -> Prop :=
  | lift_state_match i s1 j1 s2 j2:
      fsim_match_states HL se1 se2 w i s1 s2 ->
      Rk jcc j1 j2 -> Rr jcc j1 w ->
      state_match i (s1, j1) (s2, j2).

  Lemma lift_layer_semantics_simulation:
    fsim_properties 1 (kcc * jcc) se1 se2 w
      (lift_layer_k L1 se1) (lift_layer_k L2 se2)
      (fsim_index HL) (fsim_order HL) state_match.
  Proof.
    split; cbn.
    - intros [q1 [k1 j1]] [q2 [k2 j2]] [s1 sj1] Hq [H Hj]; cbn in *.
      subst sj1. eapply prod_match_query in Hq.
      pose proof (fsim_lts HL _ w Hse Hse1).
      edestruct @fsim_match_initial_states as (idx & s2 & Hs2 & Hs); eauto.
      apply Hq. exists idx, (s2, j2). split. split; auto.
      constructor; auto. apply Hq. apply Hq.
    - intros idx [s1 sj1] [s2 sj2] [r1 [kr1 jr1]] Hs [H Hj].
      inv Hs. pose proof (fsim_lts HL _ w Hse Hse1).
      edestruct @fsim_match_final_states as (r2 & Hr2 & Hr); eauto.
      cbn [fst snd] in *. destruct r2 as [r2 rk2]. subst sj1.
      exists (r2, (rk2, sj2)). split. split; eauto.
      apply prod_match_reply. apply Hr. auto.
      eapply G_unchanged; eauto.
      destruct Hr as [w' [Hw' Hr]]. inv Hr.
      eapply Mem.unchanged_on_implies. apply Hw'.
      cbn. intros. intros contra. eapply Hdisjoint; eauto.
    - intros i [s1 sj1] [s2 sj2] [ ].
    - intros [s1 sj1] t [s1' sj1'] H idx [s2 sj2] Hs. destruct H as [H <-].
      inv Hs. pose proof (fsim_lts HL _ w Hse Hse1).
      edestruct @fsim_simulation as (idx' & s2' & Hs2' & Hs'); eauto.
      exists idx', (s2', sj2). split.
      + destruct Hs2'; [left | right].
        apply lifting_step_plus; eauto.
        split. apply lifting_step_star; eauto. intuition. intuition.
      + constructor; eauto.
  Qed.

End TENSOR.

Lemma layer_lifting_simulation {K1 K2 J1 J2} (kcc: krel K1 K2) (jcc: krel J1 J2) L1 L2:
  (forall b ofs, G jcc b ofs -> G kcc b ofs -> False) -> forward_simulation 1 kcc L1 L2 ->
  forward_simulation 1 (kcc * jcc) (lift_layer_k L1) (lift_layer_k L2).
Proof.
  intros Hdisjoint [HL]. constructor.
  eapply Forward_simulation with (fsim_order HL) (state_match L1 L2 jcc kcc HL).
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
