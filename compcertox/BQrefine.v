From Coq Require Import List.
From compcert Require Import
     Integers Coqlib Maps
     Memory AST Values
     Clight Ctypes
     LanguageInterface
     Events Globalenvs
     Smallstep SimplLocalsproof.
(* From cal.example Require Import BQ. *)
Import ListNotations.
From compcertox Require Import Lifting BQcode RBspec BQspec.

Definition bq_state : Type := list val.

Inductive bq_abs_state: Type :=
| bq_abs_init: forall (sig: BQspec.sig) (s: bq_state) (vs: list val) (m: mem), bq_abs_state
| bq_abs_final: forall (s: bq_state) (v: val) (m: mem), bq_abs_state.

Section BQ_LTS.

  Variable ge:  genv.

  Inductive bq_abs_initial_state: c_query * bq_state -> bq_abs_state -> Prop :=
  | initial_state_enq: forall vf b v m bqst sig,
      vf = Vptr b Integers.Ptrofs.zero ->
      Genv.find_symbol ge enq_id = Some b ->
      Ple (Genv.genv_next ge) (Mem.nextblock m) ->
      Cop.val_casted v tint ->
      sig = enq_sg ->
      bq_abs_initial_state (cq vf sig [v] m, bqst) (bq_abs_init enq bqst [v] m)
  | initial_state_deq: forall vf b m bqst sig,
      vf = Vptr b Integers.Ptrofs.zero ->
      Genv.find_symbol ge deq_id = Some b ->
      Ple (Genv.genv_next ge) (Mem.nextblock m) ->
      sig = deq_sg ->
      bq_abs_initial_state (cq vf sig nil m, bqst) (bq_abs_init deq bqst nil m).

  Inductive bq_abs_final_state: bq_abs_state -> c_reply * bq_state -> Prop :=
  | final_state: forall rv m bqst,
      bq_abs_final_state (bq_abs_final bqst rv m) (cr rv m, bqst).

  Inductive bq_abs_step: bq_abs_state -> trace -> bq_abs_state -> Prop :=
  | enq_step:
    forall m vs v,
      (List.length vs < N)%nat ->
      bq_abs_step (bq_abs_init BQspec.enq vs [v] m) E0 (bq_abs_final (vs++[v]) Vundef m)
  | deq_step:
    forall m vs v,
      bq_abs_step (bq_abs_init BQspec.deq (v::vs) [] m) E0 (bq_abs_final vs v m).

  Program Definition bq_lts: lts li_c (li_c@bq_state) bq_abs_state :=
    {|
      Smallstep.genvtype := genv;
      Smallstep.step ge := bq_abs_step;
      Smallstep.initial_state := bq_abs_initial_state;
      Smallstep.at_external _ _ := False;
      Smallstep.after_external _ _ _ := False;
      Smallstep.final_state := bq_abs_final_state;
      Smallstep.globalenv := ge;
    |}.

End BQ_LTS.

Hypothesis rb_bq_linking:
  { cprog & Linking.link bq_program rb_program = Some cprog}.

Definition rb_bq_prog := projT1 rb_bq_linking.
Definition rb_bq_skel := AST.erase_program rb_bq_prog.

Definition bq_abs_spec: semantics li_c (li_c@bq_state) :=
  {|
    skel := AST.erase_program rb_bq_prog;
    activate se := bq_lts (Clight.globalenv se rb_bq_prog);
    footprint := fun i => footprint_of_program bq_program i \/ footprint_of_program rb_program i;
  |}.

Open Scope nat_scope.

Fixpoint slice (f : nat -> val) (i : nat) (n : nat) : list val :=
  match n with
    | O => nil
    | S n' => f i :: slice f (S i mod N) n'
  end.

Inductive rb_bq : bq_state -> rb_state -> Prop :=
  bq_rb_intro f c1 c2 n q :
    c1 < N ->
    n <= N ->
    q = slice f c1 n ->
    c2 = (c1 + n) mod N ->
    (forall i, Cop.val_casted (f i) tint) ->
    rb_bq q (f, c1, c2).

Lemma rb_bq_c2:
  forall q f c1 c2,
    rb_bq q (f, c1, c2) -> c2 < N.
Proof.
  intros. inv H. apply Nat.mod_upper_bound. unfold N. omega.
Qed.

Program Definition bq_cc: callconv (li_c@bq_state) (li_c@rb_state) :=
  {|
    ccworld := unit;
    match_senv _ := eq;
    match_query _ '(q1, s1) '(q2, s2) := q1 = q2 /\ rb_bq s1 s2;
    match_reply _ '(r1, s1) '(r2, s2) := r1 = r2 /\ rb_bq s1 s2;
  |}.
Next Obligation. reflexivity. Qed.
Next Obligation. reflexivity. Qed.
Next Obligation. reflexivity. Qed.

Require Import CategoricalComp.

Let L := comp_semantics' (bq_spec @ rb_state) rb_spec rb_bq_skel.

Inductive bq_abs_ms se: bq_abs_state -> comp_state (bq_spec @ rb_state) rb_spec -> Prop :=
| bq_abs_ms_enq:
  forall m v rbst bqst,
    rb_bq bqst rbst ->
    Ple (Genv.genv_next se) (Mem.nextblock m) ->
    Cop.val_casted v tint ->
    bq_abs_ms se  (bq_abs_init enq bqst [v] m)
      (st1 (bq_spec @ rb_state) _ (bq_init enq [v] m, rbst))
| bq_abs_ms_deq:
  forall m rbst bqst,
    rb_bq bqst rbst ->
    Ple (Genv.genv_next se) (Mem.nextblock m) ->
    bq_abs_ms se (bq_abs_init deq bqst nil m)
      (st1 (bq_spec @ rb_state) _ (bq_init deq nil m, rbst))
| bq_abs_ms_final:
  forall rv m bqst rbst,
    rb_bq bqst rbst ->
    bq_abs_ms se (bq_abs_final bqst rv m) (st1 (bq_spec @ rb_state) _ (bq_final rv m, rbst)).

Opaque semantics2.
Opaque Nat.modulo.
Require Import Lia.

Lemma bq_correct1:
  forall v vs f c1 c2,
  rb_bq (v :: vs) (f, c1, c2) ->
  v = f c1 /\ rb_bq vs (f, S c1 mod N, c2).
Proof.
  intros. inv H. destruct n as [|m]. easy.
  inv H6. split. easy.
  eapply bq_rb_intro with (n := m); eauto.
  - apply Nat.mod_upper_bound. unfold N. omega.
  - apply le_Sn_le; eauto.
  - rewrite Nat.add_mod_idemp_l.
    f_equal. omega. unfold N. omega.
Qed.

Lemma slice_length f c1 n :
  List.length (slice f c1 n) = n.
Proof.
  revert c1. induction n; cbn; auto.
Qed.

Lemma mod_add_not_same a b:
  a < N -> b < N -> b <> 0 -> (a + b) mod N <> a.
Proof.
Admitted.

Lemma bq_correct2:
  forall v vs f c1 c2,
  List.length vs < N ->
  Cop.val_casted v tint ->
  rb_bq vs (f, c1, c2) ->
  rb_bq (vs++[v]) (fun j : nat => if Nat.eq_dec c2 j then v else f j, c1, S c2 mod N).
Proof.
  intros. inv H1. apply le_lt_or_eq in H6 as [A|A].
  - eapply bq_rb_intro with (n := S n); eauto.
    + clear - H5 A. revert c1 H5. induction n; cbn; intros.
      * destruct Nat.eq_dec. reflexivity. exfalso. apply n.
        rewrite Nat.add_0_r. now apply Nat.mod_small.
      * rewrite IHn.
        -- cbn. f_equal.
           ++ destruct Nat.eq_dec; try easy.
              exfalso. eapply mod_add_not_same. apply H5. apply A. easy. apply e.
           ++ replace ((S c1 mod N + n) mod N) with ((c1 + S n) mod N). easy.
              change (S ?x) with (1 + x).
              rewrite Nat.add_mod_idemp_l. f_equal. omega.
              unfold N. omega.
        -- apply Nat.lt_succ_l. auto.
        -- apply Nat.mod_upper_bound. unfold N. omega.
    + change (S ?x) with (1 + x).
      rewrite Nat.add_mod_idemp_r. f_equal. omega.
      unfold N. omega.
    + intros. destruct Nat.eq_dec; eauto.
  - rewrite slice_length in H. omega.
Qed.

Hypothesis linkorder_erase:
  forall (p q: Clight.program),
  Linking.linkorder p q ->
  Linking.linkorder (erase_program p) (erase_program q).

Lemma bq_linkorder: Linking.linkorder bq_program rb_bq_prog.
Proof.
  unfold rb_bq_prog.
  pose proof (projT2 rb_bq_linking). cbn in *.
  apply Linking.link_linkorder in H. apply H.
Qed.

Lemma rb_linkorder: Linking.linkorder rb_program rb_bq_prog.
Proof.
  unfold rb_bq_prog.
  pose proof (projT2 rb_bq_linking). cbn in *.
  apply Linking.link_linkorder in H. apply H.
Qed.

Lemma bq_refine: forward_simulation cc_id bq_cc bq_abs_spec
                   (CategoricalComp.comp_semantics' (bq_spec @ rb_state) rb_spec rb_bq_skel).
Proof.
  constructor. econstructor. reflexivity. firstorder.
  intros. instantiate (1 := fun _ _ _ => _). cbn beta.
  destruct H. destruct wB.
  set (ms := fun s1 s2 => bq_abs_ms se1 s1 s2).
  eapply forward_simulation_plus with (match_states := ms).
  - intros. destruct q1, q2, H. subst. inv H1.
    + eexists. split.
      * econstructor.  instantiate (1 := (_, _)).
        constructor; cbn. econstructor; eauto. reflexivity.
      * econstructor; eauto.
    + eexists. split.
      * econstructor.  instantiate (1 := (_, _)).
        constructor; cbn. econstructor; eauto. reflexivity.
      * econstructor; eauto.
  - intros. inv H; inv H1.
    eexists (_, _). split; repeat constructor. eauto.
  - intros. inv H1.
  - intros. inv H1; inv H.
    (* enq *)
    + exploit (inc2_block se1). cbn in *.
      eapply Genv.valid_for_linkorder; eauto.
      apply linkorder_erase. apply bq_linkorder.
      intros (b1 & A & B).
      exploit (set_block se1).
      eapply Genv.valid_for_linkorder; eauto.
      apply linkorder_erase. apply bq_linkorder.
      intros (b2 & C & D).
      destruct rbst as [[f c1] c2].
      eexists. split.
      * eapply plus_left. cbn. constructor.
        { instantiate (1 := (_, _)). constructor; eauto. constructor. }
        lts_step.
        {
          eapply step_push.
          - instantiate (1 := (_, _)).  constructor; cbn.
            econstructor; eauto. eauto.
          - eapply initial_state_inc2; eauto.
        }
        lts_step.
        { eapply step2. constructor. reflexivity. }
        lts_step.
        {
          eapply step_pop.
          - constructor.
          - instantiate (1 := (_, _)). constructor; cbn.
            constructor. constructor. cbn. reflexivity. reflexivity.
        }
        lts_step.
        { apply step1. instantiate (1 := (_, _)). constructor; eauto. constructor. }
        lts_step.
        {
          eapply step_push.
          - instantiate (1 := (_, _)).  constructor; cbn.
            econstructor; eauto. eauto.
          - econstructor; eauto. constructor. reflexivity.
        }
        lts_step.
        { eapply step2. constructor; eauto. eapply rb_bq_c2; eauto. }
        lts_step.
        {
          eapply step_pop.
          - constructor.
          - instantiate (1 := (_, _)). constructor; cbn.
            constructor. reflexivity.
        }
        lts_step.
        { eapply step1. instantiate (1 := (_, _)). repeat constructor. }
        apply star_refl. reflexivity.
      * constructor. now apply bq_correct2.
    (* deq *)
    + exploit (inc1_block se1).
      eapply Genv.valid_for_linkorder; eauto.
      apply linkorder_erase. apply bq_linkorder.
      intros (b1 & A & B).
      exploit (get_block se1).
      eapply Genv.valid_for_linkorder; eauto.
      apply linkorder_erase. apply bq_linkorder.
      intros (b2 & C & D).
      destruct rbst as [[f c1] c2].
      eexists. split.
      * eapply plus_left. cbn. constructor.
        { instantiate (1 := (_, _)). constructor; eauto. constructor. }
        lts_step.
        {
          eapply step_push.
          - instantiate (1 := (_, _)).  constructor; cbn.
            econstructor; eauto. eauto.
          - eapply initial_state_inc1; eauto.
        }
        lts_step.
        { eapply step2. constructor. reflexivity. }
        lts_step.
        {
          eapply step_pop.
          - constructor.
          - instantiate (1 := (_, _)). constructor; cbn.
            constructor. constructor. cbn. reflexivity. reflexivity.
        }
        lts_step.
        { apply step1. instantiate (1 := (_, _)). constructor; eauto. constructor. }
        lts_step.
        {
          eapply step_push.
          - instantiate (1 := (_, _)).  constructor; cbn.
            econstructor; eauto. eauto.
          - econstructor; eauto.
            constructor. reflexivity.
        }
        lts_step.
        { eapply step2. constructor. reflexivity. inv H2; eauto. }
        lts_step.
        {
          eapply step_pop.
          - constructor.
          - instantiate (1 := (_, _)). constructor; cbn.
            constructor. inv H2. apply H10. reflexivity.
        }
        lts_step.
        { eapply step1. instantiate (1 := (_, _)). repeat constructor. }
        apply star_refl. reflexivity.
      * eapply bq_correct1 in H2 as [X Y]. subst.
        constructor. auto.
  - apply well_founded_ltof.
Qed.
