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
From compcertox Require Import Lifting BQcode RBspec.

Inductive sig := enq | deq.

Inductive bq_internal_state: Type :=
| bq_init: forall (sig: sig) (vs: list val) (m: mem), bq_internal_state
| bq_call: forall (sig: RBspec.sig) (vs: list val) (m: mem), bq_internal_state
| bq_middle: forall (sig: sig) (vs: list val) (m: mem), bq_internal_state
| bq_middle': forall (sig: sig) (vs: val) (m: mem), bq_internal_state
| bq_final: forall (v: val) (m: mem), bq_internal_state.

Section RB_LTS.

  Variable ge:  genv.

  Inductive bq_initial_state: c_query -> bq_internal_state -> Prop :=
  | initial_state_geti: forall vf b v m  sig,
      vf = Vptr b Integers.Ptrofs.zero ->
      Genv.find_symbol ge enq_id = Some b ->
      Ple (Genv.genv_next ge) (Mem.nextblock m) ->
      Cop.val_casted v tint ->
      sig = enq_sg ->
      bq_initial_state (cq vf sig [v] m) (bq_init enq [v] m)
  | initial_state_seti: forall vf b m  sig,
      vf = Vptr b Integers.Ptrofs.zero ->
      Genv.find_symbol ge deq_id = Some b ->
      Ple (Genv.genv_next ge) (Mem.nextblock m) ->
      sig = deq_sg ->
      bq_initial_state (cq vf sig nil m) (bq_init deq  nil m).

  Inductive bq_final_state: bq_internal_state -> c_reply -> Prop :=
  | final_state: forall rv m,
      bq_final_state (bq_final rv m) (cr rv m).

  Inductive bq_step: bq_internal_state -> trace -> bq_internal_state -> Prop :=
  | enq_step1 v m:
      bq_step (bq_init enq [v] m) E0 (bq_call RBspec.inc2 [v] m)
  | enq_step2 v1 v2 m:
      bq_step (bq_middle enq [v1; v2] m) E0 (bq_call RBspec.seti [v1; v2] m)
  | enq_step3 vs m:
      bq_step (bq_middle' enq vs m) E0 (bq_final Vundef m)
  | deq_step1 m:
      bq_step (bq_init deq [] m) E0 (bq_call RBspec.inc1 [] m)
  | deq_step2 v m:
      bq_step (bq_middle deq [v] m) E0 (bq_call RBspec.geti [v] m)
  | deq_step3 v m:
      bq_step (bq_middle' deq v m) E0 (bq_final v m).

  Inductive bq_at_external: bq_internal_state -> c_query -> Prop :=
  | bq_ext_inc1 vf sig vs m b:
    vf = Vptr b Integers.Ptrofs.zero ->
    Genv.find_symbol ge inc1_id = Some b ->
    sig = inc1_sg ->
    bq_at_external (bq_call RBspec.inc1 vs m) (cq vf sig nil m)
  | bq_ext_inc2 vf sig vs m b:
    vf = Vptr b Integers.Ptrofs.zero ->
    Genv.find_symbol ge inc2_id = Some b ->
    sig = inc2_sg ->
    bq_at_external (bq_call RBspec.inc2 vs m) (cq vf sig nil m)
  | bq_ext_get vf sig v m b:
    vf = Vptr b Integers.Ptrofs.zero ->
    Genv.find_symbol ge get_id = Some b ->
    sig = get_sg ->
    bq_at_external (bq_call RBspec.geti [v] m) (cq vf sig [v] m)
  | bq_ext_set vf sig vs m b:
    vf = Vptr b Integers.Ptrofs.zero ->
    Genv.find_symbol ge set_id = Some b ->
    sig = set_sg ->
    bq_at_external (bq_call RBspec.seti vs m) (cq vf sig vs m).

  Inductive bq_after_external: bq_internal_state -> c_reply -> bq_internal_state -> Prop :=
  | bq_aft_inc1 rv m :
    Cop.val_casted rv tint ->
    bq_after_external (bq_call RBspec.inc1 nil m) (cr rv m) (bq_middle deq [rv] m)
  | bq_aft_inc2 rv v m :
    Cop.val_casted rv tint ->
    bq_after_external (bq_call RBspec.inc2 [v] m) (cr rv m) (bq_middle enq [rv; v] m)
  | bq_aft_get rv vs m :
    Cop.val_casted rv tint ->
    bq_after_external (bq_call RBspec.geti vs m) (cr rv m) (bq_middle' deq rv m)
  | bq_aft_set vs m :
    bq_after_external (bq_call RBspec.seti vs m) (cr Vundef m) (bq_middle' enq Vundef m).

  Program Definition bq_lts: lts li_c li_c bq_internal_state :=
    {|
      Smallstep.genvtype := genv;
      Smallstep.step ge := bq_step;
      Smallstep.initial_state := bq_initial_state;
      Smallstep.at_external := bq_at_external;
      Smallstep.after_external := bq_after_external;
      Smallstep.final_state := bq_final_state;
      Smallstep.globalenv := ge;
    |}.

End RB_LTS.

Definition bq_spec: semantics li_c li_c :=
  {|
    skel := AST.erase_program bq_program;
    activate se := bq_lts (Clight.globalenv se bq_program);
    footprint := AST.footprint_of_program bq_program;
  |}.

Inductive bq_ms se: bq_internal_state -> Clight.state -> Prop :=
| bq_ms_enq:
  forall vf m v,
    Cop.val_casted v tint ->
    Genv.find_funct (Genv.globalenv se bq_program) vf = Some (Internal bq_enq) ->
    bq_ms se (bq_init enq [v] m) (Callstate vf [v] Kstop m)
| bq_ms_deq:
  forall vf m,
    Genv.find_funct (Genv.globalenv se bq_program) vf = Some (Internal bq_deq) ->
    bq_ms se (bq_init deq [] m) (Callstate vf [] Kstop m)

| bq_ms_call_inc1:
  forall vf k m b,
    vf = Vptr b Integers.Ptrofs.zero ->
    Genv.find_symbol se inc1_id = Some b ->
    k = (Kcall (Some bq_deq_tmp1) bq_deq empty_env
          (PTree.Node (PTree.Node PTree.Leaf (Some Vundef) PTree.Leaf) (Some Vundef) PTree.Leaf)
          (Kseq
             (Ssequence
                (Scall (Some bq_deq_tmp2) (Evar get_id (Tfunction (Tcons tint Tnil) tint cc_default))
                   [Etempvar bq_deq_tmp1 tint]) (Sreturn (Some (Etempvar bq_deq_tmp2 tint)))) Kstop)) ->
    bq_ms se (bq_call RBspec.inc1 [] m) (Callstate vf [] k m)
| bq_ms_call_inc2:
  forall vf k m v b,
    Cop.val_casted v tint ->
    vf = Vptr b Integers.Ptrofs.zero ->
    Genv.find_symbol se inc2_id = Some b ->
    k = (Kcall (Some bq_enq_tmp) bq_enq empty_env
          (PTree.Node (PTree.Node PTree.Leaf (Some Vundef) PTree.Leaf) (Some v) PTree.Leaf)
          (Kseq
             (Ssequence
                (Scall None (Evar set_id (Tfunction (Tcons tint (Tcons tint Tnil)) tvoid cc_default))
                   [Etempvar bq_enq_tmp tint; Etempvar enq_arg_id tint]) (Sreturn None)) Kstop)) ->
    bq_ms se (bq_call RBspec.inc2 [v] m) (Callstate vf [] k m)

| bq_ms_mid_enq:
  forall m v1 v2 k,
    Cop.val_casted v1 tint ->
    Cop.val_casted v2 tint ->
    k = (Kcall (Some bq_enq_tmp) bq_enq empty_env
          (PTree.Node (PTree.Node PTree.Leaf (Some Vundef) PTree.Leaf) (Some v2) PTree.Leaf)
          (Kseq
             (Ssequence
                (Scall None (Evar set_id (Tfunction (Tcons tint (Tcons tint Tnil)) tvoid cc_default))
                   [Etempvar bq_enq_tmp tint; Etempvar enq_arg_id tint]) (Sreturn None)) Kstop)) ->
    bq_ms se (bq_middle enq [v1; v2] m) (Returnstate v1 k m)
| bq_ms_mid_deq:
  forall m v k,
    Cop.val_casted v tint ->
    k = (Kcall (Some bq_deq_tmp1) bq_deq empty_env
          (PTree.Node (PTree.Node PTree.Leaf (Some Vundef) PTree.Leaf) (Some Vundef) PTree.Leaf)
          (Kseq
             (Ssequence
                (Scall (Some bq_deq_tmp2) (Evar get_id (Tfunction (Tcons tint Tnil) tint cc_default))
                   [Etempvar bq_deq_tmp1 tint]) (Sreturn (Some (Etempvar bq_deq_tmp2 tint)))) Kstop)) ->
    bq_ms se (bq_middle deq [v] m) (Returnstate v k m)

| bq_ms_call_get:
  forall vf k m v b,
    vf = Vptr b Integers.Ptrofs.zero ->
    Genv.find_symbol se get_id = Some b ->
    Cop.val_casted v tint ->
    k = (Kcall (Some bq_deq_tmp2) bq_deq empty_env
          (PTree.Node (PTree.Node PTree.Leaf (Some Vundef) PTree.Leaf) (Some v) PTree.Leaf)
          (Kseq (Sreturn (Some (Etempvar bq_deq_tmp2 tint))) Kstop)) ->
    bq_ms se (bq_call RBspec.geti [v] m) (Callstate vf [v] k m)
| bq_ms_call_set:
  forall vf k m v1 v2 b,
    vf = Vptr b Integers.Ptrofs.zero ->
    Genv.find_symbol se set_id = Some b ->
    Cop.val_casted v1 tint ->
    Cop.val_casted v2 tint ->
    k = (Kcall None bq_enq empty_env (PTree.Node (PTree.Node PTree.Leaf (Some v1) PTree.Leaf) (Some v2) PTree.Leaf) (Kseq (Sreturn None) Kstop)) ->
    bq_ms se (bq_call RBspec.seti [v1; v2] m) (Callstate vf [v1; v2] k m)

| bq_ms_mid'_enq:
  forall m v k le,
    k = (Kcall None bq_enq empty_env le (Kseq (Sreturn None) Kstop)) ->
    bq_ms se (bq_middle' enq v m) (Returnstate v k m)
| bq_ms_mid'_deq:
  forall m v rv k,
    Cop.val_casted rv tint ->
    Cop.val_casted v tint ->
    k = (Kcall (Some bq_deq_tmp2) bq_deq empty_env
          (PTree.Node (PTree.Node PTree.Leaf (Some Vundef) PTree.Leaf) (Some v) PTree.Leaf)
          (Kseq (Sreturn (Some (Etempvar bq_deq_tmp2 tint))) Kstop)) ->
    bq_ms se (bq_middle' deq rv m) (Returnstate rv k m)

| bq_ms_final:
  forall rv m,
    bq_ms se (bq_final rv m) (Returnstate rv Kstop m).

Import Ptrofs.

Lemma inc2_block se:
  Genv.valid_for (erase_program bq_program) se ->
  exists b, Genv.find_symbol (globalenv ((semantics2 bq_program) se)) inc2_id = Some b /\
         Genv.find_funct (globalenv ((semantics2 bq_program) se)) (Vptr b zero) = Some inc2_ext.
Proof.
  intros Hse. eapply Genv.find_def_symbol with (id := inc2_id) in Hse .
  edestruct (proj1 Hse) as (b & Hb1 & Hb2). reflexivity.
  exists b. split; eauto. eapply genv_funct_symbol; eauto.
Qed.

Lemma set_block se:
  Genv.valid_for (erase_program bq_program) se ->
  exists b, Genv.find_symbol (globalenv ((semantics2 bq_program) se)) set_id = Some b /\
         Genv.find_funct (globalenv ((semantics2 bq_program) se)) (Vptr b zero) = Some set_ext.
Proof.
  intros Hse. eapply Genv.find_def_symbol with (id := set_id) in Hse .
  edestruct (proj1 Hse) as (b & Hb1 & Hb2). reflexivity.
  exists b. split; eauto. eapply genv_funct_symbol; eauto.
Qed.

Lemma inc1_block se:
  Genv.valid_for (erase_program bq_program) se ->
  exists b, Genv.find_symbol (globalenv ((semantics2 bq_program) se)) inc1_id = Some b /\
         Genv.find_funct (globalenv ((semantics2 bq_program) se)) (Vptr b zero) = Some inc1_ext.
Proof.
  intros Hse. eapply Genv.find_def_symbol with (id := inc1_id) in Hse .
  edestruct (proj1 Hse) as (b & Hb1 & Hb2). reflexivity.
  exists b. split; eauto. eapply genv_funct_symbol; eauto.
Qed.

Lemma get_block se:
  Genv.valid_for (erase_program bq_program) se ->
  exists b, Genv.find_symbol (globalenv ((semantics2 bq_program) se)) get_id = Some b /\
         Genv.find_funct (globalenv ((semantics2 bq_program) se)) (Vptr b zero) = Some get_ext.
Proof.
  intros Hse. eapply Genv.find_def_symbol with (id := get_id) in Hse .
  edestruct (proj1 Hse) as (b & Hb1 & Hb2). reflexivity.
  exists b. split; eauto. eapply genv_funct_symbol; eauto.
Qed.
Opaque Genv.find_funct semantics2.

Opaque semantics2.
Opaque Nat.modulo.
Require Import Lia.

Lemma bq_correct: forward_simulation cc_id cc_id bq_spec (Clight.semantics2 bq_program).
Proof.
  constructor. econstructor. reflexivity. firstorder.
  intros. instantiate (1 := fun _ _ _ => _). cbn beta.
  destruct H. subst.
  set (ms := fun (s1: state bq_spec) s2 => bq_ms se1 s1 s2).
  eapply forward_simulation_plus with (match_states := ms).
  - intros. destruct q1. inv H. inv H1.
    + eexists. split.
      * econstructor; eauto.
        eapply genv_funct_symbol; eauto. reflexivity.
        unfold type_of_function. f_equal; cbn.
        constructor; eauto. constructor.
      * constructor; eauto. eapply genv_funct_symbol; eauto.
    + eexists. split.
      * econstructor; eauto.
        eapply genv_funct_symbol; eauto. reflexivity.
        unfold type_of_function. f_equal; cbn.
        constructor; eauto.
      * constructor. eapply genv_funct_symbol; eauto.
  - intros. destruct r1. inv H1. inv H.
    eexists. split. constructor. constructor.
  - intros. inv H1; inv H.
    (* inc1 *)
    + eexists tt, _.  split. 2: split.
      * econstructor; eauto.
        eapply genv_funct_symbol; eauto. reflexivity.
      * assert (b = b0). cbn in *. congruence.
        subst. constructor.
      * split. constructor. intros. inv H. inv H1.
        eexists. split; constructor; eauto.
    (* inc2 *)
    + eexists tt, _.  split. 2: split.
      * econstructor; eauto.
        eapply genv_funct_symbol; eauto. reflexivity.
      * assert (b = b0).  cbn in *. congruence.
        subst. constructor.
      * split. constructor. intros. inv H. inv H1.
        eexists. split; constructor; eauto.
    (* get *)
    + eexists tt, _.  split. 2: split.
      * econstructor; eauto.
        eapply genv_funct_symbol; eauto. reflexivity.
      * assert (b = b0). cbn in *. congruence.
        subst. constructor.
      * split. constructor. intros. inv H. inv H1.
        eexists. split. econstructor; eauto.
        econstructor. apply H8. apply H6. reflexivity.
    (* set *)
    + eexists tt, _.  split. 2: split.
      * econstructor; eauto.
        eapply genv_funct_symbol; eauto. reflexivity.
      * assert (b = b0). cbn in *. congruence.
        subst. constructor.
      * split. constructor. intros. inv H. inv H1.
        eexists. split. econstructor; eauto.
        econstructor. reflexivity.
  - intros. inv H1; inv H.
    (* enq: from initial to call inc2 *)
    + exploit inc2_block; eauto. intros (b1 & A & B).
      eexists. split.
      * eapply plus_left. constructor; eauto.
        {
          constructor; repeat constructor.
          intros x. inv x. solve_list_disjoint.
        }
        lts_step. crush_step.
        lts_step. crush_step; crush_expr.
        apply star_refl. reflexivity.
      * econstructor; eauto.
    (* deq: from initial to call inc1 *)
    + exploit inc1_block; eauto. intros (b1 & A & B).
      eexists. split.
      * eapply plus_left. constructor; eauto.
        { constructor; repeat constructor. solve_list_disjoint. }
        lts_step. crush_step.
        lts_step. crush_step; crush_expr.
        apply star_refl. reflexivity.
      * econstructor; eauto.
    (* enq: after inc2, call set *)
    + exploit set_block; eauto. intros (b1 & A & B).
      eexists. split.
      * eapply plus_left. constructor; eauto.
        lts_step. crush_step.
        lts_step. crush_step.
        lts_step. crush_step; crush_expr.
        apply star_refl. reflexivity.
      * econstructor; eauto.
    (* deq: after inc1, call get *)
    + exploit get_block; eauto. intros (b1 & A & B).
      eexists. split.
      * eapply plus_left. constructor; eauto.
        lts_step. crush_step.
        lts_step. crush_step.
        lts_step. crush_step; crush_expr.
        apply star_refl. reflexivity.
      * econstructor; eauto.
    (* enq: to final state *)
    + eexists. split.
      * eapply plus_left. constructor.
        lts_step. crush_step.
        lts_step. crush_step; crush_expr.
        apply star_refl. reflexivity.
      * constructor.
    (* deq: to final state *)
    + eexists. split.
      * eapply plus_left. constructor.
        lts_step. crush_step.
        lts_step. crush_step; crush_expr.
        apply star_refl. reflexivity.
      * constructor.
  - apply well_founded_ltof.
Qed.
