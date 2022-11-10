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
From compcertox Require Import Lifting BQcode.

Definition rb_state : Type := (nat -> val) * nat * nat.

Inductive sig := inc1 | inc2 | geti | seti.

Inductive rb_internal_state: Type :=
| rb_init: forall (sig: sig) (s: rb_state) (vs: list val) (m: mem), rb_internal_state
| rb_final: forall (s: rb_state) (v: val) (m: mem), rb_internal_state.

Section RB_LTS.

  Variable ge:  genv.

  Inductive rb_initial_state: c_query * rb_state -> rb_internal_state -> Prop :=
  | initial_state_inc1: forall vf b m rbst sig,
      vf = Vptr b Integers.Ptrofs.zero ->
      Genv.find_symbol ge inc1_id = Some b ->
      Ple (Genv.genv_next ge) (Mem.nextblock m) ->
      sig = inc1_sg ->
      rb_initial_state (cq vf sig nil m, rbst) (rb_init inc1 rbst nil m)
  | initial_state_inc2: forall vf b m rbst sig,
      vf = Vptr b Integers.Ptrofs.zero ->
      Genv.find_symbol ge inc2_id = Some b ->
      Ple (Genv.genv_next ge) (Mem.nextblock m) ->
      sig = inc2_sg ->
      rb_initial_state (cq vf sig nil m, rbst) (rb_init inc2 rbst nil m)
  | initial_state_geti: forall vf b v m rbst sig,
      vf = Vptr b Integers.Ptrofs.zero ->
      Genv.find_symbol ge get_id = Some b ->
      Ple (Genv.genv_next ge) (Mem.nextblock m) ->
      Cop.val_casted v tint ->
      sig = get_sg ->
      rb_initial_state (cq vf sig [v] m, rbst) (rb_init geti rbst [v] m)
  | initial_state_seti: forall vf b m rbst sig vargs v1 v2,
      vf = Vptr b Integers.Ptrofs.zero ->
      Genv.find_symbol ge set_id = Some b ->
      Ple (Genv.genv_next ge) (Mem.nextblock m) ->
      sig = set_sg ->
      vargs = [ v1; v2 ] ->
      Cop.val_casted v1 tint ->
      Cop.val_casted v2 tint ->
      rb_initial_state (cq vf sig vargs m, rbst) (rb_init seti rbst vargs m).

  Inductive rb_final_state: rb_internal_state -> c_reply * rb_state -> Prop :=
  | final_state: forall rv m rbst,
      rb_final_state (rb_final rbst rv m) (cr rv m, rbst).

  Inductive rb_step: rb_internal_state -> trace -> rb_internal_state -> Prop :=
  | inc1_step:
    forall f c1 c2 m v,
      v = Vint (Integers.Int.repr (Z.of_nat c1)) ->
      rb_step (rb_init inc1 (f, c1, c2) nil m) E0 (rb_final (f, (S c1 mod N)%nat, c2) v m)
  | inc2_step:
    forall f c1 c2 m v,
      v = Vint (Integers.Int.repr (Z.of_nat c2)) ->
      rb_step (rb_init inc2 (f, c1, c2) nil m) E0 (rb_final (f, c1, (S c2 mod N)%nat) v m)
  | get_step:
    forall f c1 c2 m v i,
      v = Vint (Integers.Int.repr (Z.of_nat i)) ->
      (i < N)%nat ->
      rb_step (rb_init geti (f, c1, c2) [v] m) E0 (rb_final (f, c1, c2) (f i) m)
  | set_step:
    forall f c1 c2 m v1 v2 i,
      v1 = Vint (Integers.Int.repr (Z.of_nat i)) ->
      (i < N)%nat ->
      Cop.val_casted v2 tint ->
      rb_step (rb_init seti (f, c1, c2) [v1; v2] m) E0
        (rb_final ((fun j => if Nat.eq_dec i j then v2 else f j), c1, c2)
                  Vundef m).

  Program Definition rb_lts: lts li_c (li_c@rb_state) rb_internal_state :=
    {|
      Smallstep.genvtype := genv;
      Smallstep.step ge := rb_step;
      Smallstep.initial_state := rb_initial_state;
      Smallstep.at_external _ _ := False;
      Smallstep.after_external _ _ _ := False;
      Smallstep.final_state := rb_final_state;
      Smallstep.globalenv := ge;
    |}.

End RB_LTS.

Definition rb_spec: semantics li_c (li_c@rb_state) :=
  {|
    skel := AST.erase_program rb_program;
    activate se := rb_lts (Clight.globalenv se rb_program);
    footprint := AST.footprint_of_program rb_program;
  |}.

Inductive nat_rel: nat -> val -> Prop :=
| nat_rel_intro n i:
  Z.of_nat n = Integers.Int.intval i ->
  nat_rel n (Vint i).

Inductive rel_cnt se (id: positive): nat -> mem -> Prop :=
| rel_cnt_intro b v n m:
  Genv.find_symbol se id = Some b ->
  Mem.load Mint32 m b 0 = Some v ->
  nat_rel n v -> (n < N)%nat ->
  Mem.range_perm m b 0 4 Cur Writable ->
  rel_cnt se id n m.

Inductive rel_arr se : (nat -> val) -> mem -> Prop :=
| rel_arr_intro f b m:
  Genv.find_symbol se arr_id = Some b ->
  (forall i, (i < N)%nat ->
        exists v, Mem.load Mint32 m b (4 * Z.of_nat i) = Some v /\ (f i) = v /\ Cop.val_casted v tint) ->
  (forall ofs, 0 <= ofs < 4 * Nz -> Mem.perm m b ofs Cur Writable) ->
  rel_arr se f m.

Inductive rb_match_mem: Genv.symtbl -> rb_state -> mem -> Prop :=
| rb_match_mem_intro:
  forall se f c1 c2 m,
    rel_cnt se cnt1_id c1 m ->
    rel_cnt se cnt2_id c2 m ->
    rel_arr se f m ->
    rb_match_mem se (f, c1, c2) m.

Inductive rb_match_query: Genv.symtbl -> c_query * rb_state -> c_query -> Prop :=
| rb_query_intro:
  forall se m vf sig vargs rbst,
    rb_match_mem se rbst m ->
    rb_match_query se (cq vf sig vargs m, rbst) (cq vf sig vargs m).

Inductive rb_match_reply: Genv.symtbl -> c_reply * rb_state -> c_reply -> Prop :=
| rb_reply_intro:
  forall se rbst m m' rv,
    rb_match_mem se rbst m' ->
    rb_match_reply se (cr rv m, rbst) (cr rv m').

Program Definition rb_cc: callconv (li_c@rb_state) li_c :=
  {|
    ccworld := Genv.symtbl;
    match_senv se se1 se2 := se = se1 /\ se = se2;
    match_query := rb_match_query;
    match_reply := rb_match_reply;
  |}.
Next Obligation. reflexivity. Qed.
Next Obligation. inv H0. reflexivity. Qed.
Next Obligation. inv H. reflexivity. Qed.

Inductive rb_ms se: rb_internal_state -> Clight.state -> Prop :=
| rb_ms_inc1:
  forall vf  m rbst vs,
    rb_match_mem se rbst m ->
    Genv.find_funct (Genv.globalenv se rb_program) vf = Some (Internal rb_inc1) ->
    rb_ms se  (rb_init inc1 rbst vs m) (Callstate vf vs Kstop m)
| rb_ms_inc2:
  forall vf  m rbst vs,
    rb_match_mem se rbst m ->
    Genv.find_funct (Genv.globalenv se rb_program) vf = Some (Internal rb_inc2) ->
    rb_ms se  (rb_init inc2 rbst vs m) (Callstate vf vs Kstop m)
| rb_ms_set:
  forall vf  m rbst vs,
    rb_match_mem se rbst m ->
    Genv.find_funct (Genv.globalenv se rb_program) vf = Some (Internal rb_set) ->
    rb_ms se  (rb_init seti rbst vs m) (Callstate vf vs Kstop m)
| rb_ms_get:
  forall vf  m rbst vs,
    rb_match_mem se rbst m ->
    Genv.find_funct (Genv.globalenv se rb_program) vf = Some (Internal rb_get) ->
    rb_ms se  (rb_init geti rbst vs m) (Callstate vf vs Kstop m)
| rb_ms_final:
  forall rv m m' rbst,
    rb_match_mem se rbst m' ->
    rb_ms se (rb_final rbst rv m) (Returnstate rv Kstop m').

Opaque semantics2.
Opaque Nat.modulo.
Require Import Lia.

Lemma rel_cnt_store_other:
  forall se i j c m b m' v ofs,
  i <> j ->
  rel_cnt se i c m ->
  Genv.find_symbol se j = Some b ->
  Mem.store Mint32 m b ofs v = Some m' ->
  rel_cnt se i c m'.
Proof.
  intros. inv H0.
  assert (b <> b0).
  { intros <-. exploit Genv.find_symbol_injective.
    apply H1. apply H3. intros <-. apply H. easy. }
  econstructor; eauto.
  erewrite Mem.load_store_other; eauto.
  intros ofs' Hofs. eapply Mem.perm_store_1; eauto.
Qed.

Lemma rel_arr_store_other:
  forall se j f m b m' v ofs',
  j <> arr_id ->
  rel_arr se f m ->
  Genv.find_symbol se j = Some b ->
  Mem.store Mint32 m b ofs' v = Some m' ->
  rel_arr se f m'.
Proof.
  intros. inv H0.
  assert (b <> b0).
  { intros <-. exploit Genv.find_symbol_injective.
    apply H1. apply H3. intros ->. apply H. easy. }
  econstructor; eauto.
  intros. specialize (H4 _ H6). destruct H4 as (? & ? & ? & ?). subst.
  eexists; repeat split; eauto.
  erewrite Mem.load_store_other; eauto.
  intros ofs Hofs. eapply Mem.perm_store_1; eauto.
Qed.

Lemma cnt_inc_simp c i:
  Z.of_nat c = Int.intval i -> (c < N)%nat ->
  Z.of_nat (S c mod N) = Int.intval (Int.modu (Int.add i (Int.repr 1)) (Int.repr Nz)).
Proof.
  intros H1 H2. unfold Int.add, Int.modu.
  apply inj_le in H2. rewrite Nat2Z.inj_succ in H2.
  rewrite H1 in H2.
  repeat rewrite Int.unsigned_repr.
  all: unfold Nz in *; cbn -[Z.mul] in *; unfold Int.unsigned; try lia.
  - unfold Int.unsigned. rewrite <- H1.
    rewrite mod_Zmod.
    + f_equal. rewrite Nat2Z.inj_succ. reflexivity.
    + unfold N. lia.
  - unfold Int.unsigned. rewrite <- H1.
    exploit (Z.mod_pos_bound (Z.of_nat c + 1) (Z.of_nat N)); unfold N; lia.
Qed.

Lemma cop_sem_mod m i j:
  j <> Int.zero -> Cop.sem_mod (Vint i) tint (Vint j) tint m = Some (Vint (Int.modu i j)).
Proof.
  intros Hj. unfold Cop.sem_mod.
  unfold Cop.sem_binarith. cbn.
  unfold Cop.sem_cast. cbn.
  destruct Archi.ptr64. cbn.
  rewrite Int.eq_false; eauto.
  rewrite Int.eq_false; eauto.
Qed.

Lemma Nbound : 4 * Nz <= Ptrofs.max_unsigned. Admitted.
Lemma Nbound' : 4 * Nz <= Int.max_unsigned. Admitted.

Lemma rb_correct: forward_simulation cc_id rb_cc rb_spec (Clight.semantics2 rb_program).
Proof.
  constructor. econstructor. reflexivity. firstorder.
  intros. instantiate (1 := fun _ _ _ => _). cbn beta.
  destruct H. subst.
  set (ms := fun (s1: state rb_spec) s2 => rb_ms se2 s1 s2).
  eapply forward_simulation_plus with (match_states := ms).
  - intros. destruct q1. inv H. inv H1.
    + eexists. split.
      * econstructor; eauto.
        eapply genv_funct_symbol; eauto. reflexivity.
        unfold type_of_function. f_equal; cbn.
        constructor.
      * apply rb_ms_inc1; eauto.
        eapply genv_funct_symbol; eauto.
    + eexists. split.
      * econstructor; eauto.
        eapply genv_funct_symbol; eauto. reflexivity.
        unfold type_of_function. f_equal; cbn.
        constructor.
      * apply rb_ms_inc2; eauto.
        eapply genv_funct_symbol; eauto.
    + eexists. split.
      * econstructor; eauto.
        eapply genv_funct_symbol; eauto. reflexivity.
        unfold type_of_function. f_equal; cbn.
        constructor; eauto. constructor.
      * apply rb_ms_get; eauto.
        eapply genv_funct_symbol; eauto.
    + eexists. split.
      * econstructor; eauto.
        eapply genv_funct_symbol; eauto. reflexivity.
        unfold type_of_function. f_equal; cbn.
        constructor; eauto. constructor; eauto. constructor.
      * apply rb_ms_set; eauto.
        eapply genv_funct_symbol; eauto.
  - intros. destruct r1. inv H1. inv H.
    eexists. split. constructor. constructor. eauto.
  - intros. inv H1.
  - intros. inv H1; inv H.
    (* inc1 *)
    + inv H2. inv H6. inv H2.
      edestruct (Mem.valid_access_store m Mint32 b 0) as (m' & Hm').
      {
        constructor.
        - intros ofs Hofs. apply H5. cbn [size_chunk] in Hofs. lia.
        - apply Z.divide_0_r.
      }
      edestruct (Mem.valid_access_store m' Mint32 b 0) as (m'' & Hm'').
      {
        constructor.
        - intros ofs Hofs. eapply Mem.perm_store_1; eauto.
        - apply Z.divide_0_r.
      }
      eexists. split.
      * eapply plus_left. cbn.
        {
          constructor; eauto.
          repeat constructor. cbn. solve_list_disjoint.
        }
        lts_step. crush_step.
        lts_step. crush_step.
        lts_step. crush_step.
        lts_step. crush_step. crush_expr.
        lts_step. crush_step.
        lts_step.
        (* assign *)
        crush_step; crush_expr. now constructor.
        lts_step. crush_step.
        (* assign *)
        lts_step.
        {
          crush_step; crush_expr.
          - erewrite Mem.load_store_same; eauto.
          - apply cop_sem_mod. unfold Int.zero.
            intros contra. inv contra.
          - constructor. eauto.
        }
        lts_step. crush_step.
        lts_step. crush_step; crush_expr. now constructor.
        apply star_refl. reflexivity.
      *
        cbn. rewrite H6.
        replace (Int.repr (Int.intval i)) with i by now rewrite Int.repr_unsigned.
        constructor.
        constructor.
        (* c1 *)
        -- econstructor; eauto.
           ++ erewrite Mem.load_store_same; eauto.
           ++ cbn. constructor.
              apply cnt_inc_simp; assumption.
           ++ apply Nat.mod_upper_bound. lia.
           ++ intros ofs Hofs. eapply Mem.perm_store_1; eauto.
              eapply Mem.perm_store_1; eauto.
        (* c2 *)
        -- cut (rel_cnt se2 cnt2_id c2 m'). intros X.
           eapply rel_cnt_store_other; eauto. intros x. inv x.
           eapply rel_cnt_store_other; eauto. intros x. inv x.
        -- cut (rel_arr se2 f m'). intros X.
           eapply rel_arr_store_other; eauto. intros x. inv x.
           eapply rel_arr_store_other; eauto. intros x. inv x.
    (* inc2 *)
    + inv H2. inv H8. inv H2.
      edestruct (Mem.valid_access_store m Mint32 b 0) as (m' & Hm').
      {
        constructor.
        - intros ofs Hofs. apply H5. cbn [size_chunk] in Hofs. lia.
        - apply Z.divide_0_r.
      }
      edestruct (Mem.valid_access_store m' Mint32 b 0) as (m'' & Hm'').
      {
        constructor.
        - intros ofs Hofs. eapply Mem.perm_store_1; eauto.
        - apply Z.divide_0_r.
      }
      eexists. split.
      * eapply plus_left. cbn.
        {
          constructor; eauto.
          repeat constructor. cbn. solve_list_disjoint.
        }
        lts_step. crush_step.
        lts_step. crush_step.
        lts_step. crush_step.
        lts_step. crush_step. crush_expr.
        lts_step. crush_step.
        lts_step.
        (* assign *)
        crush_step; crush_expr. now constructor.
        lts_step. crush_step.
        (* assign *)
        lts_step.
        {
          crush_step; crush_expr.
          - erewrite Mem.load_store_same; eauto.
          - apply cop_sem_mod. unfold Int.zero.
            intros contra. inv contra.
          - constructor. eauto.
        }
        lts_step. crush_step.
        lts_step. crush_step; crush_expr. now constructor.
        apply star_refl. reflexivity.
      *
        cbn. rewrite H7.
        replace (Int.repr (Int.intval i)) with i by now rewrite Int.repr_unsigned.
        constructor.
        constructor.
        (* c1 *)
        -- cut (rel_cnt se2 cnt1_id c1 m'). intros X.
           eapply rel_cnt_store_other; eauto. intros x. inv x.
           eapply rel_cnt_store_other; eauto. intros x. inv x.
        (* c2 *)
        -- econstructor; eauto.
           ++ erewrite Mem.load_store_same; eauto.
           ++ cbn. constructor.
              apply cnt_inc_simp; assumption.
           ++ apply Nat.mod_upper_bound. lia.
           ++ intros ofs Hofs. eapply Mem.perm_store_1; eauto.
              eapply Mem.perm_store_1; eauto.
        -- cut (rel_arr se2 f m'). intros X.
           eapply rel_arr_store_other; eauto. intros x. inv x.
           eapply rel_arr_store_other; eauto. intros x. inv x.
    (* set *)
    + inv H2. inv H11.
      edestruct (Mem.valid_access_store m Mint32 b (4 * Z.of_nat i)) as (m' & Hm').
      {
        constructor.
        - intros ofs Hofs. apply H2. unfold Nz. split.
          lia. cbn [size_chunk] in Hofs. unfold N in *. lia.
        - apply Z.divide_factor_l.
      }
      eexists. split.
      * eapply plus_left.
        {
          constructor; eauto. repeat constructor. cbn.
          intros [A|A]; inv A. intros A. inv A. solve_list_disjoint.
        }
        lts_step. crush_step.
        lts_step. crush_step; crush_expr.
        {
          match goal with
          | [ H: Mem.store _ ?m ?b ?ofs ?v = Some ?m' |-
              Mem.store _ ?m ?b ?ofs' ?v' = Some _ ] =>
              replace ofs' with ofs; [ apply H | ]
          end.
          rewrite Ptrofs.add_zero_l.
          unfold Ptrofs.of_intu, Ptrofs.of_int, Ptrofs.mul.
          rewrite Int.unsigned_repr.
          repeat rewrite Ptrofs.unsigned_repr.
          all: pose proof Nbound; pose proof Nbound';
            unfold Nz in *; unfold N in *; try lia.
        }
        lts_step. crush_step.
        lts_step. crush_step; crush_expr.
        apply star_refl. reflexivity.
      * constructor. constructor.
        -- eapply rel_cnt_store_other; eauto. intros x. inv x.
        -- eapply rel_cnt_store_other; eauto. intros x. inv x.
        -- econstructor; eauto. intros ix.
           2: { intros ofs Hofs. eapply Mem.perm_store_1; eauto. }
           destruct Nat.eq_dec.
           ++ subst. intros. exists v2. split; auto.
              erewrite Mem.load_store_same; eauto.
              f_equal.
              eapply val_casted_load_result; eauto.
           ++ intros Hix. edestruct (H1 _ Hix) as (vx & Hvx & Hrv).
              exists vx; split; auto.
              erewrite Mem.load_store_other; eauto. right.
              apply not_eq in n. destruct n.
              ** right. apply inj_lt in H4. cbn [size_chunk]. lia.
              ** left. apply inj_lt in H4. cbn [size_chunk]. lia.
    (* get *)
    + inv H2. inv H10. edestruct (H1 _ H9) as (vx & Hvx & Hvr & Hrt).
      eexists. split.
      * eapply plus_left.
        {
          constructor; eauto. repeat constructor. cbn.
          easy. solve_list_disjoint.
        }
        lts_step. crush_step; crush_expr.
        {
          match goal with
          | [ H: Mem.load _ ?m ?b ?ofs = Some _ |- Mem.load _ ?m ?b ?ofs' = Some _ ] =>
              replace ofs' with ofs; [ apply H | ]
          end.
          unfold Ptrofs.of_intu, Ptrofs.of_int, Ptrofs.mul.
          rewrite Ptrofs.add_zero_l.
          rewrite Int.unsigned_repr.
          repeat rewrite Ptrofs.unsigned_repr.
          all: pose proof Nbound; pose proof Nbound';
            unfold Nz in *; unfold N in *; try lia.
        }
        apply star_refl. reflexivity.
      * subst. constructor. constructor; eauto. econstructor; eauto.
  - apply well_founded_ltof.
Qed.
