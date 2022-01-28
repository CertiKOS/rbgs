From Coq Require Import Lia.
From models Require Import
     IntSpec.
From examples Require Import
     CAL CompCertIntSpec RefConv
     CompCertCAL BoundedQueueCode.
From lattices Require Import
     Upset Downset FCD.
From structures Require Import Lattice. (* subrel *)
From compcert Require Import
     Integers Maps Coqlib
     Memory AST Values
     Clight Ctypes
     LanguageInterface
     Events Globalenvs
     Smallstep.

Import ListNotations ISpec.

(** * Example: ring buffer and bounded queue *)

Parameter cal_val_rel: CAL.val -> val -> Prop.
Hypothesis val_is_int:
  forall c v, cal_val_rel c v -> Cop.val_casted v tint.
Hint Resolve val_is_int.

Section MARSHALL.

  Inductive cal_nat_rel: nat -> val -> Prop :=
  | cal_nat_rel_intro n i:
    Z.of_nat n = Integers.Int.intval i ->
    cal_nat_rel n (Vint i).
  Inductive cal_void_rel: unit -> val -> Prop :=
  | cal_void_rel_intro: cal_void_rel tt Vundef.

  Context (se: Genv.symtbl).

  (** Refinement Conventions *)
  Inductive rb_rc: rc_rel rb_sig c_esig :=
  | rb_set_rel i v vf c_i c_v b:
    vf = Vptr b Integers.Ptrofs.zero ->
    Genv.find_symbol se set_id = Some b ->
    c_i = Vint (Integers.Int.repr (Z.of_nat i)) ->
    cal_val_rel v c_v ->
    rb_rc _ (set i v) _ (c_event vf set_sg [ c_i ; c_v ]) cal_void_rel
  | rb_get_rel i vf c_i b:
    vf = Vptr b Integers.Ptrofs.zero ->
    Genv.find_symbol se get_id = Some b ->
    c_i = Vint (Integers.Int.repr (Z.of_nat i)) ->
    rb_rc _ (CAL.get i) _ (c_event vf get_sg [ c_i ]) cal_val_rel
  | rb_inc1_rel vf b:
    vf = Vptr b Integers.Ptrofs.zero ->
    Genv.find_symbol se inc1_id = Some b ->
    rb_rc _ inc1 _ (c_event vf inc1_sg [ ]) cal_nat_rel
  | rb_inc2_rel vf b:
    vf = Vptr b Integers.Ptrofs.zero ->
    Genv.find_symbol se inc2_id = Some b ->
    rb_rc _ inc2 _ (c_event vf inc2_sg [ ]) cal_nat_rel.

  Inductive bq_rc: rc_rel bq_sig c_esig :=
  | bq_enq_rel v vf c_v b:
    vf = Vptr b Integers.Ptrofs.zero ->
    Genv.find_symbol se enq_id = Some b ->
    cal_val_rel v c_v ->
    bq_rc _ (enq v) _ (c_event vf enq_sg [ c_v ]) cal_void_rel
  | bq_deq_rel vf b:
    vf = Vptr b Integers.Ptrofs.zero ->
    Genv.find_symbol se deq_id = Some b ->
    bq_rc _ deq _ (c_event vf deq_sg [ ]) cal_val_rel.

End MARSHALL.

(* TODO: develop handy tactics *)
Tactic Notation "inf_intro" ident(x) :=
  unfold finf; rewrite !Inf.mor; apply inf_iff ; intro x; cbn.

Tactic Notation "sup_intro" ident(x) :=
  unfold fsup; rewrite !Inf.mor; apply sup_iff ; intro x; cbn.

Ltac sup_at x :=
  unfold fsup; rewrite !Sup.mor; eapply (sup_at x); cbn.

Ltac inf_at x :=
  unfold finf; rewrite !Sup.mor; eapply (inf_at x); cbn.

Lemma type_pair_des:
  forall a b c d, (a * c)%type = (b * d)%type -> a = b /\ c = d.
Proof. Admitted.

Import Ptrofs.

Lemma genv_funct_symbol se id b f (p: Clight.program):
  Genv.find_symbol se id = Some b ->
  (prog_defmap p) ! id = Some (Gfun f) ->
  Genv.find_funct (Clight.globalenv se p) (Vptr b zero) = Some f.
Proof.
  intros H1 H2.
  unfold Genv.find_funct, Genv.find_funct_ptr.
  destruct eq_dec; try congruence.
  apply Genv.find_invert_symbol in H1. cbn.
  rewrite Genv.find_def_spec. rewrite H1.
  rewrite H2. reflexivity.
Qed.

Section RB.
  Open Scope Z_scope.
  Context (se:Genv.symtbl).

  Lemma find_set b:
    Genv.find_symbol se set_id = Some b ->
    Genv.find_funct (Clight.globalenv se rb_program) (Vptr b zero) = Some (Internal rb_set).
  Proof. intros. eapply genv_funct_symbol; eauto. Qed.

  Lemma find_get b:
    Genv.find_symbol se get_id = Some b ->
    Genv.find_funct (Clight.globalenv se rb_program) (Vptr b zero) = Some (Internal rb_get).
  Proof. intros. eapply genv_funct_symbol; eauto. Qed.

  Lemma find_inc1 b:
    Genv.find_symbol se inc1_id = Some b ->
    Genv.find_funct (Clight.globalenv se rb_program) (Vptr b zero) = Some (Internal rb_inc1).
  Proof. intros. eapply genv_funct_symbol; eauto. Qed.

  Lemma find_inc2 b:
    Genv.find_symbol se inc2_id = Some b ->
    Genv.find_funct (Clight.globalenv se rb_program) (Vptr b zero) = Some (Internal rb_inc2).
  Proof. intros. eapply genv_funct_symbol; eauto. Qed.

  Hint Resolve find_get find_set find_inc1 find_inc2.

  Inductive R_cnt (id: positive): nat -> mem -> Prop :=
  | R_cnt_intro b v n m:
    Genv.find_symbol se id = Some b ->
    Mem.load Mint32 m b 0 = Some v ->
    cal_nat_rel n v -> (n < CAL.N)%nat ->
    Mem.range_perm m b 0 4 Cur Writable ->
    R_cnt id n m.

  Inductive R_arr : (nat -> CAL.val) -> mem -> Prop :=
  | R_arr_intro f b m:
    Genv.find_symbol se arr_id = Some b ->
    (forall i, exists v, Mem.load Mint32 m b (4 * Z.of_nat i) = Some v /\
                 cal_val_rel (f i) v) ->
    (forall ofs, 0 <= ofs < 4 * Nz + 4 ->
            Mem.perm m b ofs Cur Writable) ->
    R_arr f m.

  Inductive R_rb: rb_state -> mem -> Prop :=
  | R_rb_intro f c1 c2 m:
    R_cnt cnt1_id c1 m -> R_cnt cnt2_id c2 m -> R_arr f m ->
    Ple (Genv.genv_next se) (Mem.nextblock m) ->
    R_rb (f, c1, c2) m.

  Hypothesis se_valid: Genv.valid_for (erase_program bq_program) se.

  Hypothesis Nbound : 4 * Nz <= max_unsigned.
  Hypothesis Nbound' : 4 * Nz <= Int.max_unsigned.
  Hypothesis N_neq_0: Nz <> 0.

  Lemma cnt_inc_simp c i:
    Z.of_nat c = Int.intval i -> (c < CAL.N)%nat ->
    Z.of_nat (S c mod CAL.N) = Int.intval (Int.modu (Int.add i (Int.repr 1)) (Int.repr Nz)).
  Proof.
    intros H1 H2. unfold Int.add, Int.modu.
    apply inj_le in H2. rewrite Nat2Z.inj_succ in H2.
    rewrite H1 in H2.
    repeat rewrite Int.unsigned_repr.
    all: unfold Nz in *; cbn -[Z.mul] in *; unfold Int.unsigned; try lia.
    - unfold Int.unsigned. rewrite <- H1.
      rewrite mod_Zmod.
      + f_equal. rewrite Nat2Z.inj_succ. reflexivity.
      + lia.
    - unfold Int.unsigned. rewrite <- H1.
      exploit (Z.mod_pos_bound (Z.of_nat c + 1) (Z.of_nat CAL.N)); lia.
  Qed.

  Local Opaque semantics2 normalize_rc.

  Lemma rb_code_correct:
    L_rb [= (right_arrow (rb_rc se * rel_rc R_rb)%rc)
         @ (right_arrow c_rc)
         @ ang_lts_spec (semantics2 rb_program se) @ bot.
  Proof.
    intros ? [? ? m [ s ]]. destruct s as [ [ f c1 ] c2 ].

    unfold compose. cbn. unfold rc_adj_right. cbn.
    inf_intro ar. inf_intro x. destruct x as [ ? ? c_m [ mm ] ].
    destruct c_m as [vf sg args].
    inf_intro x. destruct x as [ Rp Hr ]. cbn.
    intm. inf_intro ar'. inf_intro q. destruct q as [ q ].
    inf_intro x. destruct x as [ Rc Hc ]. cbn.
    intm. simple inversion Hc. intros. depsubst.
    inv H3. inv H5. clear Hc H2 H4. rename H1 into HRc.
    (* destruct Hr as (Rx & Hx & Hy). *)
    (* inversion Hx. depsubst. *)
    (* rc_inversion Hr. *)
    destruct Hr as (Rx & Hr & HRp).
    inversion Hr. depsubst. clear H H0 H6 H7.
    rename H2 into HRev. rename H13 into HRst.

    destruct HRev as (Rev & HRev & Hx).
    destruct HRst as (Rst & HRst & Hy).
    inv HRst. depsubst.
    unfold fsup. setoid_rewrite Sup.mor.
    setoid_rewrite FCD.ext_ana. cbn.
    rewrite <- Sup.mor.
    inv HRev; depsubst.
    (* simple inversion HRev; intros; depsubst; clear HRev. *)

    (* simple inversion Hr. depsubst. *)
    (* apply type_pair_des in H2. inv H2. *)
    (* apply type_pair_des in H4. inv H4. *)
    (* depsubst. inv H3. inv H5. *)
    (* depsubst. cbn. intros HRev HRst HRp. *)
    (* simple inversion HRst. depsubst. clear H1 H3 Hr. inv H2. inv H4. *)
    (* clear HRst. intros HRst HRx. *)
    (* unfold fsup. setoid_rewrite Sup.mor. *)
    (* setoid_rewrite FCD.ext_ana. cbn. *)
    (* rewrite <- Sup.mor. *)
    (* simple inversion HRev; intros; depsubst; clear HRev. *)
    (* set *)
    - clear H H6. clear Hr.
      (* inv H8. *)
      apply assert_l. intros Hi. apply inj_lt in Hi.
      rename H9 into Hb. rename H11 into Hv. rename H2 into HRst.
      setoid_rewrite sup_sup. rewrite !Sup.mor.
      (* initial_state *)
      eapply (sup_at (exist _ _ _)); cbn. Unshelve.
      3: { cbn. repeat econstructor; eauto. inv HRst. eauto. }
      cbn. rewrite lts_spec_step.
      rewrite !Sup.mor_join. apply join_l. apply join_l.
      unfold fsup. rewrite !Sup.mor.
      (* internal steps *)
      inv HRst. inv H5. rename mm into m.
      edestruct (Mem.valid_access_store m Mint32 b0 (4 * Z.of_nat i)) as (m' & Hm').
      {
        constructor.
        - intros ofs Hofs. apply H1. unfold Nz. split.
          lia. cbn [size_chunk] in Hofs. lia.
        - apply Z.divide_factor_l.
      }
      eapply (sup_at (exist _ _ _)); cbn. Unshelve.
      4: {
        cbn. crush_star.
        match goal with
        | [ H: Mem.store _ ?m ?b ?ofs ?v = Some ?m' |- Mem.store _ ?m ?b ?ofs' ?v' = Some _ ] =>
            replace ofs' with ofs; [ apply H | ]
        end.
        rewrite add_zero_l.
        unfold of_intu, of_int, mul.
        rewrite Int.unsigned_repr.
        repeat rewrite unsigned_repr.
        all: unfold Nz in *; try lia.
      }
      (* final step *)
      rewrite lts_spec_step. rewrite !Sup.mor_join.
      apply join_r. unfold fsup.
      rewrite !Sup.mor. eapply (sup_at (exist _ _ _)); cbn.
      Unshelve. 3: { cbn. econstructor. } cbn.
      (* re-establish the relation *)
      setoid_rewrite FCD.ext_ana. cbn.
      setoid_rewrite FCD.ext_ana. cbn.
      rewrite !Sup.mor.
      eapply (sup_at (exist _ (Vundef, m') _)); cbn. Unshelve.
      2: { cbn. apply HRc. reflexivity. } cbn.
      setoid_rewrite FCD.ext_ana. cbn.
      eapply (sup_at (exist _ (tt, (update f i v, c1, c2)) _)). Unshelve.
      2: {
        cbn. apply HRp. split.
        - now apply Hx.
        - apply Hy. cbn. constructor.
          + destruct H2. econstructor; eauto.
            erewrite Mem.load_store_other; eauto.
            left. intros Hbb. subst.
            exploit Genv.find_symbol_injective. apply H2. apply H.
            intros. easy.
            intros ofs Hofs. eapply Mem.perm_store_1; eauto.
          + destruct H3. econstructor; eauto.
            erewrite Mem.load_store_other; eauto.
            left. intros Hbb. subst.
            exploit Genv.find_symbol_injective. apply H3. apply H.
            intros. easy.
            intros ofs Hofs. eapply Mem.perm_store_1; eauto.
          + econstructor; eauto. intros ix.
            * unfold update in *. destruct Nat.eq_dec.
              -- subst. exists c_v. split; auto.
                 erewrite Mem.load_store_same; eauto.
                 f_equal.
                 eapply SimplLocalsproof.val_casted_load_result.
                 eapply val_is_int; eauto. reflexivity.
              -- edestruct (H0 ix) as (vx & Hvx & Hrv).
                 exists vx; split; auto.
                 erewrite Mem.load_store_other; eauto. right.
                 apply not_eq in n. destruct n.
                 ++ right. apply inj_lt in H4. cbn [size_chunk]. lia.
                 ++ left. apply inj_lt in H4. cbn [size_chunk]. lia.
            * intros ofs Hofs. eapply Mem.perm_store_1; eauto.
          + erewrite Mem.nextblock_store; eauto.
      } cbn. reflexivity.
    (* get *)
    - clear H H6 Hr.
      (* inv H7. *)
      apply assert_l. intros Hi.
      rename H9 into Hb. rename H2 into HRst.
      setoid_rewrite sup_sup. rewrite !Sup.mor.
      (* initial_state *)
      eapply (sup_at (exist _ _ _)); cbn. Unshelve.
      3: { cbn. repeat econstructor; eauto. inv HRst. eauto. }
      rewrite lts_spec_step.
      rewrite !Sup.mor_join. apply join_l. apply join_l.
      unfold fsup. rewrite !Sup.mor.
      (* internal steps *)
      inv HRst. inv H5. rename mm into m.
      edestruct (H0 i) as (vx & Hvx & Hvr).
      eapply (sup_at (exist _ _ _)); cbn. Unshelve.
      3: {
        cbn. crush_star.
        match goal with
        | [ H: Mem.load _ ?m ?b ?ofs = Some _ |- Mem.load _ ?m ?b ?ofs' = Some _ ] =>
            replace ofs' with ofs; [ apply H | ]
        end.
        unfold of_intu, of_int, mul.
        rewrite add_zero_l.
        rewrite Int.unsigned_repr.
        repeat rewrite unsigned_repr.
        all: unfold Nz in *; try lia.
      }
      (* final state *)
      rewrite lts_spec_step. rewrite !Sup.mor_join.
      apply join_r. unfold fsup.
      rewrite !Sup.mor. eapply (sup_at (exist _ _ _)); cbn.
      Unshelve. 3: { cbn. econstructor. } cbn.
      (* re-establish the relation *)
      setoid_rewrite FCD.ext_ana. cbn.
      setoid_rewrite FCD.ext_ana. cbn.
      rewrite !Sup.mor.
      eapply (sup_at (exist _ (vx, m) _)); cbn. Unshelve.
      2: { cbn. apply HRc. reflexivity. } cbn.
      setoid_rewrite FCD.ext_ana. cbn.
      eapply (sup_at (exist _ (f i, (f, c1, c2)) _)); cbn.
      Unshelve.
      2: {
        cbn. apply HRp. split; eauto.
        apply Hy. cbn. constructor; eauto.
        econstructor; eauto.
      }
      reflexivity.
    (* inc1 *)
    - clear H H7.
      rename H9 into Hb. rename H2 into HRst.
      setoid_rewrite sup_sup. rewrite !Sup.mor.
      (* initial_state *)
      eapply (sup_at (exist _ _ _)); cbn. Unshelve.
      3: { cbn. repeat econstructor; eauto. inv HRst; eauto. }
      rewrite lts_spec_step.
      rewrite !Sup.mor_join. apply join_l. apply join_l.
      unfold fsup. rewrite !Sup.mor.
      inv HRst. inv H2.
      (* internal steps *)
      inv H1. rename mm into m.
      edestruct (Mem.valid_access_store m Mint32 b0 0) as (m' & Hm').
      {
        constructor.
        - intros ofs Hofs. apply H7. cbn [size_chunk] in Hofs. lia.
        - apply Z.divide_0_r.
      }
      edestruct (Mem.valid_access_store m' Mint32 b0 0) as (m'' & Hm'').
      {
        constructor.
        - intros ofs Hofs. eapply Mem.perm_store_1; eauto.
        - apply Z.divide_0_r.
      }
      eapply (sup_at (exist _ _ _)); cbn. Unshelve.
      5: {
        cbn.
        do 7 (lts_step; [ crush_step; crush_expr | ]). now constructor.
        do 2 (lts_step; [ crush_step; crush_expr | ]). erewrite Mem.load_store_same; eauto.

        unfold Cop.sem_mod.
        unfold Cop.sem_binarith. cbn.
        unfold Cop.sem_cast. cbn.
        destruct Archi.ptr64. cbn.
        rewrite Int.eq_false. reflexivity.
        intros contra. assert (Int.unsigned (Int.repr Nz) = 0).
        rewrite contra. rewrite Int.unsigned_zero. reflexivity.
        rewrite Int.unsigned_repr in H1. easy.
        unfold Nz in *. lia.
        rewrite Int.eq_false. reflexivity.
        intros contra. assert (Int.unsigned (Int.repr Nz) = 0).
        rewrite contra. rewrite Int.unsigned_zero. reflexivity.
        rewrite Int.unsigned_repr in H1. easy.
        unfold Nz in *. lia.

        now constructor.
        crush_star. now constructor.
      }
      rewrite lts_spec_step. rewrite !Sup.mor_join. apply join_r.
      unfold fsup. rewrite !Sup.mor. eapply (sup_at (exist _ _ _)); cbn.
      Unshelve. 3: { cbn. econstructor. } cbn.
      (* re-establish the relation *)
      setoid_rewrite FCD.ext_ana. cbn.
      setoid_rewrite FCD.ext_ana. cbn.
      rewrite !Sup.mor.
      eapply (sup_at (exist _ (Vint i, m'') _)); cbn. Unshelve.
      2: { cbn. apply HRc. reflexivity. } cbn.
      setoid_rewrite FCD.ext_ana. cbn.
      eapply (sup_at (exist _ (c1, (f, (S c1 mod CAL.N)%nat, c2)) _)); cbn.
      Unshelve.
      2: {
        cbn. apply HRp. split; eauto.
        - apply Hx. cbn. now constructor.
        - apply Hy. cbn. constructor; eauto.
          + econstructor; eauto.
            * erewrite Mem.load_store_same; eauto.
            * cbn. constructor.
              apply cnt_inc_simp; assumption.
            * apply Nat.mod_upper_bound. lia.
            * intros ofs Hofs. eapply Mem.perm_store_1; eauto.
              eapply Mem.perm_store_1; eauto.
          + inv H3. econstructor; eauto.
            * assert (b1 <> b0).
              { intros <-. exploit Genv.find_symbol_injective.
                apply H. apply H1. easy. }
              erewrite Mem.load_store_other. 2: apply Hm''. 2: left; auto.
              erewrite Mem.load_store_other; eauto.
            * intros ofs Hofs. eapply Mem.perm_store_1; eauto.
              eapply Mem.perm_store_1; eauto.
          + inv H5. assert (b0 <> b1).
            { intros <-. exploit Genv.find_symbol_injective.
              apply H. apply H1. easy. }
            econstructor; eauto.
            * intros ix. edestruct (H8 ix) as (vx & Hvx & Hrx).
              exists vx. split; eauto.
              erewrite Mem.load_store_other. 2: apply Hm''. 2: left; auto.
              erewrite Mem.load_store_other; eauto.
            * intros ofs Hofs. eapply Mem.perm_store_1; eauto.
              eapply Mem.perm_store_1; eauto.
          + erewrite Mem.nextblock_store. 2: apply Hm''.
            erewrite Mem.nextblock_store; eauto.
      }
      reflexivity.
    (* inc2 *)
    - clear H H7.
      (* inv H6. *)
      rename H9 into Hb. rename H2 into HRst.
      setoid_rewrite sup_sup. rewrite !Sup.mor.
      (* initial_state *)
      eapply (sup_at (exist _ _ _)); cbn. Unshelve.
      3: { cbn. repeat econstructor; eauto. inv HRst; eauto. }
      rewrite lts_spec_step.
      rewrite !Sup.mor_join. apply join_l. apply join_l.
      unfold fsup. rewrite !Sup.mor.
      inv HRst. inv H3.
      (* internal steps *)
      inv H1. rename mm into m.
      edestruct (Mem.valid_access_store m Mint32 b0 0) as (m' & Hm').
      {
        constructor.
        - intros ofs Hofs. apply H7. cbn [size_chunk] in Hofs. lia.
        - apply Z.divide_0_r.
      }
      edestruct (Mem.valid_access_store m' Mint32 b0 0) as (m'' & Hm'').
      {
        constructor.
        - intros ofs Hofs. eapply Mem.perm_store_1; eauto.
        - apply Z.divide_0_r.
      }
      eapply (sup_at (exist _ _ _)); cbn. Unshelve.
      5: {
        cbn.
        do 7 (lts_step; [ crush_step; crush_expr | ]). now constructor.
        do 2 (lts_step; [ crush_step; crush_expr | ]). erewrite Mem.load_store_same; eauto.

        unfold Cop.sem_mod.
        unfold Cop.sem_binarith. cbn.
        unfold Cop.sem_cast. cbn.
        destruct Archi.ptr64. cbn.
        rewrite Int.eq_false. reflexivity.
        intros contra. assert (Int.unsigned (Int.repr Nz) = 0).
        rewrite contra. rewrite Int.unsigned_zero. reflexivity.
        rewrite Int.unsigned_repr in H1. easy.
        unfold Nz in *. lia.
        rewrite Int.eq_false. reflexivity.
        intros contra. assert (Int.unsigned (Int.repr Nz) = 0).
        rewrite contra. rewrite Int.unsigned_zero. reflexivity.
        rewrite Int.unsigned_repr in H1. easy.
        unfold Nz in *. lia.

        now constructor.
        crush_star. now constructor.
      }
      rewrite lts_spec_step. rewrite !Sup.mor_join. apply join_r.
      unfold fsup. rewrite !Sup.mor. eapply (sup_at (exist _ _ _)); cbn.
      Unshelve. 3: { cbn. econstructor. } cbn.
      (* re-establish the relation *)
      setoid_rewrite FCD.ext_ana. cbn.
      setoid_rewrite FCD.ext_ana. cbn.
      rewrite !Sup.mor.
      eapply (sup_at (exist _ (Vint i, m'') _)); cbn. Unshelve.
      2: { cbn. apply HRc. reflexivity. } cbn.
      setoid_rewrite FCD.ext_ana. cbn.
      eapply (sup_at (exist _ (c2, (f, c1, (S c2 mod CAL.N)%nat)) _)); cbn.
      Unshelve.
      2: {
        cbn. apply HRp. split; eauto.
        - apply Hx. cbn. now constructor.
        - apply Hy. cbn. constructor; eauto.
          + inv H2. econstructor; eauto.
            * assert (b1 <> b0).
              { intros <-. exploit Genv.find_symbol_injective.
                apply H. apply H1. easy. }
              erewrite Mem.load_store_other. 2: apply Hm''. 2: left; auto.
              erewrite Mem.load_store_other; eauto.
            * intros ofs Hofs. eapply Mem.perm_store_1; eauto.
              eapply Mem.perm_store_1; eauto.
          + econstructor; eauto.
            * erewrite Mem.load_store_same; eauto.
            * cbn. constructor.
              apply cnt_inc_simp; assumption.
            * apply Nat.mod_upper_bound. lia.
            * intros ofs Hofs. eapply Mem.perm_store_1; eauto.
              eapply Mem.perm_store_1; eauto.
          + inv H5. assert (b0 <> b1).
            { intros <-. exploit Genv.find_symbol_injective.
              apply H. apply H1. easy. }
            econstructor; eauto.
            * intros ix. edestruct (H8 ix) as (vx & Hvx & Hrx).
              exists vx. split; eauto.
              erewrite Mem.load_store_other. 2: apply Hm''. 2: left; auto.
              erewrite Mem.load_store_other; eauto.
            * intros ofs Hofs. eapply Mem.perm_store_1; eauto.
              eapply Mem.perm_store_1; eauto.
          + erewrite Mem.nextblock_store. 2: apply Hm''.
            erewrite Mem.nextblock_store; eauto.
      }
      reflexivity.
  Qed.

End RB.

Section BQ.
  Context (se: Genv.symtbl).

  Lemma find_enq b:
    Genv.find_symbol se enq_id = Some b ->
    Genv.find_funct (Clight.globalenv se bq_program) (Vptr b zero) = Some (Internal bq_enq).
  Proof. intros. eapply genv_funct_symbol; eauto. Qed.

  Lemma find_deq b:
    Genv.find_symbol se deq_id = Some b ->
    Genv.find_funct (Clight.globalenv se bq_program) (Vptr b zero) = Some (Internal bq_deq).
  Proof. intros. eapply genv_funct_symbol; eauto. Qed.

  Hint Resolve find_enq find_deq.

  Context (Hse: Genv.valid_for (erase_program bq_program) se).

  Lemma inc2_block:
    exists b, Genv.find_symbol (globalenv ((semantics2 bq_program) se)) inc2_id = Some b /\
           Genv.find_funct (globalenv ((semantics2 bq_program) se)) (Vptr b zero) = Some inc2_ext.
  Proof.
    eapply Genv.find_def_symbol with (id := inc2_id) in Hse .
    edestruct (proj1 Hse) as (b & Hb1 & Hb2). reflexivity.
    exists b. split; eauto. eapply genv_funct_symbol; eauto.
  Qed.

  Lemma set_block:
    exists b, Genv.find_symbol (globalenv ((semantics2 bq_program) se)) set_id = Some b /\
           Genv.find_funct (globalenv ((semantics2 bq_program) se)) (Vptr b zero) = Some set_ext.
  Proof.
    eapply Genv.find_def_symbol with (id := set_id) in Hse .
    edestruct (proj1 Hse) as (b & Hb1 & Hb2). reflexivity.
    exists b. split; eauto. eapply genv_funct_symbol; eauto.
  Qed.

  Lemma inc1_block:
    exists b, Genv.find_symbol (globalenv ((semantics2 bq_program) se)) inc1_id = Some b /\
           Genv.find_funct (globalenv ((semantics2 bq_program) se)) (Vptr b zero) = Some inc1_ext.
  Proof.
    eapply Genv.find_def_symbol with (id := inc1_id) in Hse .
    edestruct (proj1 Hse) as (b & Hb1 & Hb2). reflexivity.
    exists b. split; eauto. eapply genv_funct_symbol; eauto.
  Qed.

  Lemma get_block:
    exists b, Genv.find_symbol (globalenv ((semantics2 bq_program) se)) get_id = Some b /\
           Genv.find_funct (globalenv ((semantics2 bq_program) se)) (Vptr b zero) = Some get_ext.
  Proof.
    eapply Genv.find_def_symbol with (id := get_id) in Hse .
    edestruct (proj1 Hse) as (b & Hb1 & Hb2). reflexivity.
    exists b. split; eauto. eapply genv_funct_symbol; eauto.
  Qed.

  Variable S: Type.
  Variable R: S -> mem -> Prop.

  Hypothesis R_ple: forall s m, R s m -> Ple (Genv.genv_next se) (Mem.nextblock m).
  Local Opaque Genv.find_funct.
  Local Opaque semantics2.
  Local Opaque normalize_rc.

  Lemma bq_code_correct:
    slift M_bq [= (right_arrow (bq_rc se * rel_rc R)%rc)
               @ (right_arrow c_rc)
               @ ang_lts_spec (semantics2 bq_program se)
               @ (left_arrow c_rc)
               @ (left_arrow (rb_rc se * rel_rc R)%rc).
  Proof.
    intros ? [? ? m [ s ]].
    unfold compose. cbn. unfold rc_adj_right. cbn.
    inf_intro ar. inf_intro x. destruct x as [ ? ? c_m [ mm ] ].
    destruct c_m as [vf sg args].
    inf_intro x. destruct x as [ Rp Hr ]. cbn.
    intm. inf_intro ar'. inf_intro q. destruct q as [ q ].
    inf_intro x. destruct x as [ Rc Hc ]. cbn.
    intm. simple inversion Hc. intros. depsubst.
    inv H3. inv H5. clear Hc H2 H4. rename H1 into HRc.

    destruct Hr as (Rx & Hr & Hsub). inversion Hr; clear Hr.
    depsubst. clear H H0 H6 H7.
    rename H2 into HRev. rename H13 into HRst.

    destruct HRev as (Rev & HRev & Hx).
    destruct HRst as (Rst & HRst & Hy).
    inv HRst. depsubst.
    unfold fsup. setoid_rewrite Sup.mor.
    setoid_rewrite FCD.ext_ana. cbn.
    rewrite <- Sup.mor.
    inv HRev; depsubst.

    (* simple inversion Hr. *)
    (* apply type_pair_des in H2. inv H2. *)
    (* apply type_pair_des in H4. inv H4. *)
    (* depsubst. inv H3. inv H5. *)
    (* depsubst. cbn. intros HRev HRst HRp. *)
    (* simple inversion HRst. depsubst. clear H1 H3 Hr. inv H2. inv H4. *)
    (* clear HRst. intros HRst HRx. *)
    (* unfold fsup. setoid_rewrite Sup.mor. *)
    (* setoid_rewrite FCD.ext_ana. cbn. *)
    (* rewrite <- Sup.mor. *)
    (* simple inversion HRev; intros; depsubst; clear HRev. *)

    (* enq *)
    - clear H H0 H7.
      rename H10 into Hb. rename H11 into Hv. rename H3 into HRst.
      edestruct inc2_block as (inc2b & Hb1 & Hb2).
      edestruct set_block as (setb & Hb3 & Hb4).
      setoid_rewrite sup_sup.
      rewrite !Sup.mor. eapply (sup_at (exist _ _ _)); cbn.
      Unshelve.
      3: { cbn. repeat econstructor; eauto. }
      rewrite lts_spec_step.
      rewrite !Sup.mor_join. apply join_l. apply join_l.
      unfold fsup. rewrite !Sup.mor.
      eapply (sup_at (exist _ _ _)). cbn.
      Unshelve.
      3: { cbn. crush_star. apply star_refl. }
      (* external call to [inc2] *)
      rewrite lts_spec_step.
      rewrite !Sup.mor_join. apply join_l. apply join_r.
      unfold fsup. rewrite !Sup.mor.
      eapply (sup_at (exist _ _ _)); cbn.
      Unshelve.
      3: { cbn. econstructor. eauto. }
      unfold query_int.
      rewrite srun_bind. rewrite srun_int.
      rewrite apply_bind. rewrite apply_int_r.
      unfold rc_adj_left.
      rewrite !Sup.mor. eapply (sup_at _).
      rewrite !Sup.mor. eapply (sup_at _).
      unfold fsup. rewrite !Sup.mor. eapply (sup_at (exist _ _ _)). cbn.
      Unshelve.
      5: { cbn. constructor; try reflexivity.
           instantiate (1 := (fun '(r, m) (c_r : c_reply) => c_r = cr r m)).
           reflexivity. }
      intm.
      rewrite !Sup.mor. eapply (sup_at _).
      rewrite !Sup.mor. eapply (sup_at _).
      rewrite !Sup.mor. eapply (sup_at (exist _ _ _)). cbn.
      Unshelve.
      5: {
        cbn. rc_econstructor.
        (* fix here *)
        - eexists. split. 2: reflexivity. eapply rb_inc2_rel; eauto.
        - rc_econstructor.
      }
      unfold ISpec.int at 2 6.
      rewrite !Sup.mor. apply sup_iff. intros ons. apply (sup_at ons).
      destruct ons as [ [ n s' ] | ].
      2: {
        setoid_rewrite FCD.ext_ana; cbn.
        setoid_rewrite FCD.ext_ana; cbn. reflexivity.
      }
      setoid_rewrite FCD.ext_ana. cbn. rewrite !Sup.mor_join.
      apply join_lub.
      { apply join_l. setoid_rewrite FCD.ext_ana; cbn. reflexivity. }
      apply join_r.
      inf_intro x. destruct x as [ [vr m'] Hm']. cbn.
      inv Hm'. inv H. cbn [fst snd] in *. subst.
      setoid_rewrite FCD.ext_ana.
      setoid_rewrite FCD.ext_ana. cbn. apply join_r. rstep.
      inf_intro x. destruct x as [ r_c Hrc ]. cbn.
      inv Hrc.
      setoid_rewrite FCD.ext_ana. cbn.
      setoid_rewrite FCD.ext_ana. cbn.
      rewrite !Sup.mor. eapply (sup_at (exist _ _ _)); cbn.
      Unshelve.
      3: { cbn. constructor. }
      (* internal steps before calling [set] *)
      rewrite lts_spec_step.
      rewrite !Sup.mor_join. apply join_l. apply join_l.
      unfold fsup. rewrite !Sup.mor.
      eapply (sup_at (exist _ _ _)); cbn. Unshelve.
      3: { cbn. crush_star. now constructor. apply star_refl. }
      (* external call to [set] *)
      rewrite lts_spec_step.
      rewrite !Sup.mor_join. apply join_l. apply join_r.
      unfold fsup. rewrite !Sup.mor.
      eapply (sup_at (exist _ _ _)); cbn. Unshelve.
      3: { cbn. econstructor. eauto. }
      rewrite srun_int. unfold query_int.
      intm.
      rewrite !Sup.mor. eapply (sup_at _).
      rewrite !Sup.mor. eapply (sup_at _).
      rewrite !Sup.mor. eapply (sup_at (exist _ _ _)). cbn.
      Unshelve.
      5: {
        cbn. constructor; try reflexivity.
        instantiate (1 := (fun '(r, m) (c_r : c_reply) => c_r = cr r m)). reflexivity.
      }
      intm.
      rewrite !Sup.mor. eapply (sup_at _).
      rewrite !Sup.mor. eapply (sup_at _).
      rewrite !Sup.mor. eapply (sup_at (exist _ _ _)). cbn.
      Unshelve.
      5: {
        cbn. repeat econstructor; try reflexivity; eauto.
        rewrite H1. rewrite Int.repr_unsigned. reflexivity.
      }
      unfold ISpec.int at 1 5. rewrite !Sup.mor.
      apply sup_iff. intros oret. apply (sup_at oret).
      destruct oret as [ [? s''] | ].
      2: {
        setoid_rewrite FCD.ext_ana. cbn.
        setoid_rewrite FCD.ext_ana. cbn. reflexivity.
      }
      setoid_rewrite FCD.ext_ana. cbn.
      rewrite Sup.mor_join. apply join_r.
      inf_intro x. destruct x as [ [rv m''] Hrm ]. cbn.
      inv Hrm. inv H. cbn [fst snd] in *. subst.
      setoid_rewrite FCD.ext_ana. cbn.
      setoid_rewrite FCD.ext_ana. cbn.
      apply join_r.
      inf_intro x. destruct x as [ rc Hrc ]. cbn.
      inv Hrc.
      setoid_rewrite FCD.ext_ana. cbn.
      setoid_rewrite FCD.ext_ana. cbn.
      replace (FCD.emb (pcons (st (set n v) s') (tt, s'') (pret (tt, s''))))
        with (FCD.ext (fun s => FCD.emb (pcons (st (set n v) s') (tt, s'') s)) (ret (tt, s''))).
      2: { setoid_rewrite FCD.ext_ana. reflexivity. }
      rstep.
      rewrite !Sup.mor. eapply (sup_at (exist _ _ _)); cbn.
      Unshelve.
      3: { cbn. constructor. }

      rewrite lts_spec_step. rewrite !Sup.mor_join.
      apply join_l. apply join_l.
      unfold fsup. rewrite !Sup.mor. eapply (sup_at (exist _ _ _)); cbn.
      Unshelve.
      3: { cbn. crush_star. }
      (* final state *)
      rewrite lts_spec_step. rewrite !Sup.mor_join. apply join_r.
      unfold fsup. rewrite !Sup.mor. eapply (sup_at (exist _ _ _)).
      cbn. Unshelve.
      3: { cbn. constructor. }
      setoid_rewrite FCD.ext_ana. cbn.
      setoid_rewrite FCD.ext_ana. cbn.
      rewrite Sup.mor. eapply (sup_at (exist _ (_, _) _)).
      Unshelve.
      4: { cbn. apply HRc. reflexivity. }
      setoid_rewrite FCD.ext_ana. cbn.
      eapply (sup_at (exist _ (_, _) _)).
      Unshelve.
      4: {
        cbn. apply Hsub. split; eauto.
        (* fix here: hint constructor *)
        apply Hx. constructor.
      }
      cbn. reflexivity.
    (* deq *)
    - clear H H0 H8.
      rename H10 into Hb. rename H3 into HRst.
      edestruct inc1_block as (inc1b & Hb1 & Hb2).
      edestruct get_block as (getb & Hb3 & Hb4).
      (* initial_state *)
      setoid_rewrite sup_sup.
      rewrite !Sup.mor. eapply (sup_at (exist _ _ _)); cbn.
      Unshelve.
      3: { cbn. repeat econstructor; eauto. }
      rewrite lts_spec_step.
      rewrite !Sup.mor_join. apply join_l. apply join_l.
      unfold fsup. rewrite !Sup.mor.
      eapply (sup_at (exist _ _ _)). cbn.
      Unshelve.
      3: { cbn. crush_star. apply star_refl. }
      (* external call to [inc1] *)
      rewrite lts_spec_step.
      rewrite !Sup.mor_join. apply join_l. apply join_r.
      unfold fsup. rewrite !Sup.mor.
      eapply (sup_at (exist _ _ _)); cbn.
      Unshelve.
      3: { cbn. econstructor. eauto. }
      unfold query_int.
      rewrite srun_bind. rewrite srun_int.
      rewrite apply_bind. rewrite apply_int_r.
      unfold rc_adj_left.
      rewrite !Sup.mor. eapply (sup_at _).
      rewrite !Sup.mor. eapply (sup_at _).
      unfold fsup. rewrite !Sup.mor. eapply (sup_at (exist _ _ _)). cbn.
      Unshelve.
      5: { cbn. constructor; try reflexivity.
           instantiate (1 := (fun '(r, m) (c_r : c_reply) => c_r = cr r m)).
           reflexivity. }
      intm.
      rewrite !Sup.mor. eapply (sup_at _).
      rewrite !Sup.mor. eapply (sup_at _).
      rewrite !Sup.mor. eapply (sup_at (exist _ _ _)). cbn.
      Unshelve.
      5: {
        cbn. rc_econstructor.
        - eexists. split. 2: reflexivity.
          eapply rb_inc1_rel; eauto.
        - rc_econstructor.
      }
      unfold ISpec.int at 2 6.
      rewrite !Sup.mor. apply sup_iff. intros ons. apply (sup_at ons).
      destruct ons as [ [ n s' ] | ].
      2: {
        setoid_rewrite FCD.ext_ana; cbn.
        setoid_rewrite FCD.ext_ana; cbn. reflexivity.
      }
      setoid_rewrite FCD.ext_ana. cbn. rewrite !Sup.mor_join.
      apply join_lub.
      { apply join_l. setoid_rewrite FCD.ext_ana; cbn. reflexivity. }
      apply join_r.
      inf_intro x. destruct x as [ [vr m'] Hm']. cbn.
      inv Hm'. inv H. cbn [fst snd] in *. subst.
      setoid_rewrite FCD.ext_ana.
      setoid_rewrite FCD.ext_ana. cbn. apply join_r. rstep.
      inf_intro x. destruct x as [ r_c Hrc ]. cbn.
      inv Hrc.
      setoid_rewrite FCD.ext_ana. cbn.
      setoid_rewrite FCD.ext_ana. cbn.
      rewrite !Sup.mor. eapply (sup_at (exist _ _ _)); cbn.
      Unshelve.
      3: { cbn. constructor. }
      (* internal steps before calling [get] *)
      rewrite lts_spec_step.
      rewrite !Sup.mor_join. apply join_l. apply join_l.
      unfold fsup. rewrite !Sup.mor.
      eapply (sup_at (exist _ _ _)); cbn. Unshelve.
      3: { cbn. crush_star. now constructor. apply star_refl. }
      (* external call to [get] *)
      rewrite lts_spec_step.
      rewrite !Sup.mor_join. apply join_l. apply join_r.
      unfold fsup. rewrite !Sup.mor.
      eapply (sup_at (exist _ _ _)); cbn. Unshelve.
      3: { cbn. econstructor. eauto. }
      rewrite srun_int. unfold query_int.
      intm.
      rewrite !Sup.mor. eapply (sup_at _).
      rewrite !Sup.mor. eapply (sup_at _).
      rewrite !Sup.mor. eapply (sup_at (exist _ _ _)). cbn.
      Unshelve.
      5: {
        cbn. constructor; try reflexivity.
        instantiate (1 := (fun '(r, m) (c_r : c_reply) => c_r = cr r m)).
        reflexivity.
      }
      intm.
      rewrite !Sup.mor. eapply (sup_at _).
      rewrite !Sup.mor. eapply (sup_at _).
      rewrite !Sup.mor. eapply (sup_at (exist _ _ _)). cbn.
      Unshelve.
      5: {
        cbn. repeat econstructor; try reflexivity; eauto.
        rewrite H1. rewrite Int.repr_unsigned. reflexivity.
      }
      unfold ISpec.int at 1 5. rewrite !Sup.mor.
      apply sup_iff. intros oret. apply (sup_at oret).
      destruct oret as [ [? s''] | ].
      2: {
        setoid_rewrite FCD.ext_ana. cbn.
        setoid_rewrite FCD.ext_ana. cbn. reflexivity.
      }
      setoid_rewrite FCD.ext_ana. cbn.
      rewrite Sup.mor_join. apply join_r.
      inf_intro x. destruct x as [ [rv m''] Hrm ]. cbn.
      inv Hrm. cbn [fst snd] in *.
      setoid_rewrite FCD.ext_ana. cbn.
      setoid_rewrite FCD.ext_ana. cbn.
      apply join_r.
      inf_intro x. destruct x as [ rc Hrc ]. cbn.
      inv Hrc.
      setoid_rewrite FCD.ext_ana. cbn.
      setoid_rewrite FCD.ext_ana. cbn.
      replace (FCD.emb (pcons (st (CAL.get n) s') (v, s'') (pret (v, s''))))
        with (FCD.ext (fun s => FCD.emb (pcons (st (CAL.get n) s') (v, s'') s)) (ret (v, s''))).
      2: { setoid_rewrite FCD.ext_ana. reflexivity. }
      rstep.
      rewrite !Sup.mor. eapply (sup_at (exist _ _ _)); cbn.
      Unshelve.
      3: { cbn. constructor. }

      rewrite lts_spec_step. rewrite !Sup.mor_join.
      apply join_l. apply join_l.
      unfold fsup. rewrite !Sup.mor. eapply (sup_at (exist _ _ _)); cbn.
      Unshelve.
      3: { cbn. crush_star. }
      (* final state *)
      rewrite lts_spec_step. rewrite !Sup.mor_join. apply join_r.
      unfold fsup. rewrite !Sup.mor. eapply (sup_at (exist _ _ _)).
      cbn. Unshelve.
      3: { cbn. constructor. }
      setoid_rewrite FCD.ext_ana. cbn.
      setoid_rewrite FCD.ext_ana. cbn.
      rewrite Sup.mor. eapply (sup_at (exist _ (_, _) _)).
      Unshelve.
      4: { cbn. apply HRc. reflexivity. }
      setoid_rewrite FCD.ext_ana. cbn.
      eapply (sup_at (exist _ (_, _) _)).
      Unshelve.
      4: { cbn. apply Hsub. split; eauto. }
      cbn. reflexivity.
  Qed.

End BQ.

Section COMPOSITION.

  Context (se: Genv.symtbl).
  Context {L} (COMP: CategoricalComp.comp_semantics
                       (semantics2 bq_program)
                       (semantics2 rb_program) = Some L).

  Lemma rb_bq_code_correct:
    slift M_bq @ L_rb [= right_arrow (bq_rc se * rel_rc (R_rb se))%rc
                      @ right_arrow c_rc
                      @ ang_lts_spec (L se)
                      @ bot.
  Proof.
    rewrite bq_code_correct by admit.
    rewrite rb_code_correct by admit.
    rewrite !compose_assoc.
    rewrite <- (compose_assoc _ (right_arrow _) (left_arrow _)).
    rewrite epsilon. rewrite compose_unit_l.
    rewrite <- (compose_assoc _ (right_arrow _) (left_arrow _)).
    rewrite epsilon. rewrite compose_unit_l.
    rewrite <- (compose_assoc _ (ang_lts_spec _) (ang_lts_spec _)).
    rewrite comp_embed by apply COMP. reflexivity.
  Admitted.

End COMPOSITION.
