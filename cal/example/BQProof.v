From Coq Require Import Lia.
From models Require Import
     IntSpec.
From cal Require Import
     CompCertIntSpec RefConv
     IntSpecCAL CompCertCAL
     BQ BQCode.
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

Parameter val_rel: BQ.val -> val -> Prop.
Hypothesis val_is_int:
  forall c v, val_rel c v -> Cop.val_casted v tint.
Hint Resolve val_is_int.

Section MARSHALL.

  Inductive nat_rel: nat -> val -> Prop :=
  | nat_rel_intro n i:
    Z.of_nat n = Integers.Int.intval i ->
    nat_rel n (Vint i).
  Inductive void_rel: unit -> val -> Prop :=
  | void_rel_intro: void_rel tt Vundef.

  Inductive rel_with_mem {A B} (R: A -> B -> Prop) m: A -> (B * mem) -> Prop :=
  | rel_with_mem_intro a b:
    R a b -> rel_with_mem R m a (b, m).

  (** Refinement Conventions *)
  Inductive rb_rc_rel: rc_rel rb_sig (c_esig # mem) :=
  | rb_set_rel i v vf c_i c_v b m se:
    vf = Vptr b Integers.Ptrofs.zero ->
    Genv.find_symbol se set_id = Some b ->
    c_i = Vint (Integers.Int.repr (Z.of_nat i)) ->
    val_rel v c_v ->
    Ple (Genv.genv_next se) (Mem.nextblock m) ->
    rb_rc_rel _ (set i v) _ (c_event vf set_sg [ c_i ; c_v ] se # m) (rel_with_mem void_rel m)
  | rb_get_rel i vf c_i b m se:
    vf = Vptr b Integers.Ptrofs.zero ->
    Genv.find_symbol se get_id = Some b ->
    c_i = Vint (Integers.Int.repr (Z.of_nat i)) ->
    Ple (Genv.genv_next se) (Mem.nextblock m) ->
    rb_rc_rel _ (BQ.get i) _ (c_event vf get_sg [ c_i ] se # m) (rel_with_mem val_rel m)
  | rb_inc1_rel vf b m se:
    vf = Vptr b Integers.Ptrofs.zero ->
    Genv.find_symbol se inc1_id = Some b ->
    Ple (Genv.genv_next se) (Mem.nextblock m) ->
    rb_rc_rel _ inc1 _ (c_event vf inc1_sg [ ] se # m) (rel_with_mem nat_rel m)
  | rb_inc2_rel vf b m se:
    vf = Vptr b Integers.Ptrofs.zero ->
    Genv.find_symbol se inc2_id = Some b ->
    Ple (Genv.genv_next se) (Mem.nextblock m) ->
    rb_rc_rel _ inc2 _ (c_event vf inc2_sg [ ] se # m) (rel_with_mem nat_rel m).

  Inductive bq_rc_rel: rc_rel bq_sig (c_esig # mem) :=
  | bq_enq_rel v vf c_v b m se:
    vf = Vptr b Integers.Ptrofs.zero ->
    Genv.find_symbol se enq_id = Some b ->
    val_rel v c_v ->
    Ple (Genv.genv_next se) (Mem.nextblock m) ->
    bq_rc_rel _ (enq v) _ (c_event vf enq_sg [ c_v ] se # m) (rel_with_mem void_rel m)
  | bq_deq_rel vf b m se:
    vf = Vptr b Integers.Ptrofs.zero ->
    Genv.find_symbol se deq_id = Some b ->
    Ple (Genv.genv_next se) (Mem.nextblock m) ->
    bq_rc_rel _ deq _ (c_event vf deq_sg [ ] se # m) (rel_with_mem val_rel m).

  Local Obligation Tactic := idtac.
  Definition rb_rc : esig_rc rb_sig :=
    {| esig_refconv := rb_rc_rel; |}.

  Definition bq_rc : esig_rc bq_sig :=
    {| esig_refconv := bq_rc_rel; |}.

End MARSHALL.

Hint Constructors nat_rel void_rel.

Local Opaque fsup finf.
Local Opaque semantics2.

(* Import Ptrofs. *)

Section RHO.

  Context (se:Genv.symtbl).

  Inductive R_cnt (id: positive): nat -> mem -> Prop :=
  | R_cnt_intro b v n m:
    Genv.find_symbol se id = Some b ->
    Mem.load Mint32 m b 0 = Some v ->
    nat_rel n v -> (n < BQ.N)%nat ->
    Mem.range_perm m b 0 4 Cur Writable ->
    R_cnt id n m.

  Inductive R_arr : (nat -> BQ.val) -> mem -> Prop :=
  | R_arr_intro f b m:
    Genv.find_symbol se arr_id = Some b ->
    (forall i, (i < BQ.N)%nat ->
      exists v, Mem.load Mint32 m b (4 * Z.of_nat i) = Some v /\
                 val_rel (f i) v) ->
    (forall ofs, 0 <= ofs < 4 * Nz ->
            Mem.perm m b ofs Cur Writable) ->
    R_arr f m.

  Inductive R_rb: rb_state -> mem -> Prop :=
  | R_rb_intro f c1 c2 m:
    R_cnt cnt1_id c1 m -> R_cnt cnt2_id c2 m -> R_arr f m ->
    R_rb (f, c1, c2) m.

End RHO.

Program Definition rho_rb : rho_rel rb_state :=
  {|
    rho_pred := R_rb;
    rho_footprint := (cnt1_id, 4) :: (cnt2_id, 4)
                       :: (arr_id, Nz * 4) :: nil;
  |}.
Next Obligation.
  destruct H. constructor.
  - inv H. econstructor; eauto.
    + eapply Mem.load_unchanged_on; eauto.
      cbn. intros.
      apply Exists_cons_hd. split; eauto.
    + unfold Mem.range_perm in *. intros ofs Hofs.
      eapply Mem.perm_unchanged_on; eauto.
      apply Exists_cons_hd. split; eauto.
  - inv H1. econstructor; eauto.
    + eapply Mem.load_unchanged_on; eauto.
      cbn. intros.
      apply Exists_cons_tl. apply Exists_cons_hd. split; eauto.
    + unfold Mem.range_perm in *. intros ofs Hofs.
      eapply Mem.perm_unchanged_on; eauto.
      apply Exists_cons_tl. apply Exists_cons_hd. split; eauto.
  - inv H2. econstructor; eauto.
    + intros i Hi. specialize (H4 i) as (v & Hv1 & Hv2).
      apply Hi. exists v; split; eauto.
      eapply Mem.load_unchanged_on; eauto.
      intros.
      apply Exists_cons_tl. apply Exists_cons_tl.
      apply Exists_cons_hd. split; eauto.
      replace (size_chunk Mint32) with 4 in H2 by reflexivity.
      unfold Nz. lia.
    + unfold Mem.range_perm in *. intros ofs Hofs.
      eapply Mem.perm_unchanged_on; eauto.
      apply Exists_cons_tl. apply Exists_cons_tl.
      apply Exists_cons_hd. split; eauto. lia.
Qed.
Next Obligation.
  inv H. eapply Mem.perm_valid_block with (ofs := 0).
  inv H0. 2: inv H4.
  - inv H1. destruct H4. replace b with b0 by congruence. apply H7. lia.
  - inv H2. destruct H0. replace b with b0 by congruence. apply H7. lia.
  - inv H3. inv H0. destruct H6.
    replace b with b0 by congruence.
    apply H5. lia. inv H6.
Qed.
Next Obligation.
  inv H. inv H0. 2: inv H4.
  - inv H1. destruct H4. replace b with b0 by congruence. eauto with mem.
  - inv H2. destruct H0. replace b with b0 by congruence. eauto with mem.
  - inv H3. inv H0. destruct H6.
    replace b with b0 by congruence.
    assert (Mem.perm m b0 ofs Cur Writable). apply H5. lia.
    eauto with mem. inv H6.
Qed.

(*
Lemma find_get se b:
  Genv.find_symbol se get_id = Some b ->
  Genv.find_funct (Clight.globalenv se rb_program) (Vptr b zero) = Some (Internal rb_get).
Proof. intros. eapply genv_funct_symbol; eauto. Qed.
  Lemma find_set se b:
    Genv.find_symbol se set_id = Some b ->
    Genv.find_funct (Clight.globalenv se rb_program) (Vptr b zero) = Some (Internal rb_set).
  Proof. intros. eapply genv_funct_symbol; eauto. Qed.


Lemma find_inc1 se b:
  Genv.find_symbol se inc1_id = Some b ->
  Genv.find_funct (Clight.globalenv se rb_program) (Vptr b zero) = Some (Internal rb_inc1).
Proof. intros. eapply genv_funct_symbol; eauto. Qed.

Lemma find_inc2 se b:
  Genv.find_symbol se inc2_id = Some b ->
  Genv.find_funct (Clight.globalenv se rb_program) (Vptr b zero) = Some (Internal rb_inc2).
Proof. intros. eapply genv_funct_symbol; eauto. Qed.

 (* Hint Resolve find_get find_set find_inc1 find_inc2. *)
*)

Section RB.
  Open Scope Z_scope.
  Import Ptrofs.
  Hypothesis Nbound : 4 * Nz <= max_unsigned.
  Hypothesis Nbound' : 4 * Nz <= Int.max_unsigned.
  Hypothesis N_neq_0: Nz <> 0.

  Lemma cnt_inc_simp c i:
    Z.of_nat c = Int.intval i -> (c < BQ.N)%nat ->
    Z.of_nat (S c mod BQ.N) = Int.intval (Int.modu (Int.add i (Int.repr 1)) (Int.repr Nz)).
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
      exploit (Z.mod_pos_bound (Z.of_nat c + 1) (Z.of_nat BQ.N)); lia.
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

  Lemma rb_code_correct:
    L_rb [= slift (right_arrow rb_rc)
         @@ right_arrow (rho_rc rho_rb)
         @ right_arrow c_rc
         @ ang_lts_spec (semantics2 rb_program) @ bot.
  Proof.
    intros ? [? ? m [ s ]]. destruct s as [ [ f c1 ] c2 ]. cbn.
    match goal with
    | |- context [ _ @ ?f ] => set (f1 := f)
    end.
    unfold compose. cbn. unfold rc_adj_right.
    inf_intro ?. inf_intro [ ? ? [vf sg args se] [mm] ].
    inf_intro [ Rp Hr ]. intm.
    unfold f1 at 2.
    match goal with
    | |- context [ _ @ ?f ] => set (f2 := f)
    end.
    unfold compose. unfold rc_adj_left.
    sup_mor. eapply sup_at.
    sup_mor. apply (sup_at (c_event vf sg args se # (mm, (f, c1, c2)))).
    sup_mor. eapply fsup_at. rc_econstructor.
    intm. unfold f2 at 2.
    match goal with
    | |- context [ _ @ ?f ] => set (f3 := f)
    end.
    unfold compose. unfold rc_adj_right.
    inf_intro ?. inf_intro [ ? ? [vf' sg' args' se'] [mm'] ].
    inf_intro [ Rrho Hrho ].
    intm. unfold f3 at 2. unfold compose.
    unfold rc_adj_right.
    inf_intro ?. inf_intro [ [ vf'' sg'' args'' mm'' ] se'' ].
    inf_intro [ Rc Hc ]. intm.
    rc_inversion Hc. depsubst. inv H. inv H0. clear Hrel. rename Hsub into HRc.
    rc_inversion Hrho. unfold rb_state in *. depsubst. clear Hrel. rename Hsub into Hrho.
    inv H6. rename H into Hm. rename H12 into Hvdef.
    rename H13 into Hvinj. rename H14 into Hargs.
    destruct H0 as [Hperm [Hdef HRst]].
    unfold assume. inf_intro Hse. intm.
    rc_elim (inv) Hr; unfold mem in *; depsubst; clear_hyp.
    - rename H10 into Hb. rename H12 into Hv. rename H13 into Hnb.
      replace vf' with (Vptr b zero).
      2: inv Hvinj; inv H1; reflexivity.
      replace args' with ([Vint (Int.repr (Z.of_nat i2)); c_v]).
      2: {
        inv Hargs. f_equal. inv H1. reflexivity.
        inv H3. f_equal. apply val_is_int in Hv.
        inv Hv. inv H2. reflexivity. inv H2. inv H4. f_equal.
        rewrite add_zero. reflexivity.
        inv H5. reflexivity.
      }
      apply assert_l. intros Hi. apply inj_lt in Hi.
      setoid_rewrite sup_fsup. sup_mor. eapply fsup_at.
      (* initial state *)
      { repeat econstructor.
        - eapply genv_funct_symbol; [ eauto | reflexivity ].
        - eauto.
        - eauto.
        - erewrite <- Mem.mext_next; eauto. }
      rewrite lts_spec_step. sup_mor. apply join_l. apply join_l.
      (* internal steps *)
      inv HRst. inv H5. rename mm' into m.
      edestruct (Mem.valid_access_store m Mint32 b0 (4 * Z.of_nat i2)) as (m' & Hm').
      {
        constructor.
        - intros ofs Hofs. apply H1. unfold Nz. split.
          lia. cbn [size_chunk] in Hofs. lia.
        - apply Z.divide_factor_l.
      }
      sup_mor. eapply fsup_at.
      {
        crush_star.
        match goal with
        | [ H: Mem.store _ ?m ?b ?ofs ?v = Some ?m' |-
            Mem.store _ ?m ?b ?ofs' ?v' = Some _ ] =>
            replace ofs' with ofs; [ apply H | ]
        end.
        rewrite add_zero_l.
        unfold of_intu, of_int, mul.
        rewrite Int.unsigned_repr.
        repeat rewrite unsigned_repr.
        all: unfold Nz in *; try lia.
      }
      (* final step *)
      rewrite lts_spec_step. rewrite !Sup.mor_join. apply join_r.
      sup_mor. eapply fsup_at.
      { cbn. econstructor. }
      (* re-establish the relation *)
      fcd_simpl. sup_mor. eapply (fsup_at (Vundef, m')); cbn.
      { cbn. apply HRc. reflexivity. }
      fcd_simpl. sup_mor. cbn. eapply (fsup_at (Vundef, (mm, (update f i2 v, c1, c2)))).
      {
        apply Hrho. constructor.
        (* temporal conditions *)
        - apply Mem.unchanged_on_refl.
        - eapply Mem.store_unchanged_on. exact Hm'.
          intros ofs Hofs [A B]. apply B.
          cbn. apply Exists_cons_tl.
          apply Exists_cons_tl. apply Exists_cons_hd.
          split. eassumption.
          replace (size_chunk Mint32) with 4 in * by reflexivity.
          unfold Nz. lia.
        (* match return value *)
        - constructor.
        (* match return state *)
        - constructor. 2: repeat apply conj.
          (* memory extension *)
          + eapply Mem.store_outside_extends; eauto.
            intros. apply (Hperm b0 ofs').
            cbn. apply Exists_cons_tl.
            apply Exists_cons_tl. apply Exists_cons_hd.
            split. eassumption.
            replace (size_chunk Mint32) with 4 in * by reflexivity.
            unfold Nz. lia.
            eauto with mem.
          (* permission *)
          + apply Hperm.
          (* defined *)
          + admit.
          (* rho relation *)
          + constructor.
            * destruct H2. econstructor; eauto.
              erewrite Mem.load_store_other; eauto.
              left. intros Hbb. subst.
              exploit Genv.find_symbol_injective. apply H2. apply H.
              intros. easy.
              intros ofs Hofs. eapply Mem.perm_store_1; eauto.
            * destruct H4. econstructor; eauto.
              erewrite Mem.load_store_other; eauto.
              left. intros Hbb. subst.
              exploit Genv.find_symbol_injective. apply H3. apply H.
              intros. easy.
              intros ofs Hofs. eapply Mem.perm_store_1; eauto.
            * econstructor; eauto. intros ix.
              -- unfold update in *. destruct Nat.eq_dec.
                 ++ subst. exists c_v. split; auto.
                    erewrite Mem.load_store_same; eauto.
                    f_equal.
                    eapply SimplLocalsproof.val_casted_load_result.
                    eapply val_is_int; eauto. reflexivity.
                 ++ intros Hix. edestruct (H0 _ Hix) as (vx & Hvx & Hrv).
                    exists vx; split; auto.
                    erewrite Mem.load_store_other; eauto. right.
                    apply not_eq in n. destruct n.
                 ** right. apply inj_lt in H3. cbn [size_chunk]. lia.
                 ** left. apply inj_lt in H3. cbn [size_chunk]. lia.
              -- intros ofs Hofs. eapply Mem.perm_store_1; eauto.
      }
      fcd_simpl. inf_intro [ n Hx ]. inv Hx.
      fcd_simpl. sup_mor. apply (fsup_at tt).
      apply Hsub. constructor. constructor.
      fcd_simpl. reflexivity.
    (* get *)
    - rename H10 into Hb. rename H12 into Hnb.
      replace vf' with (Vptr b zero).
      2: inv Hvinj; inv H1; reflexivity.
      replace args' with ([Vint (Int.repr (Z.of_nat i2))]).
      2: { inv Hargs. inv H3. inv H1. reflexivity. }
      apply assert_l. intros Hi.
      setoid_rewrite sup_fsup. sup_mor.
      (* initial_state *)
      eapply fsup_at.
      { repeat econstructor.
        - eapply genv_funct_symbol; [ eauto | reflexivity ].
        - eauto.
        - erewrite <- Mem.mext_next; eauto. }
      rewrite lts_spec_step. sup_mor. apply join_l. apply join_l.
      (* internal steps *)
      inv HRst. inv H5. rename mm into m.
      edestruct (H0 _ Hi) as (vx & Hvx & Hvr).
      sup_mor. eapply fsup_at.
      {
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
      rewrite lts_spec_step. sup_mor. apply join_r.
      sup_mor. eapply fsup_at. { cbn. econstructor. }
      (* re-establish the relation *)
      fcd_simpl. sup_mor.
      eapply (fsup_at (_, _)). { apply HRc. subst R0. reflexivity. }
      fcd_simpl. sup_mor.
      eapply (fsup_at (vx, (m, (f, c1, c2)))).
      {
        apply Hrho. constructor.
        (* temporal conditions *)
        - apply Mem.unchanged_on_refl.
        - apply Mem.unchanged_on_refl.
        (* match return value *)
        - reflexivity.
        - constructor; eauto. repeat apply conj; eauto.
          constructor; eauto. econstructor; eauto.
      }
      fcd_simpl. inf_intro [x Hx]. inv Hx.
      fcd_simpl. sup_mor. eapply (fsup_at (f i2)).
      { apply Hsub. constructor; eauto. }
      fcd_simpl. reflexivity.
    (* inc1 *)
    - rename H10 into Hb. rename H11 into Hnb.
      replace vf' with (Vptr b zero).
      2: inv Hvinj; inv H1; reflexivity.
      inv Hargs.
      setoid_rewrite sup_fsup.
      (* initial_state *)
      sup_mor. eapply fsup_at.
      { repeat econstructor.
        - eapply genv_funct_symbol; [ eauto | reflexivity ].
        - eauto.
        - erewrite <- Mem.mext_next; eauto. }
      rewrite lts_spec_step. sup_mor. apply join_l. apply join_l.
      (* internal steps *)
      inv HRst. inv H2. inv H1. rename mm' into m.
      edestruct (Mem.valid_access_store m Mint32 b0 0) as (m' & Hm').
      {
        constructor.
        - intros ofs Hofs. apply H6. cbn [size_chunk] in Hofs. lia.
        - apply Z.divide_0_r.
      }
      edestruct (Mem.valid_access_store m' Mint32 b0 0) as (m'' & Hm'').
      {
        constructor.
        - intros ofs Hofs. eapply Mem.perm_store_1; eauto.
        - apply Z.divide_0_r.
      }
      sup_mor. eapply fsup_at.
      {
        do 7 (lts_step; [ crush_step; crush_expr | ]). now constructor.
        do 2 (lts_step; [ crush_step; crush_expr | ]). erewrite Mem.load_store_same; eauto.
        apply cop_sem_mod.
        intros contra. assert (Int.unsigned (Int.repr Nz) = 0).
        rewrite contra. rewrite Int.unsigned_zero. reflexivity.
        rewrite Int.unsigned_repr in H1. easy. unfold Nz in *. lia.
        now constructor.
        crush_star. now constructor.
      }
      rewrite lts_spec_step. sup_mor. apply join_r.
      sup_mor. eapply fsup_at. { cbn. econstructor. }
      (* re-establish the relation *)
      fcd_simpl. sup_mor.  eapply (fsup_at (Vint i2, m'')).
      { apply HRc. reflexivity. }
      fcd_simpl. sup_mor.
      eapply (fsup_at (Vint i2, (mm, (f, (S c1 mod BQ.N)%nat, c2)))).
      {
        apply Hrho. constructor.
        (* temporal conditions *)
        - apply Mem.unchanged_on_refl.
        - admit.
        (* match return value *)
        - constructor.
        (* match state *)
        - constructor. 2: repeat apply conj; eauto.
          (* memory extension *)
          + assert (Hp: forall ofs', Mem.perm mm b0 ofs' Cur Readable ->
                              0 <= ofs' < 0 + size_chunk Mint32 -> False).
            { intros. apply (Hperm b0 ofs').
              apply Exists_exists.
              eexists (cnt1_id, _). split; auto.
              cbn. now left. cbn. eauto. eauto with mem. }
            eapply Mem.store_outside_extends; [ | eauto | eauto ].
            eapply Mem.store_outside_extends; eauto.
          (* defined *)
          + admit.
          + constructor.
            * econstructor; eauto.
              -- erewrite Mem.load_store_same; eauto.
              -- cbn. constructor.
                 apply cnt_inc_simp; assumption.
              -- apply Nat.mod_upper_bound. lia.
              -- intros ofs Hofs. eapply Mem.perm_store_1; eauto.
                 eapply Mem.perm_store_1; eauto.
            * inv H4. econstructor; eauto.
              -- assert (b1 <> b0).
                 { intros <-. exploit Genv.find_symbol_injective.
                   apply H. apply H1. easy. }
                 erewrite Mem.load_store_other. 2: apply Hm''. 2: left; auto.
                 erewrite Mem.load_store_other; eauto.
              -- intros ofs Hofs. eapply Mem.perm_store_1; eauto.
                 eapply Mem.perm_store_1; eauto.
            * inv H5. assert (b0 <> b1).
              { intros <-. exploit Genv.find_symbol_injective.
                apply H. apply H1. easy. }
              econstructor; eauto.
              -- intros ix Hix. edestruct (H7 _ Hix) as (vx & Hvx & Hrx).
                 exists vx. split; eauto.
                 erewrite Mem.load_store_other. 2: apply Hm''. 2: left; auto.
                 erewrite Mem.load_store_other; eauto.
              -- intros ofs Hofs. eapply Mem.perm_store_1; eauto.
                 eapply Mem.perm_store_1; eauto.
      }
      fcd_simpl. inf_intro [x Hx]. inv Hx.
      fcd_simpl. sup_mor. eapply (fsup_at c1).
      { apply Hsub. constructor. constructor. eauto. }
      fcd_simpl. reflexivity.
    (* inc2 *)
    - rename H10 into Hb. rename H11 into Hnb.
      replace vf' with (Vptr b zero).
      2: inv Hvinj; inv H1; reflexivity.
      inv Hargs.
      setoid_rewrite sup_fsup.
      (* initial_state *)
      sup_mor. eapply fsup_at.
      { repeat econstructor.
        - eapply genv_funct_symbol; [ eauto | reflexivity ].
        - eauto.
        - erewrite <- Mem.mext_next; eauto. }
      rewrite lts_spec_step. sup_mor. apply join_l. apply join_l.
      (* internal steps *)
      inv HRst. inv H4. inv H1. rename mm' into m.
      edestruct (Mem.valid_access_store m Mint32 b0 0) as (m' & Hm').
      {
        constructor.
        - intros ofs Hofs. apply H6. cbn [size_chunk] in Hofs. lia.
        - apply Z.divide_0_r.
      }
      edestruct (Mem.valid_access_store m' Mint32 b0 0) as (m'' & Hm'').
      {
        constructor.
        - intros ofs Hofs. eapply Mem.perm_store_1; eauto.
        - apply Z.divide_0_r.
      }
      sup_mor. eapply fsup_at.
      {
        do 7 (lts_step; [ crush_step; crush_expr | ]). now constructor.
        do 2 (lts_step; [ crush_step; crush_expr | ]). erewrite Mem.load_store_same; eauto.
        apply cop_sem_mod.
        intros contra. assert (Int.unsigned (Int.repr Nz) = 0).
        rewrite contra. rewrite Int.unsigned_zero. reflexivity.
        rewrite Int.unsigned_repr in H1. easy. unfold Nz in *. lia.
        now constructor.
        crush_star. now constructor.
      }
      rewrite lts_spec_step. sup_mor. apply join_r.
      sup_mor. eapply fsup_at. { cbn. econstructor. }
      (* re-establish the relation *)
      fcd_simpl. sup_mor.  eapply (fsup_at (Vint i2, m'')).
      { apply HRc. reflexivity. }
      fcd_simpl. sup_mor.
      eapply (fsup_at (Vint i2, (mm, (f, c1, (S c2 mod BQ.N)%nat)))).
      {
        apply Hrho. constructor.
        (* temporal conditions *)
        - apply Mem.unchanged_on_refl.
        - admit.
        (* match return value *)
        - constructor.
        (* match state *)
        - constructor. 2: repeat apply conj; eauto.
          (* memory extension *)
          + assert (Hp: forall ofs', Mem.perm mm b0 ofs' Cur Readable ->
                              0 <= ofs' < 0 + size_chunk Mint32 -> False).
            { intros. apply (Hperm b0 ofs').
              apply Exists_exists.
              eexists (cnt2_id, _). split; auto.
              cbn. now right; left. cbn. eauto. eauto with mem. }
            eapply Mem.store_outside_extends; [ | eauto | eauto ].
            eapply Mem.store_outside_extends; eauto.
          (* defined *)
          + admit.
          + constructor.
            * inv H2. econstructor; eauto.
              -- assert (b1 <> b0).
                 { intros <-. exploit Genv.find_symbol_injective.
                   apply H. apply H1. easy. }
                 erewrite Mem.load_store_other. 2: apply Hm''. 2: left; auto.
                 erewrite Mem.load_store_other; eauto.
              -- intros ofs Hofs. eapply Mem.perm_store_1; eauto.
                 eapply Mem.perm_store_1; eauto.
            * econstructor; eauto.
              -- erewrite Mem.load_store_same; eauto.
              -- cbn. constructor.
                 apply cnt_inc_simp; assumption.
              -- apply Nat.mod_upper_bound. lia.
              -- intros ofs Hofs. eapply Mem.perm_store_1; eauto.
                 eapply Mem.perm_store_1; eauto.
            * inv H5. assert (b0 <> b1).
              { intros <-. exploit Genv.find_symbol_injective.
                apply H. apply H1. easy. }
              econstructor; eauto.
              -- intros ix Hix. edestruct (H7 _ Hix) as (vx & Hvx & Hrx).
                 exists vx. split; eauto.
                 erewrite Mem.load_store_other. 2: apply Hm''. 2: left; auto.
                 erewrite Mem.load_store_other; eauto.
              -- intros ofs Hofs. eapply Mem.perm_store_1; eauto.
                 eapply Mem.perm_store_1; eauto.
      }
      fcd_simpl. inf_intro [x Hx]. inv Hx.
      fcd_simpl. sup_mor. eapply (fsup_at c2).
      { apply Hsub. constructor. constructor. eauto. }
      fcd_simpl. reflexivity.
  Admitted.

End RB.

Require Import Effects.

Inductive empty_rc_rel {E: esig}: rc_rel 0 E := .
Program Definition empty_rc : esig_rc 0 :=
  {|
    esig_refconv := empty_rc_rel;
  |}.

Program Definition empty_rho : rho_rel unit :=
  {|
    rho_pred se tt m := True;
    rho_footprint := nil;
  |}.
Next Obligation. inv H0. Qed.
Next Obligation. inv H0. Qed.

Unset Asymmetric Patterns.

Definition dummy_state {E} : E ~> E # unit :=
  fun _ '(etens_intro m t) =>
    match t with
    | est_intro tt => ISpec.int m >>= (fun n => ret (n ,tt))
    end.

(*
Lemma find_enq b:
  Genv.find_symbol se enq_id = Some b ->
  Genv.find_funct (Clight.globalenv se bq_program) (Vptr b zero) = Some (Internal bq_enq).
Proof. intros. eapply genv_funct_symbol; eauto. Qed.

Lemma find_deq b:
  Genv.find_symbol se deq_id = Some b ->
  Genv.find_funct (Clight.globalenv se bq_program) (Vptr b zero) = Some (Internal bq_deq).
Proof. intros. eapply genv_funct_symbol; eauto. Qed.

Hint Resolve find_enq find_deq.
*)

Import Ptrofs.
Transparent semantics2.
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

Section BQ.

  Local Transparent LatticeProduct.poset_prod.

  Lemma bq_code_correct:
    dummy_state @ M_bq [=
      slift (right_arrow bq_rc) @ h
      @ (right_arrow (rho_rc empty_rho))
      @ right_arrow c_rc
      @ ang_lts_spec (semantics2 bq_program)
      @ left_arrow c_rc
      @ left_arrow rb_rc.
  Proof.
    intros ? m. unfold compose at 1. destruct m as [ ? ? m [ [ ] ] ].
    cbn. intm.
    match goal with
    | |- context [ _ @ ?f ] => set (f1 := f)
    end.
    unfold compose. cbn. unfold rc_adj_right.
    inf_intro ?. inf_intro [ ? ? [vf sg args se] [ mm ] ].
    inf_intro [ Rr Hr ].
    intm. unfold f1 at 2.
    match goal with
    | |- context [ _ @ ?f ] => set (f2 := f)
    end.
    unfold compose. unfold rc_adj_left.
    sup_mor. eapply sup_at.
    sup_mor. apply (sup_at (c_event vf sg args se # (mm, tt))).
    sup_mor. eapply fsup_at. rc_econstructor.
    intm. unfold f2 at 2.
    match goal with
    | |- context [ _ @ ?f ] => set (f3 := f)
    end.
    unfold compose. unfold rc_adj_right.
    inf_intro ?. inf_intro [ ? ? [vf' sg' args' se'] [ mm' ] ].
    inf_intro [ Rrho Hrho ].
    intm. unfold f3 at 2.
    match goal with
    | |- context [ _ @ ?f ] => set (f4 := f)
    end.
    unfold compose. unfold rc_adj_right.
    inf_intro ?. inf_intro [ q ]. inf_intro [ Rc Hc ].
    intm. unfold f4 at 2. cbn.
    unfold compose. cbn.
    unfold assume. inf_intro Hse. intm.
    rc_elim (inv) Hc. depsubst. inv H. inv H0. rename Hsub into HRc.
    rc_elim (inv) Hrho. depsubst. rename Hsub into HRho.
    rename H12 into Hvdef. rename H13 into Hvinj. rename H14 into Hargs.
    inv H6. rename H into Hm. destruct H0 as [Hperm [Hdef Hx]]. inv Hx.
    rename se' into se.
    rc_elim (inv) Hr; unfold mem in *; depsubst; clear_hyp.
    (* enq *)
    - rename H10 into Hb. rename H11 into Hv.
      replace vf' with (Vptr b zero).
      2: inv Hvinj; inv H1; reflexivity.
      replace args' with [c_v].
      2: admit.
      edestruct inc2_block as (inc2b & Hb1 & Hb2); eauto.
      edestruct set_block as (setb & Hb3 & Hb4); eauto.
      setoid_rewrite sup_fsup.
      sup_mor. eapply fsup_at.
      (* initial state *)
      { repeat econstructor.
        - eapply genv_funct_symbol; [ eauto | reflexivity ].
        - eauto.
        - eauto.
        - erewrite <- Mem.mext_next; eauto. }
      rewrite lts_spec_step.
      rewrite !Sup.mor_join. apply join_l. apply join_l.
      sup_mor. eapply fsup_at.
      { cbn. crush_star. apply star_refl. }
      (* external call to [inc2] *)
      rewrite lts_spec_step. sup_mor. apply join_l. apply join_r.
      sup_mor. eapply fsup_at.
      { cbn. econstructor. eauto. }
      unfold query_int. intm.
      unfold rc_adj_left.
      sup_mor. eapply sup_at. sup_mor. eapply sup_at. sup_mor. eapply fsup_at.
      { cbn. rc_econstructor; reflexivity. } intm.
      sup_mor. eapply sup_at. sup_mor. eapply sup_at. sup_mor. eapply fsup_at.
      { rc_eapply rb_inc2_rel; eauto.
        erewrite <- Mem.mext_next; eauto. }
      unfold ISpec.int at 2 6.
      sup_intro ns_opt. apply (sup_at ns_opt).
      destruct ns_opt as [ n | ].
      2: { now fcd_simpl. }
      fcd_simpl. sup_mor. apply join_lub.
      { apply join_l. fcd_simpl. reflexivity. }
      apply join_r. inf_intro [ [vr m'] Hm'].
      inv Hm'. inv H1. fcd_simpl. apply join_r. rstep.
      inf_intro [ r_c Hrc ]. subst.
      fcd_simpl. sup_mor. eapply fsup_at.
      { cbn. constructor. }
      (* internal steps before calling [set] *)
      rewrite lts_spec_step.
      sup_mor. apply join_l. apply join_l.
      sup_mor. eapply fsup_at.
      { cbn. crush_star. now constructor. apply star_refl. }
      (* external call to [set] *)
      rewrite lts_spec_step.
      sup_mor. apply join_l. apply join_r.
      sup_mor. eapply fsup_at.
      { cbn. econstructor. eauto. }
      unfold query_int. intm.
      sup_mor. eapply sup_at. sup_mor. eapply sup_at. sup_mor. eapply fsup_at.
      { cbn. rc_econstructor; reflexivity. }
      intm.
      sup_mor. eapply sup_at. sup_mor. eapply sup_at. sup_mor. eapply fsup_at.
      {
        cbn. repeat econstructor; try reflexivity; eauto.
        rewrite H. rewrite Int.repr_unsigned. reflexivity.
        erewrite <- Mem.mext_next; eauto.
      }
      unfold ISpec.int at 1 5.
      sup_intro [ [] | ].
      2: { apply (sup_at None). fcd_simpl. reflexivity. }
      fcd_simpl. apply join_lub. apply (sup_at None). fcd_simpl. reflexivity.
      apply (sup_at (Some tt)). fcd_simpl.
      sup_mor. apply join_r.
      inf_intro [ [rv m''] Hrm ]. inv Hrm. inv H2.
      fcd_simpl. apply join_r.
      replace (FCD.emb (pcons (set n v) tt (pret (tt, tt))))
        with (FCD.ext (fun s => FCD.emb (pcons (set n v) tt s)) (ret (tt, tt))).
      2: { setoid_rewrite FCD.ext_ana. reflexivity. }
      rstep.
      inf_intro [ rc Hrc ]. inv Hrc.
      fcd_simpl.
      sup_mor. eapply fsup_at.
      { cbn. constructor. }
      rewrite lts_spec_step. sup_mor. apply join_l. apply join_l.
      sup_mor. eapply fsup_at.
      { cbn. crush_star. }
      (* final state *)
      rewrite lts_spec_step. sup_mor. apply join_r.
      sup_mor. eapply fsup_at.
      { cbn. constructor. }
      fcd_simpl. sup_mor. eapply (fsup_at (_, _)).
      { cbn. apply HRc. subst R0. reflexivity. }
      fcd_simpl. sup_mor. eapply (fsup_at (_, (_, tt))).
      { apply HRho. constructor.
        1-2: eapply Mem.unchanged_on_refl. reflexivity.
        constructor; eauto.
        repeat apply conj; eauto.
        constructor. }
      fcd_simpl. inf_intro [ x Hx ]. inv Hx.
      fcd_simpl. sup_mor. eapply (fsup_at tt).
      apply Hsub. constructor. constructor.
      fcd_simpl. unfold ret. reflexivity.
    (* deq *)
    - rename H10 into Hb.
      replace vf' with (Vptr b zero).
      2: inv Hvinj; inv H1; reflexivity.
      inv Hargs.
      edestruct inc1_block as (inc1b & Hb1 & Hb2); eauto.
      edestruct get_block as (getb & Hb3 & Hb4); eauto.
      (* initial_state *)
      setoid_rewrite sup_fsup.
      sup_mor. eapply fsup_at.
      { repeat econstructor.
        - eapply genv_funct_symbol; [ eauto | reflexivity ].
        - eauto.
        - erewrite <- Mem.mext_next; eauto. }
      rewrite lts_spec_step.
      sup_mor. apply join_l. apply join_l.
      sup_mor. eapply fsup_at.
      { cbn. crush_star. apply star_refl. }
      (* external call to [inc1] *)
      rewrite lts_spec_step.
      sup_mor. apply join_l. apply join_r.
      sup_mor. eapply fsup_at.
      { cbn. econstructor. eauto. }
      unfold query_int. cbn. intm.
      unfold rc_adj_left.
      sup_mor. eapply sup_at. sup_mor. eapply sup_at. sup_mor. eapply fsup_at.
      { cbn. rc_econstructor; reflexivity. }
      intm. sup_mor. eapply sup_at. sup_mor. eapply sup_at. sup_mor. eapply fsup_at.
      { rc_eapply rb_inc1_rel; eauto.
        erewrite <- Mem.mext_next; eauto. }
      unfold ISpec.int at 2 6.
      sup_intro ns_opt. apply (sup_at ns_opt).
      destruct ns_opt as [ n | ].
      2: { fcd_simpl. reflexivity. }
      fcd_simpl. sup_mor. apply join_lub.
      { apply join_l. fcd_simpl. reflexivity. }
      apply join_r. inf_intro [ [vr m'] Hm'].
      inv Hm'. inv H1.
      fcd_simpl. apply join_r. rstep.
      inf_intro [ r_c Hrc ]. subst.
      fcd_simpl. sup_mor. eapply fsup_at.
      { econstructor. }
      (* internal steps before calling [get] *)
      rewrite lts_spec_step.
      sup_mor. apply join_l. apply join_l.
      sup_mor. eapply fsup_at.
      { cbn. crush_star. now constructor. apply star_refl. }
      (* external call to [get] *)
      rewrite lts_spec_step.
      sup_mor. apply join_l. apply join_r.
      sup_mor. eapply fsup_at.
      { cbn. econstructor. eauto. }
      unfold query_int. intm.
      sup_mor. eapply sup_at. sup_mor. eapply sup_at. sup_mor. eapply fsup_at.
      { cbn. rc_econstructor; reflexivity. } intm.
      sup_mor. eapply sup_at. sup_mor. eapply sup_at. sup_mor. eapply fsup_at.
      {
        cbn. repeat econstructor; try reflexivity; eauto.
        rewrite H. rewrite Int.repr_unsigned. reflexivity.
        erewrite <- Mem.mext_next; eauto.
      }
      unfold ISpec.int at 1 5.
      sup_intro [ v | ].
      2: { apply (sup_at None). now fcd_simpl. }
      fcd_simpl. apply join_lub. apply (sup_at None). now fcd_simpl.
      apply (sup_at (Some v)). fcd_simpl. sup_mor. apply join_r.
      inf_intro [ [rv m''] Hrm ]. inv Hrm.
      fcd_simpl. apply join_r.
      inf_intro [ rc Hrc ]. subst. fcd_simpl.
      replace (FCD.emb (pcons (BQ.get n) v (pret (v, tt))))
        with (FCD.ext (fun s => FCD.emb (pcons (BQ.get n) v s)) (ret (v, tt))).
      2: { setoid_rewrite FCD.ext_ana. reflexivity. }
      rstep. sup_mor. eapply fsup_at.
      { constructor. }
      rewrite lts_spec_step. sup_mor. apply join_l. apply join_l.
      sup_mor. eapply fsup_at.
      { cbn. crush_star. }
      (* final state *)
      rewrite lts_spec_step. sup_mor. apply join_r.
      sup_mor. eapply fsup_at.
      { cbn. constructor. }
      fcd_simpl. sup_mor. eapply (fsup_at (_, _)).
      { cbn. apply HRc.  subst R0. reflexivity. }
      fcd_simpl. sup_mor. eapply (fsup_at (_, (_, tt))).
      { apply HRho. constructor.
        1-2: eapply Mem.unchanged_on_refl. reflexivity.
        constructor; eauto.
        repeat apply conj; eauto.
        constructor. }
      fcd_simpl. inf_intro [x Hx]. inv Hx.
      fcd_simpl. sup_mor. eapply (fsup_at v).
      { apply Hsub. constructor. eauto. }
      fcd_simpl. reflexivity.
  Admitted.

End BQ.

Require Composition.
Transparent CModule.semantics.

Lemma singleton_module_ref p:
  ang_lts_spec (semantics2 p) [= ang_lts_spec (CModule.semantics (CModule.cmod_of_program p)).
Proof.
  pose proof @Composition.hcomp_singleton_fsim.
  apply ang_fsim_embed_cc_id.
  unfold CModule.semantics. cbn. etransitivity.
  2: { apply H. typeclasses eauto. }
  reflexivity.
Qed.

Lemma compose_bot {E F G} (f f': E ~> F) (g: E ~> G):
  f [= f' -> f @ bot @ g [= f'.
Proof.
  intros Hf. etransitivity. 2: apply Hf.
  intros ar m. unfold compose.
  edestruct (FCD.join_meet_dense (f ar m)) as (I & J & c & Hc).
  rewrite Hc.
  sup_intro i. apply (sup_at i).
  inf_intro j. apply (inf_at j).
  fcd_simpl. induction (c i j).
  - reflexivity.
  - cbn. Local Transparent bot.
    unfold bot. sup_mor. sup_intro [].
  - cbn. sup_intro [].
Qed.

Opaque CModule.semantics LatticeProduct.poset_prod bot.

Program Definition rb_correct: strategy_clight L_rb :=
  {|
    rho := rho_rb;
    r1 := empty_rc;
    r2 := rb_rc;
    M := CModule.cmod_of_program rb_program;
  |}.
Local Obligation Tactic := idtac.
Next Obligation.
  rewrite rb_code_correct. cbn -[left_arrow right_arrow].
  unfold h, sig_assoc_right, sig_assoc_left.
  rewrite !compose_assoc.
  rewrite <- (compose_assoc _ (slift (right_arrow _)) (slift (left_arrow _))).
  rewrite <- slift_compose. rewrite epsilon.
  rewrite slift_identity. rewrite compose_unit_l.
  rewrite <- (compose_assoc _ (left_arrow _) (right_arrow _)).
  rewrite assoc_inverse'. rewrite compose_unit_l.
  rewrite <- (compose_assoc _ (right_arrow _) (left_arrow _)).
  rewrite epsilon. rewrite compose_unit_l.
  rewrite <- (compose_assoc _ (right_arrow _) (left_arrow _)).
  rewrite epsilon. rewrite compose_unit_l.
  apply compose_bot. apply singleton_module_ref.
Admitted.

Program Definition bq_correct : strategy_clight (dummy_state @ M_bq) :=
  {|
    rho := empty_rho;
    r1 := rb_rc;
    r2 := bq_rc;
    M := CModule.cmod_of_program bq_program;
  |}.
Next Obligation.
  rewrite bq_code_correct. cbn -[left_arrow right_arrow].
  unfold h, sig_assoc_right, sig_assoc_left.
  rewrite !compose_assoc.
  rewrite <- (compose_assoc _ (right_arrow rb_rc_rel) (left_arrow _)).
  rewrite epsilon. rewrite compose_unit_l.
  rewrite epsilon. rewrite compose_unit_r.
  rewrite <- (compose_assoc _ (slift (right_arrow bq_rc_rel)) _).
  rewrite <- slift_compose. rewrite epsilon.
  rewrite slift_identity. rewrite compose_unit_l.
  rewrite <- (compose_assoc _ (left_arrow sig_assoc) _).
  rewrite assoc_inverse'. rewrite compose_unit_l.
  rewrite <- (compose_assoc _ (right_arrow _) (left_arrow _)).
  rewrite epsilon. rewrite compose_unit_l.
  rewrite <- (compose_assoc _ (right_arrow _) (left_arrow _)).
  rewrite epsilon. rewrite compose_unit_l.
  apply singleton_module_ref.
Qed.
