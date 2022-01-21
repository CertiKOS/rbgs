From Coq Require Import
     Relations
     RelationClasses
     List Lia
     FunctionalExtensionality.
From models Require Import
     IntSpec.
From examples Require Import
     CAL CompCertIntSpec RefConv
     BoundedQueueCode.
From lattices Require Import
     Upset Downset FCD.
From structures Require Import
     Effects Lattice.
From compcert Require Import
     Integers Maps Coqlib
     Memory AST Values
     Clight Ctypes
     LanguageInterface
     Events Globalenvs
     Smallstep.
From compcertox Require Import
     Lifting CModule.
Import ListNotations ISpec.

Unset Asymmetric Patterns.

(** The language interface "C simple" which does not include the memory *)
Inductive c_esig : esig :=
| c_event : val -> signature -> list val -> c_esig val.

Inductive c_rc_rel: rc_rel (c_esig # mem) li_c :=
| c_rc_rel_intro vf sg args e_c e_s m R:
  e_c = c_event vf sg args -> e_s = state_event m ->
  subrel (fun '(r, m) c_r => c_r = cr r m) R ->
  c_rc_rel _ (esig_tens_intro e_c e_s) _ (li_sig (cq vf sg args m)) R.

Program Definition c_rc : (c_esig # mem) <=> li_c :=
  {|
    refconv_rel := c_rc_rel;
  |}.
Next Obligation.
  intros x y Hxy H. destruct H.
  econstructor; eauto. etransitivity; eauto.
Qed.

(** Some auxiliary definitions *)
Definition overlay_rc {E: esig} {S1 S2: Type} (rc: E <=> c_esig) (rel: S2 -> mem * S1 -> Prop):
  E # S2 <=> c_esig # (mem * S1)%type := rc * rel_rc rel.

Inductive lts_state_rc_rel {S: Type}: rc_rel (c_esig # (mem * S)) (li_c @ S)%li :=
| lts_state_rc_rel_intro vf sg args m s R (qs: query (li_c @ S)) qe:
  qs = (cq vf sg args m, s) ->
  qe = st (c_event vf sg args) (m, s) ->
  subrel (fun '(r, (m, s)) '(r', s') => r' = cr r m /\ s = s') R ->
  lts_state_rc_rel _ qe _ (li_sig qs) R.

Program Definition lts_state_rc {S: Type} : c_esig # (mem * S) <=> (li_c @ S)%li :=
  {|
    refconv_rel := lts_state_rc_rel;
  |}.
Next Obligation.
  intros x y Hxy H. destruct H.
  econstructor; eauto. etransitivity; eauto.
Qed.

Inductive st_mem_rc_rel {S: Type}: rc_rel (s_esig S) (s_esig (mem * S)) :=
| st_mem_rc_rel_intro s m R:
  subrel (fun s' '(m', t') => s' = t' /\ m = m') R ->
  st_mem_rc_rel _ (state_event s) _ (state_event (m, s)) R.

Program Definition st_mem_rc {S: Type}: s_esig S <=> s_esig (mem * S) :=
  {|
    refconv_rel := st_mem_rc_rel;
  |}.
Next Obligation.
  intros x y Hxy H. destruct H.
  constructor. etransitivity; eauto.
Qed.

Definition underlay_rc {E: esig} {S: Type} (rc: E <=> c_esig):
  E # S <=> c_esig # (mem * S) := rc * st_mem_rc.

Close Scope Z_scope.
(** ** Construction of a certified abstraction layer *)
Record certi_layer {E1 E2: esig} {S1 S2: Type} {se: Genv.symtbl} :=
  {
    L1: 0 ~> E1 * s_esig S1;    (** underlay *)
    L1_rc: E1 <=> c_esig;
    L2: 0 ~> E2 * s_esig S2;    (** overlay *)
    L2_rc: E2 <=> c_esig;
    module: list Clight.program;
    sk: AST.program unit unit;
    abs_rel: S2 -> mem * S1 -> Prop;

    layer_rel:
    L2 [= right_arrow (overlay_rc L2_rc abs_rel)
       @ right_arrow lts_state_rc
       @ ang_lts_spec (((semantics module sk) @ S1)%lts se)
       @ left_arrow lts_state_rc
       @ left_arrow (underlay_rc L1_rc)
       @ L1;
  }.

(** ** Layer Composition *)
Section COMP.

  Context {E1 E2 E3: esig} {S1 S2 S3: Type} (se: Genv.symtbl).
  Context (C1: @certi_layer E1 E2 S1 S2 se)
          (C2: @certi_layer E2 E3 S2 S3 se).
  Context (sk_comp: AST.program unit unit)
          (Hsk: Linking.link (sk C1) (sk C2) = Some sk_comp).
  Program Definition comp_certi_layer: @certi_layer E1 E3 S1 S3 se :=
    {|
      L1 := L1 C1;
      L1_rc := L1_rc C1;
      L2 := L2 C2;
      L2_rc := L2_rc C2;
      module := module C1 ++ module C2;
      sk := sk_comp;
      (* This is probably wrong *)
      abs_rel :=
      fun s3 '(m, s1) =>
        exists s2, (abs_rel C1) s2 (m, s1)
              /\ (abs_rel C2) s3 (m, s2);
    |}.
  Next Obligation.
  Admitted.

End COMP.

(** * Example: ring buffer and bounded queue *)

(** With CompCertO semantics embedded in the interaction specification, we
    substitute Clight programs for the layer implementation. *)

(** ** Language interfaces vs. effect signatures *)

(** We define "marshalling" transformations between coarse-grained language
    interfaces and fine-grained effect signatures as adjunctions, similar to the
    embedding of calling conventions. We lift the language interfaces with
    abstract states to smooth the convertion. To further connect the abstract
    states with values in memory blocks we use the calling conventions induced
    by the abstraction relations from CompCertOX. *)


Parameter cal_val_rel: CAL.val -> val -> Prop.
Hypothesis val_is_int:
  forall c v, cal_val_rel c v -> Cop.val_casted v tint.

Section MARSHALL.

  Inductive cal_nat_rel: nat -> val -> Prop :=
  | cal_nat_rel_intro n i:
    Z.of_nat n = Integers.Int.intval i ->
    cal_nat_rel n (Vint i).
  Inductive cal_void_rel: unit -> val -> Prop :=
  | cal_void_rel_intro: cal_void_rel tt Vundef.

  Context (se: Genv.symtbl).

  (** Refinement Conventions *)
  Inductive rb_rc_rel: rc_rel rb_sig c_esig :=
  | rb_set_rel i v vf sg c_i c_v b R:
    vf = Vptr b Integers.Ptrofs.zero ->
    Genv.find_symbol se set_id = Some b ->
    c_i = Vint (Integers.Int.repr (Z.of_nat i)) ->
    cal_val_rel v c_v ->
    subrel cal_void_rel R ->
    sg = set_sg ->
    rb_rc_rel _ (set i v) _ (c_event vf sg [ c_i ; c_v ]) R
  | rb_get_rel i vf sg c_i b R:
    vf = Vptr b Integers.Ptrofs.zero ->
    Genv.find_symbol se get_id = Some b ->
    c_i = Vint (Integers.Int.repr (Z.of_nat i)) ->
    subrel cal_val_rel R ->
    sg = get_sg ->
    rb_rc_rel _ (CAL.get i) _ (c_event vf sg [ c_i ]) R
  | rb_inc1_rel vf sg b R:
    vf = Vptr b Integers.Ptrofs.zero ->
    Genv.find_symbol se inc1_id = Some b ->
    subrel cal_nat_rel R ->
    sg = inc1_sg ->
    rb_rc_rel _ inc1 _ (c_event vf sg [ ]) R
  | rb_inc2_rel vf sg b R:
    vf = Vptr b Integers.Ptrofs.zero ->
    Genv.find_symbol se inc2_id = Some b ->
    subrel cal_nat_rel R ->
    sg = inc2_sg ->
    rb_rc_rel _ inc2 _ (c_event vf sg [ ]) R.

  Inductive bq_rc_rel: rc_rel bq_sig c_esig :=
  | bq_enq_rel v vf sg c_v b R:
    vf = Vptr b Integers.Ptrofs.zero ->
    Genv.find_symbol se enq_id = Some b ->
    cal_val_rel v c_v ->
    subrel cal_void_rel R ->
    sg = enq_sg ->
    bq_rc_rel _ (enq v) _ (c_event vf sg [ c_v ]) R
  | bq_deq_rel vf sg b R:
    vf = Vptr b Integers.Ptrofs.zero ->
    Genv.find_symbol se deq_id = Some b ->
    subrel cal_val_rel R ->
    sg = deq_sg ->
    bq_rc_rel _ deq _ (c_event vf sg [ ]) R.

  Program Definition rb_rc : rb_sig <=> c_esig :=
    {|
      refconv_rel := rb_rc_rel;
    |}.
  Next Obligation.
    intros * x y Hxy H.
    destruct H; econstructor; eauto; etransitivity; eauto.
  Qed.

  Program Definition bq_rc : bq_sig <=> c_esig :=
    {|
      refconv_rel := bq_rc_rel;
    |}.
  Next Obligation.
    intros * x y Hxy H.
    destruct H; econstructor; eauto; etransitivity; eauto.
  Qed.

  (* TODO: figure out whether we need typing at all *)
  Inductive args_type_check (vs: list val) (sg: signature) : Prop :=
  | args_tyck ts:
    Cop.val_casted_list vs ts ->
    typlist_of_typelist ts = sig_args sg ->
    args_type_check vs sg.
  Inductive retval_type_check (v: val) (sg: signature) : Prop :=
  | ret_tyck t:
    Cop.val_casted v t ->
    opttyp_of_type t = sig_res sg ->
    retval_type_check v sg.

End MARSHALL.

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

Section RB.
  Open Scope Z_scope.
  Import Ptrofs.
  Context (se:Genv.symtbl).

  Lemma find_set b:
    Genv.find_symbol se set_id = Some b ->
    Genv.find_funct (Clight.globalenv se rb_program) (Vptr b zero) = Some (Internal rb_set).
  Proof.
    intros H. unfold Genv.find_funct, Genv.find_funct_ptr.
    destruct eq_dec; try congruence.
    apply Genv.find_invert_symbol in H. cbn.
    rewrite Genv.find_def_spec. rewrite H. reflexivity.
  Qed.

  Lemma find_get b:
    Genv.find_symbol se get_id = Some b ->
    Genv.find_funct (Clight.globalenv se rb_program) (Vptr b zero) = Some (Internal rb_get).
  Proof.
    intros H. unfold Genv.find_funct, Genv.find_funct_ptr.
    destruct eq_dec; try congruence.
    apply Genv.find_invert_symbol in H. cbn.
    rewrite Genv.find_def_spec. rewrite H. reflexivity.
  Qed.

  Lemma find_inc1 b:
    Genv.find_symbol se inc1_id = Some b ->
    Genv.find_funct (Clight.globalenv se rb_program) (Vptr b zero) = Some (Internal rb_inc1).
  Proof.
    intros H. unfold Genv.find_funct, Genv.find_funct_ptr.
    destruct eq_dec; try congruence.
    apply Genv.find_invert_symbol in H. cbn.
    rewrite Genv.find_def_spec. rewrite H. reflexivity.
  Qed.

  Lemma find_inc2 b:
    Genv.find_symbol se inc2_id = Some b ->
    Genv.find_funct (Clight.globalenv se rb_program) (Vptr b zero) = Some (Internal rb_inc2).
  Proof.
    intros H. unfold Genv.find_funct, Genv.find_funct_ptr.
    destruct eq_dec; try congruence.
    apply Genv.find_invert_symbol in H. cbn.
    rewrite Genv.find_def_spec. rewrite H. reflexivity.
  Qed.

  Inductive R_cnt (id: positive): nat -> mem -> Prop :=
  | R_cnt_intro b v n m:
    Genv.find_symbol se id = Some b ->
    Mem.load Mint32 m b 0 = Some v ->
    cal_nat_rel n v ->
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

(*
  Lemma rb_set_code_correct i v f c1 c2 c_v b m:
    R_rb (f, c1, c2) m ->
    Genv.find_symbol se set_id = Some b ->
    let Rc := fun '(r, m) rx => rx = cr r m in
    L_rb unit (set i v) (f, c1, c2) [=
      a <- (ang_lts_spec (semantics2 rb_program se) @ bot) _
            (li_sig (cq (Vptr b zero) set_sg [Vint (Int.repr (Z.of_nat i)); c_v] m));
      a0 <- sup {n : val * mem | Rc n a}, ret n;
      sup {n : unit * rb_state | (cal_void_rel * R_rb)%rel n a0}, ret n.
  Admitted.
 *)

  Hypothesis Nbound : 4 * Nz <= max_unsigned.
  Hypothesis Nbound' : 4 * Nz <= Int.max_unsigned.
  Hypothesis N_neq_0: Nz <> 0.
  Lemma rb_code_correct:
    L_rb [= (right_arrow (rb_rc se * rel_rc R_rb)%rc)
         @ (right_arrow c_rc)
         @ ang_lts_spec (semantics2 rb_program se) @ bot.
  Proof.
    intros ? [? ? m [ s ]]. destruct s as [ [ f c1 ] c2 ].
    Local Opaque semantics2.
    unfold compose. cbn. unfold rc_adj_right. cbn.
    inf_intro ar. inf_intro x. destruct x as [ ? ? c_m [ mm ] ].
    destruct c_m as [vf sg args].
    inf_intro x. destruct x as [ Rp Hr ]. cbn.
    intm. inf_intro ar'. inf_intro q. destruct q as [ q ].
    inf_intro x. destruct x as [ Rc Hc ]. cbn.
    intm. simple inversion Hc. intros. depsubst.
    inv H3. inv H5. clear Hc H2 H4. rename H1 into HRc.
    simple inversion Hr.
    apply type_pair_des in H2. inv H2.
    apply type_pair_des in H4. inv H4.
    depsubst. inv H3. inv H5.
    depsubst. cbn. intros HRev HRst HRp.
    simple inversion HRst. depsubst. clear H1 H3 Hr. inv H2. inv H4.
    clear HRst. intros HRst HRx.
    unfold fsup. setoid_rewrite Sup.mor.
    setoid_rewrite FCD.ext_ana. cbn.
    rewrite <- Sup.mor.
    simple inversion HRev; intros; depsubst; clear HRev.
    Ltac lts_step := eapply star_left with (t1 := E0) (t2 := E0); [ | | reflexivity ].
    (* set *)
    - clear H7. inv H8.
      apply assert_l. intros Hi. apply inj_lt in Hi.
      rename H0 into Hb. rename H2 into Hv. rename H3 into HRr.
      setoid_rewrite sup_sup. rewrite !Sup.mor.
      (* initial_state *)
      eapply (sup_at (exist _ _ _)); cbn. Unshelve.
      3: {
        cbn. econstructor.
        - eapply find_set; eauto.
        - reflexivity.
        - repeat constructor; try reflexivity.
          eapply val_is_int; eauto.
        - inv HRst. eauto.
      } cbn. rewrite lts_spec_step.
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
        cbn. lts_step.
        {
          econstructor.
          - apply find_set. auto.
          - constructor; cbn; try constructor; try easy.
            + intro contra. inv contra; easy.
            + constructor; try easy. constructor.
        }
        lts_step. { constructor. }
        lts_step.
        {
          econstructor.
          - constructor. econstructor.
            + econstructor.
              * apply eval_Evar_global; [ reflexivity | eassumption ].
              * constructor. reflexivity.
            + econstructor. reflexivity.
            + reflexivity.
          - constructor. reflexivity.
          - cbn. instantiate (1 := c_v).
            apply Cop.cast_val_casted. eapply val_is_int; eauto.
          - cbn. rewrite add_zero_l.
            unfold of_intu, of_int, mul.
            rewrite Int.unsigned_repr.
            rewrite !unsigned_repr.
            eapply assign_loc_value. reflexivity.
            unfold Mem.storev. rewrite unsigned_repr.
            apply Hm'.
            all: unfold Nz in *; try lia.
        }
        lts_step. { constructor. }
        lts_step. { constructor. reflexivity. }
        apply star_refl.
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
        - now apply HRr.
        - apply HRx. cbn. constructor.
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
    - clear H6. inv H7.
      apply assert_l. intros Hi.
      rename H0 into Hb. rename H2 into HRr.
      setoid_rewrite sup_sup. rewrite !Sup.mor.
      (* initial_state *)
      eapply (sup_at (exist _ _ _)); cbn. Unshelve.
      3: {
        cbn. econstructor.
        - eapply find_get; eauto.
        - reflexivity.
        - repeat constructor; reflexivity.
        - inv HRst. eauto.
      } rewrite lts_spec_step.
      rewrite !Sup.mor_join. apply join_l. apply join_l.
      unfold fsup. rewrite !Sup.mor.
      (* internal steps *)
      inv HRst. inv H5. rename mm into m.
      edestruct (H0 i) as (vx & Hvx & Hvr).
      eapply (sup_at (exist _ _ _)); cbn. Unshelve.
      3: {
        cbn. lts_step.
        {
          econstructor.
          - apply find_get. auto.
          - constructor; cbn; try repeat constructor; try easy.
        }
        lts_step.
        { econstructor; eauto.
          - econstructor.
            + constructor. econstructor.
              * econstructor.
                -- eapply eval_Evar_global; try easy.
                   apply H.
                -- constructor. reflexivity.
              * econstructor. reflexivity.
              * reflexivity.
            + eapply deref_loc_value. reflexivity.
              cbn. unfold of_intu, of_int, mul.
              rewrite add_zero_l.
              rewrite Int.unsigned_repr.
              rewrite !unsigned_repr.
              apply Hvx.
              all: unfold Nz in *; try lia.
              rewrite !unsigned_repr.
              all: unfold Nz in *; try lia.
          - cbn. instantiate (1 := vx).
            apply Cop.cast_val_casted. eapply val_is_int; eauto.
          - reflexivity.
        }
        apply star_refl.
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
        apply HRx. cbn. constructor; eauto.
        econstructor; eauto.
      }
      reflexivity.
    (* inc1 *)
    - clear H5. inv H6.
      rename H0 into Hb. rename H1 into HR1.
      setoid_rewrite sup_sup. rewrite !Sup.mor.
      (* initial_state *)
      eapply (sup_at (exist _ _ _)); cbn. Unshelve.
      3: {
        cbn. econstructor.
        - eapply find_inc1; eauto.
        - reflexivity.
        - constructor.
        - inv HRst. eauto.
      } rewrite lts_spec_step.
      rewrite !Sup.mor_join. apply join_l. apply join_l.
      unfold fsup. rewrite !Sup.mor.
      inv HRst. inv H2.
      (* internal steps *)
      inv H1. rename mm into m.
      edestruct (Mem.valid_access_store m Mint32 b0 0) as (m' & Hm').
      {
        constructor.
        - intros ofs Hofs. apply H4. cbn [size_chunk] in Hofs. lia.
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
        cbn. lts_step.
        {
          econstructor.
          - apply find_inc1. auto.
          - constructor; cbn; try repeat constructor; try easy.
        }
        lts_step. { econstructor. }
        lts_step. { econstructor. }
        lts_step. { econstructor. }
        lts_step.
        {
          constructor. econstructor.
          - apply eval_Evar_global; try easy. apply H.
          - eapply deref_loc_value. reflexivity. apply H0.
        }
        lts_step. { econstructor. }
        lts_step.
        {
          econstructor.
          - apply eval_Evar_global; try easy. apply H.
          - econstructor.
            + econstructor.
              * apply eval_Evar_global; try easy. apply H.
              * eapply deref_loc_value. reflexivity. apply H0.
            + constructor.
            + reflexivity.
          - cbn. reflexivity.
          - cbn. econstructor. reflexivity. apply Hm'.
        }
        lts_step.
        { constructor. }
        lts_step.
        {
          econstructor.
          - apply eval_Evar_global; try easy. apply H.
          - econstructor.
            + econstructor.
              * apply eval_Evar_global; try easy. apply H.
              * eapply deref_loc_value. reflexivity.
                unfold Mem.loadv. erewrite Mem.load_store_same; eauto.
            + constructor.
            + cbn. unfold Cop.sem_mod.
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
          - cbn. reflexivity.
          - cbn. econstructor. reflexivity. apply Hm''.
        }
        lts_step. { constructor. }
        lts_step.
        { econstructor; try constructor; reflexivity. }
        apply star_refl.
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
        - apply HR1. cbn. now constructor.
        - apply HRx. cbn. constructor; eauto.
          + econstructor; eauto.
            * erewrite Mem.load_store_same; eauto.
            * cbn. constructor.
              unfold Int.add, Int.modu.
              repeat rewrite !Int.unsigned_repr.
              unfold Int.unsigned. rewrite <- H2.
              rewrite mod_Zmod.
              unfold Nz. f_equal.
              rewrite Nat2Z.inj_succ. reflexivity.
              admit. all: unfold Nz in *; try lia.
              unfold Int.unsigned.
              pose proof (Integers.Int.intrange i).
              unfold Int.max_unsigned. split. lia.
              admit.
              admit.
              admit.

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
            * intros ix. edestruct (H7 ix) as (vx & Hvx & Hrx).
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
    -
  Admitted.

End RB.

Instance subrel_refl {A B}: Reflexive (@subrel A B).
Proof. now intros R x y Hxy. Qed.

Section BQ.
  Context (se: Genv.symtbl) (Hse: Genv.valid_for (erase_program bq_program) se).
  Import Ptrofs.
  Lemma find_enq b:
    Genv.find_symbol se enq_id = Some b ->
    Genv.find_funct (Clight.globalenv se bq_program) (Vptr b zero) = Some (Internal bq_enq).
  Proof.
    intros H. unfold Genv.find_funct, Genv.find_funct_ptr.
    destruct eq_dec; try congruence.
    apply Genv.find_invert_symbol in H. cbn.
    rewrite Genv.find_def_spec. rewrite H. reflexivity.
  Qed.

  Lemma find_deq b:
    Genv.find_symbol se deq_id = Some b ->
    Genv.find_funct (Clight.globalenv se bq_program) (Vptr b zero) = Some (Internal bq_deq).
  Proof.
    intros H. unfold Genv.find_funct, Genv.find_funct_ptr.
    destruct eq_dec; try congruence.
    apply Genv.find_invert_symbol in H. cbn.
    rewrite Genv.find_def_spec. rewrite H. reflexivity.
  Qed.

  Lemma inc2_block:
    exists b, Genv.find_symbol (globalenv ((semantics2 bq_program) se)) inc2_id = Some b
         /\ Genv.find_def (globalenv ((semantics2 bq_program) se)) b = Some (Gfun inc2_ext).
  Proof. apply Genv.find_def_symbol; eauto. Qed.

  Lemma set_block:
    exists b, Genv.find_symbol (globalenv ((semantics2 bq_program) se)) set_id = Some b
         /\ Genv.find_def (globalenv ((semantics2 bq_program) se)) b = Some (Gfun set_ext).
  Proof. apply Genv.find_def_symbol; eauto. Qed.

  Lemma inc1_block:
    exists b, Genv.find_symbol (globalenv ((semantics2 bq_program) se)) inc1_id = Some b
         /\ Genv.find_def (globalenv ((semantics2 bq_program) se)) b = Some (Gfun inc1_ext).
  Proof. apply Genv.find_def_symbol; eauto. Qed.

  Lemma get_block:
    exists b, Genv.find_symbol (globalenv ((semantics2 bq_program) se)) get_id = Some b
         /\ Genv.find_def (globalenv ((semantics2 bq_program) se)) b = Some (Gfun get_ext).
  Proof. apply Genv.find_def_symbol; eauto. Qed.

  Variable S: Type.
  Variable R: S -> mem -> Prop.

  Hypothesis R_ple: forall s m, R s m -> Ple (Genv.genv_next se) (Mem.nextblock m).

  Lemma bq_code_correct:
    slift M_bq [= (right_arrow (bq_rc se * rel_rc R)%rc)
               @ (right_arrow c_rc)
               @ ang_lts_spec (semantics2 bq_program se)
               @ (left_arrow c_rc)
               @ (left_arrow (rb_rc se * rel_rc R)%rc).
  Proof.
    intros ? [? ? m [ s ]]. Local Opaque semantics2.
    unfold compose. cbn. unfold rc_adj_right. cbn.
    inf_intro ar. inf_intro x. destruct x as [ ? ? c_m [ mm ] ].
    destruct c_m as [vf sg args].
    inf_intro x. destruct x as [ Rp Hr ]. cbn.
    intm. inf_intro ar'. inf_intro q. destruct q as [ q ].
    inf_intro x. destruct x as [ Rc Hc ]. cbn.
    intm. simple inversion Hc. intros. depsubst.
    inv H3. inv H5. clear Hc H2 H4. rename H1 into HRc.
    simple inversion Hr.
    apply type_pair_des in H2. inv H2.
    apply type_pair_des in H4. inv H4.
    depsubst. inv H3. inv H5.
    depsubst. cbn. intros HRev HRst HRp.
    simple inversion HRst. depsubst. clear H1 H3 Hr. inv H2. inv H4.
    clear HRst. intros HRst HRx.
    unfold fsup. setoid_rewrite Sup.mor.
    setoid_rewrite FCD.ext_ana. cbn.
    rewrite <- Sup.mor.
    simple inversion HRev; intros; depsubst; clear HRev.
    Ltac lts_step := eapply star_left with (t1 := E0) (t2 := E0); [ | | reflexivity ].
    (* enq *)
    - clear H6. inv H7.
      rename H0 into Hb. rename H1 into Hv. rename H2 into HRr.
      edestruct inc2_block as (inc2b & Hb1 & Hb2).
      edestruct set_block as (setb & Hb3 & Hb4).
      setoid_rewrite sup_sup.
      rewrite !Sup.mor. eapply (sup_at (exist _ _ _)); cbn.
      Unshelve.
      3: {
        cbn. econstructor.
        - apply find_enq; auto.
        - reflexivity.
        - constructor.
          (* the type of the enq argument *)
          + eapply val_is_int. eauto.
          + constructor.
        - eapply R_ple; eauto.
      }
      rewrite lts_spec_step.
      rewrite !Sup.mor_join. apply join_l. apply join_l.
      unfold fsup. rewrite !Sup.mor.
      eapply (sup_at (exist _ _ _)). cbn.
      Unshelve.
      3: {
        cbn. lts_step.
        {
          constructor. apply find_enq; auto.
          constructor; cbn; repeat constructor; try easy.
          intros x y [ ] [ ]; try easy. subst. easy.
        }
        lts_step.
        { constructor. }
        lts_step.
        {
          econstructor.
          - cbn. reflexivity.
          - econstructor.
            + eapply eval_Evar_global.
              * reflexivity.
              * apply Hb1.
            + eapply deref_loc_reference. reflexivity.
          - constructor.
          - unfold Genv.find_funct.
            destruct Integers.Ptrofs.eq_dec; try congruence.
            unfold Genv.find_funct_ptr. rewrite Hb2. reflexivity.
          - cbn. reflexivity.
        }
        apply star_refl.
      }
      (* external call to [inc2] *)
      rewrite lts_spec_step.
      rewrite !Sup.mor_join. apply join_l. apply join_r.
      unfold fsup. rewrite !Sup.mor.
      eapply (sup_at (exist _ _ _)); cbn.
      Unshelve.
      3: {
        cbn. econstructor.
        unfold Genv.find_funct.
        destruct Integers.Ptrofs.eq_dec; try congruence.
        unfold Genv.find_funct_ptr.
        Local Transparent semantics2. cbn in Hb2 |- *.
        rewrite Hb2. reflexivity.
      }
      Local Opaque semantics2.
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
        cbn. econstructor.
        - eapply rb_inc2_rel; eauto. reflexivity.
        - constructor. eauto. reflexivity.
        - reflexivity.
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
      3: {
        cbn. lts_step. { constructor. }
        lts_step. { constructor. }
        lts_step. { constructor. }
        lts_step.
        {
          econstructor.
          - cbn. reflexivity.
          - econstructor.
            + eapply eval_Evar_global.
              * reflexivity.
              * apply Hb3.
            + eapply deref_loc_reference. reflexivity.
          - econstructor.
            + constructor. reflexivity.
            + cbn. apply Cop.cast_val_casted.
              constructor. reflexivity.
            + econstructor.
              * constructor. reflexivity.
              * cbn. apply Cop.cast_val_casted.
                eapply val_is_int. eauto.
              * constructor.
          - unfold Genv.find_funct.
            destruct Integers.Ptrofs.eq_dec; try congruence.
            unfold Genv.find_funct_ptr.
            Local Transparent semantics2. cbn in Hb4 |- *.
            rewrite Hb4. reflexivity.
          - cbn. reflexivity.
        }
        apply star_refl.
      }
      (* external call to [set] *)
      Local Opaque semantics2.
      rewrite lts_spec_step.
      rewrite !Sup.mor_join. apply join_l. apply join_r.
      unfold fsup. rewrite !Sup.mor.
      eapply (sup_at (exist _ _ _)); cbn. Unshelve.
      3: {
        cbn. econstructor.
        unfold Genv.find_funct.
        destruct Integers.Ptrofs.eq_dec; try congruence.
        unfold Genv.find_funct_ptr.
        Local Transparent semantics2. cbn in Hb4 |- *.
        rewrite Hb4. reflexivity.
      }
      Local Opaque semantics2.
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
        cbn. econstructor.
        - econstructor; try reflexivity; eauto.
          rewrite H1. rewrite Int.repr_unsigned. reflexivity.
        - econstructor; try reflexivity; eauto.
        - reflexivity.
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
      3: {
        cbn. lts_step. { constructor. }
        lts_step. { constructor. }
        lts_step. { constructor. reflexivity. }
        apply star_refl.
      }
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
        cbn. apply HRp. split.
        - apply HRr. constructor.
        - apply HRx. eauto.
      }
      cbn. reflexivity.
    (* deq *)
    - clear H5. inv H6.
      edestruct inc1_block as (inc1b & Hb1 & Hb2).
      edestruct get_block as (getb & Hb3 & Hb4).
      (* initial_state *)
      setoid_rewrite sup_sup.
      rewrite !Sup.mor. eapply (sup_at (exist _ _ _)); cbn.
      Unshelve.
      3: {
        cbn. econstructor.
        - apply find_deq; auto.
        - reflexivity.
        - constructor.
        - eapply R_ple; eauto.
      }
      rewrite lts_spec_step.
      rewrite !Sup.mor_join. apply join_l. apply join_l.
      unfold fsup. rewrite !Sup.mor.
      eapply (sup_at (exist _ _ _)). cbn.
      Unshelve.
      3: {
        cbn. lts_step.
        {
          constructor. apply find_deq; auto.
          constructor; cbn; repeat constructor; try easy.
        }
        lts_step. { constructor. }
        lts_step.
        {
          econstructor.
          - cbn. reflexivity.
          - econstructor.
            + eapply eval_Evar_global.
              * reflexivity.
              * apply Hb1.
            + eapply deref_loc_reference. reflexivity.
          - constructor.
          - unfold Genv.find_funct.
            destruct Integers.Ptrofs.eq_dec; try congruence.
            unfold Genv.find_funct_ptr. rewrite Hb2. reflexivity.
          - cbn. reflexivity.
        }
        apply star_refl.
      }
      (* external call to [inc1] *)
      rewrite lts_spec_step.
      rewrite !Sup.mor_join. apply join_l. apply join_r.
      unfold fsup. rewrite !Sup.mor.
      eapply (sup_at (exist _ _ _)); cbn.
      Unshelve.
      3: {
        cbn. econstructor.
        unfold Genv.find_funct.
        destruct Integers.Ptrofs.eq_dec; try congruence.
        unfold Genv.find_funct_ptr.
        Local Transparent semantics2. cbn in Hb2 |- *.
        rewrite Hb2. reflexivity.
      }
      Local Opaque semantics2.
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
        cbn. econstructor.
        - eapply rb_inc1_rel; eauto. reflexivity.
        - constructor. eauto. reflexivity.
        - reflexivity.
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
      3: {
        cbn. lts_step. { constructor. }
        lts_step. { constructor. }
        lts_step. { constructor. }
        lts_step.
        {
          econstructor.
          - cbn. reflexivity.
          - econstructor.
            + eapply eval_Evar_global.
              * reflexivity.
              * apply Hb3.
            + eapply deref_loc_reference. reflexivity.
          - econstructor.
            + constructor. reflexivity.
            + cbn. apply Cop.cast_val_casted.
              constructor. reflexivity.
            + econstructor.
          - unfold Genv.find_funct.
            destruct Integers.Ptrofs.eq_dec; try congruence.
            unfold Genv.find_funct_ptr.
            Local Transparent semantics2. cbn in Hb4 |- *.
            rewrite Hb4. reflexivity.
          - cbn. reflexivity.
        }
        apply star_refl.
      }
      (* external call to [get] *)
      Local Opaque semantics2.
      rewrite lts_spec_step.
      rewrite !Sup.mor_join. apply join_l. apply join_r.
      unfold fsup. rewrite !Sup.mor.
      eapply (sup_at (exist _ _ _)); cbn. Unshelve.
      3: {
        cbn. econstructor.
        unfold Genv.find_funct.
        destruct Integers.Ptrofs.eq_dec; try congruence.
        unfold Genv.find_funct_ptr.
        Local Transparent semantics2. cbn in Hb4 |- *.
        rewrite Hb4. reflexivity.
      }
      Local Opaque semantics2.
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
        cbn. econstructor.
        - econstructor; try reflexivity; eauto.
          rewrite H3. rewrite Int.repr_unsigned. reflexivity.
        - econstructor; try reflexivity; eauto.
        - reflexivity.
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
      3: {
        cbn. lts_step. { constructor. }
        lts_step. { constructor. }
        lts_step.
        {
          econstructor.
          - constructor. reflexivity.
          - cbn. apply Cop.cast_val_casted.
            eapply val_is_int. eauto.
          - reflexivity.
        }
        apply star_refl.
      }
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
        cbn. apply HRp. split.
        - apply H1. cbn. eauto.
        - apply HRx. eauto.
      }
      cbn. reflexivity.
  Qed.

End BQ.

(* TODO: clean up the obsolete code below *)
(*
Notation li_cmem := LanguageInterface.li_c.
Notation cqmem := LanguageInterface.cq.
Notation crmem := LanguageInterface.cr.

Require Import compcertox.Lifting.
Require Import Effects.
(** ** Correctness  *)
Section CORRECT.

  Context (se:Genv.symtbl).

  Definition umem: li_c ~> li_cmem :=
    fun _ '(li_sig q) =>
      match q with
      | cqmem vf sg args m =>
        r <- query_int (cq vf sg args);
        match r with
        | cr retval => ret (crmem retval m)
        end
      end.

  Definition iota {S}: sig li_cmem # S ~> sig li_c # (mem * S) :=
    fun _ '(st q (m, s)) =>
      match q with
      | li_sig (cq vf sg args) =>
          rs <- int (st (li_sig (cqmem vf sg args m)) s);
          match rs with
          | (crmem retval m', s') => ret (cr retval, (m', s'))
          end
      end.

  Close Scope Z_scope.
  (* L2 is the overlay *)
  Record certi_layer {E1 E2 S1 S2} :=
    {
      L1: 0 ~> E1 # S1;
      L1_adj: E1 <~> li_c;
      L2: 0 ~> E2 # S2;
      L2_adj: E2 <~> li_c;
      module: list Clight.program;
      sk: AST.program unit unit;
      abs_rel: S2 -> mem * S1 -> Prop;

      layer_ref:
      L2 [= right_arrow (lift_adjunction L2_adj abs_rel)
         @ iota
         @ slift (ang_lts_spec (CModule.semantics module sk se))
         @ slift (umem @ left_arrow L1_adj)
         @ L1;
    }.

  Hypothesis se_valid: Genv.valid_for (erase_program bq_program) se.

  Lemma inc2_block:
    exists b, Genv.find_symbol (globalenv ((semantics2 bq_program) se)) inc2_id = Some b
         /\ Genv.find_def (globalenv ((semantics2 bq_program) se)) b = Some (Gfun inc2_ext).
  Proof. apply Genv.find_def_symbol; eauto. Qed.

  Lemma set_block:
    exists b, Genv.find_symbol (globalenv ((semantics2 bq_program) se)) set_id = Some b
         /\ Genv.find_def (globalenv ((semantics2 bq_program) se)) b = Some (Gfun set_ext).
  Proof. apply Genv.find_def_symbol; eauto. Qed.

  Instance srun_morphism {E S A} (k: S):
    CDL.Morphism (@srun E S A k).
  Proof.
    unfold srun. split.
    - intros x y. apply Sup.mor.
    - intros x y. apply Inf.mor.
  Qed.

  Hypothesis Nneq0: CAL.N <> 0%nat.

  Lemma enq_helper f c1 n v:
    c1 < CAL.N -> n < CAL.N ->
    slice (update f ((c1 + n) mod CAL.N) v) c1 (S n) = slice f c1 n ++ [v].
  Proof. Admitted.

  Program Definition bq: @certi_layer rb_sig bq_sig rb_state bq_state :=
    {|
      L1 := L_rb;
      L1_adj := rb_adj se;
      L2 := L_bq;
      L2_adj := bq_adj se;
      module := [bq_program];
      sk := erase_program bq_program;
      abs_rel bq '(m, rb) := rb_bq rb bq /\ Ple (Genv.genv_next se) (Mem.nextblock m);
    |}.
  Next Obligation.
    replace (CModule.semantics [bq_program] (erase_program bq_program))
      with (Clight.semantics2 bq_program) by admit.
    intros ? [? m bq]. destruct m.
    (* enq *)
    Local Opaque semantics2.
    - edestruct inc2_block as (inc2b & Hb1 & Hb2).
      edestruct set_block as (setb & Hb3 & Hb4).
      setoid_rewrite Sup.mor. apply sup_iff. intros bq_len.
      setoid_rewrite FCD.ext_ana. cbn.
      unfold bq_adj, right_arr. cbn.
      rewrite !compose_assoc.
      unfold compose at 1. cbn.
      unfold bq_right. unfold finf.
      rewrite !Inf.mor. apply inf_iff. intros [q [Hbqr Hbqt]]. cbn.
      unfold query_int.
      rewrite srun_bind. rewrite srun_int.
      rewrite apply_bind. rewrite apply_int_r.
      unfold compose at 6. cbn.
      setoid_rewrite Inf.mor. setoid_rewrite Inf.mor.
      apply inf_iff. intros [[m rb] [Hr Hm]]. cbn.
      rewrite apply_bind. rewrite apply_int_r.
      unfold compose at 10. unfold iota at 3.
      destruct q as [vf sg args]. cbn.
      rewrite apply_bind. rewrite apply_int_r.
      unfold compose at 13. cbn.
      match goal with
      | |- context[ bind ?f (bind ?g (bind ?h _)) ] =>
          set (f1 := f);
          set (f2 := g);
          set (f3 := h)
      end.
      setoid_rewrite sup_sup.
      do 5 rewrite Sup.mor.
      eapply (sup_at (exist _ (Callstate vf args Kstop m) _)). cbn. Unshelve.
      2: {
        cbn. inv Hbqr. unfold enq_sg. econstructor.
        - unfold Genv.find_funct.
          destruct Integers.Ptrofs.eq_dec; try congruence.
          unfold Genv.find_funct_ptr.
          apply Genv.find_invert_symbol in H4.
          unfold Clight.globalenv. cbn.
          rewrite Genv.find_def_spec. rewrite H4.
          cbn. reflexivity.
        - reflexivity.
        - constructor.
          (* the type of the enq argument *)
          + admit.
          + constructor.
        - cbn. assumption.
      }

      rewrite lts_spec_step.
      rewrite !Sup.mor_join. apply join_l. apply join_l.
      unfold fsup. do 5 rewrite Sup.mor. inv Hbqr.
      eapply (sup_at (exist _ _ _)). cbn.
      Unshelve.
      3: {
        cbn. lts_step.
        {
          constructor. instantiate (1 := bq_enq).
          - unfold Genv.find_funct.
            destruct Integers.Ptrofs.eq_dec; try congruence.
            unfold Genv.find_funct_ptr.
            apply Genv.find_invert_symbol in H4.
            unfold Clight.globalenv. cbn.
            Local Transparent semantics2.
            cbn. rewrite Genv.find_def_spec. rewrite H4.
            cbn. reflexivity.
          - constructor; cbn; try constructor.
            + unfold In. easy.
            + constructor.
            (* because we are using semantics2
               enq_arg_id ≠ bq_enq_tmp *)
            + intros x y Hx Hy. inv Hx; inv Hy; easy.
        }
        lts_step.
        {
          unfold bq_enq at 2. cbn.
          unfold bq_enq_body. constructor.
        }
        lts_step.
        {
          econstructor.
          - cbn. reflexivity.
          - econstructor.
            + eapply eval_Evar_global.
              * reflexivity.
              * apply Hb1.
            + eapply deref_loc_reference. reflexivity.
          - constructor.
          - unfold Genv.find_funct.
            destruct Integers.Ptrofs.eq_dec; try congruence.
            unfold Genv.find_funct_ptr. rewrite Hb2. reflexivity.
          - cbn. reflexivity.
        }
        apply star_refl.
      }

      rewrite lts_spec_step.
      rewrite !Sup.mor_join. apply join_l. apply join_r.
      unfold fsup. rewrite !Sup.mor.
      eapply (sup_at (exist _ _ _)).
      cbn. Unshelve.
      3: {
        cbn. econstructor.
        unfold Genv.find_funct.
        destruct Integers.Ptrofs.eq_dec; try congruence.
        unfold Genv.find_funct_ptr.
        Local Transparent semantics2. cbn in Hb2 |- *.
        rewrite Hb2. reflexivity.
      }
      Local Opaque semantics2.
      unfold query_int.
      rewrite srun_bind. rewrite srun_int.
      rewrite apply_bind. rewrite apply_int_r.
      unfold compose at 3. cbn.
      unfold compose at 3. cbn.
      unfold query_int.
      rewrite apply_bind. rewrite apply_int_r. cbn.
      rewrite !Sup.mor. eapply (sup_at _).
      unfold fsup. rewrite !Sup.mor.
      eapply (sup_at (exist _ inc2 _)). cbn. Unshelve.
      2: {
        cbn. split.
        - constructor. apply Hb1.
        - econstructor. constructor. reflexivity.
      }
      rewrite srun_bind. rewrite apply_bind.
      rewrite srun_bind. rewrite apply_bind.
      rewrite srun_int. rewrite apply_int_r. cbn.
      rewrite !bind_bind. inv Hr. cbn.
      rewrite bind_ret_r. unfold finf.
      rewrite !Inf.mor. apply inf_iff.
      intros [rval [Hrval Hrty]]. cbn.
      repeat (setoid_rewrite FCD.ext_ana; cbn).
      rewrite !Sup.mor.
      eapply (sup_at (exist _ _ _)). cbn. Unshelve.
      3: { cbn. econstructor. }

      rewrite lts_spec_step.
      rewrite !Sup.mor_join. apply join_l. apply join_l.
      unfold fsup. rewrite !Sup.mor.
      eapply (sup_at (exist _ _ _)). cbn. Unshelve.
      3: {
        cbn.
        lts_step.
        { constructor. }
        lts_step.
        { constructor. }
        lts_step.
        { constructor. }
        lts_step.
        {
          econstructor.
          - cbn. reflexivity.
          - econstructor.
            + eapply eval_Evar_global.
              * reflexivity.
              * apply Hb3.
            + eapply deref_loc_reference. reflexivity.
          - econstructor.
            + constructor. reflexivity.
            + cbn. inv Hrval.
              (* type *)
              * exfalso. admit.
              * depsubst. reflexivity.
              * admit.
            + econstructor.
              * constructor. reflexivity.
              * cbn. instantiate (1 := arg).
                (* Type of enq argument *)
                admit.
              * constructor.
          - unfold Genv.find_funct.
            destruct Integers.Ptrofs.eq_dec; try congruence.
            unfold Genv.find_funct_ptr.
            Local Transparent semantics2. cbn in Hb4 |- *.
            rewrite Hb4. reflexivity.
          - cbn. reflexivity.
        }
        apply star_refl.
      }

      rewrite lts_spec_step.
      rewrite !Sup.mor_join. apply join_l. apply join_r.
      unfold fsup. rewrite !Sup.mor.
      eapply (sup_at (exist _ _ _)). cbn. Unshelve.
      3: {
        cbn. econstructor.
        unfold Genv.find_funct.
        destruct Integers.Ptrofs.eq_dec; try congruence.
        unfold Genv.find_funct_ptr.
        Local Transparent semantics2. cbn in Hb4 |- *.
        rewrite Hb4. reflexivity.
      }
      Local Opaque semantics2.
      unfold query_int.
      rewrite srun_bind. rewrite srun_int.
      rewrite apply_bind. rewrite apply_int_r.
      unfold compose at 3. cbn.
      unfold compose at 3. cbn.
      unfold query_int.
      rewrite apply_bind. rewrite apply_int_r. cbn.
      rewrite !Sup.mor. eapply sup_at.
      unfold fsup. rewrite !Sup.mor.
      inv Hrval. 1, 3: admit. depsubst.
      eapply (sup_at (exist _ (set ((c1 + n) mod CAL.N) v) _)). cbn. Unshelve.
      2: {
        cbn. split.
        - constructor; auto.
          constructor. auto.
        - unfold set_sg. econstructor.
          2: reflexivity. constructor.
          constructor. reflexivity.
          constructor. 2: constructor.
          (* type of the enq argument *)
          admit.
      }
      intm. apply assert_r.
      2: { apply Nat.mod_upper_bound. auto. }
      unfold finf. rewrite !Inf.mor.
      apply inf_iff. intros [retv [Hr Htyr]]. cbn.
      repeat (setoid_rewrite FCD.ext_ana; cbn).
      rewrite !Sup.mor. eapply (sup_at (exist _ _ _)).
      cbn. Unshelve.
      3: { cbn. constructor. }

      rewrite lts_spec_step. rewrite !Sup.mor_join.
      apply join_l. apply join_l.
      unfold fsup. rewrite !Sup.mor. eapply (sup_at (exist _ _ _)).
      cbn. Unshelve.
      3: {
        cbn.
        lts_step.
        { constructor. }
        lts_step.
        { constructor. }
        lts_step.
        { constructor. reflexivity. }
        apply star_refl.
      }

      rewrite lts_spec_step. rewrite !Sup.mor_join. apply join_r.
      unfold fsup. rewrite !Sup.mor. eapply (sup_at (exist _ _ _)).
      cbn. Unshelve.
      3: { cbn. constructor. }
      setoid_rewrite FCD.ext_ana. cbn.
      setoid_rewrite FCD.ext_ana. cbn.
      setoid_rewrite FCD.ext_ana. cbn.
      subst f3. cbn. setoid_rewrite FCD.ext_ana. cbn.
      setoid_rewrite FCD.ext_ana. cbn.
      subst f2. cbn.
      unfold fsup. rewrite !Sup.mor. eapply (sup_at (exist _ _ _)).
      cbn. Unshelve.
      3: {
        cbn. split; auto. apply bq_rb_intro with (n := S n); auto.
        - rewrite slice_length in bq_len.
          apply Nat.le_succ_l. auto.
        - change (S ?x) with (1 + x).
          rewrite Nat.add_mod_idemp_r by auto. f_equal.
          induction c1; cbn in *; auto.
      }
      setoid_rewrite FCD.ext_ana. cbn.
      setoid_rewrite FCD.ext_ana. cbn.
      subst f1. cbn.
      unfold fsup. rewrite !Sup.mor.
      eapply (sup_at (exist _ tt _)).
      cbn. Unshelve.
      2: {
        cbn. split.
        - apply unit_val.
        - unfold enq_sg. econstructor; cbn.
          + instantiate (1 := Tvoid). constructor.
          + reflexivity.
      }
      setoid_rewrite FCD.ext_ana. cbn.
      setoid_rewrite FCD.ext_ana. cbn.
      unfold ret. rstep. cbn.
      replace (slice f c1 n ++ [v])
        with (slice (update f ((c1 + n) mod CAL.N) v) c1 (S n)).
      constructor. apply enq_helper; auto.
      rewrite slice_length in bq_len; auto.
    - admit.
  Admitted.

  Definition empty_adj_left {E}: 0 ~> E := bot.

  Definition empty_adj_right {E}: E ~> 0 := top.

  Lemma empty_adj_epsilon {E}:
    (@empty_adj_left E) @ (@empty_adj_right E) [= identity.
  Proof.
    unfold empty_adj_left, empty_adj_right, compose, identity.
    intros ? m. unfold apply.
    Local Transparent bot. unfold bot. cbn.
    fcd. apply sup_iff. intros [].
  Qed.

  Lemma empty_adj_eta {E}:
    identity [= (@empty_adj_right E) @ (@empty_adj_left E).
  Proof.
    unfold empty_adj_left, empty_adj_right, compose, identity.
    intros ? m. unfold apply.
    Local Transparent top. unfold top. cbn.
    fcd. apply inf_iff. intros [].
  Qed.

  Definition empty_adj {E}: 0 <~> E :=
    {|
      left_arrow := empty_adj_left;
      right_arrow := empty_adj_right;
      epsilon := empty_adj_epsilon;
      eta := empty_adj_eta;
    |}.

  Program Definition rb: @certi_layer 0 rb_sig unit rb_state :=
    {|
      L1 := bot;
      L1_adj := empty_adj;
      L2 := L_rb;
      L2_adj := rb_adj se;
      module := [rb_program];
      sk := erase_program rb_program;
      abs_rel rb '(m, tt) := Ple (Genv.genv_next se) (Mem.nextblock m);
    |}.
  Next Obligation.
  Admitted.

End CORRECT.
*)
