From compcert Require Import Integers.
Require Import List Coqlib.
Require Import AST CAsm.
Require Asm.
Import ListNotations.

(** * §F.4 Simulation between C and Asm components *)

Notation hello_bytes := [ Byte.repr 104; Byte.repr 101; Byte.repr 108; Byte.repr 108; Byte.repr 111 ].
Notation uryyb_bytes := [ Byte.repr 117; Byte.repr 114; Byte.repr 121; Byte.repr 121; Byte.repr 98].

Definition secret_main_id: positive := 1.
Definition secret_rot13_id: positive := 2.
Definition secret_write_id: positive := 3.
Definition secret_msg_id: positive := 4.

Definition msg_il : list init_data :=
  [ Init_int8 (Int.repr 117); (* u *)
    Init_int8 (Int.repr 114); (* r *)
    Init_int8 (Int.repr 121); (* y *)
    Init_int8 (Int.repr 121); (* y *)
    Init_int8 (Int.repr 98) ]. (* b *)

Definition msg_globvar : globvar unit :=
  {|
    gvar_info := tt;
    gvar_init := msg_il;
    gvar_readonly := false;
    gvar_volatile := false;
  |}.

Definition write_sig : signature :=
  {| sig_args := [Tint; Tptr; Tint]; sig_res := Tint; sig_cc := cc_default; |}.
Definition rot13_sig : signature :=
  {| sig_args := [Tptr; Tint]; sig_res := Tvoid; sig_cc := cc_default; |}.
Definition write: Asm.fundef := External (EF_external "write" write_sig).
Definition rot13: Asm.fundef := External (EF_external "rot13" rot13_sig).

Section CODE.
Import Asm.
Definition secret_main_code: code := [
    Pallocframe 16 (Ptrofs.repr 8) (Ptrofs.repr 0);
    Pleaq RDI (Addrmode None None (inr (secret_msg_id, Ptrofs.repr 0)));
    Pmovl_ri RSI (Int.repr 5);
    Pcall_s secret_rot13_id rot13_sig;
    Pmovl_ri RDI (Int.repr 1);
    Pleaq RSI (Addrmode None None (inr (secret_msg_id, Ptrofs.repr 0)));
    Pmovl_ri RDX (Int.repr 5);
    Pcall_s secret_write_id write_sig;
    Pmovl_ri RAX (Int.repr 0);
    Pfreeframe 16 (Ptrofs.repr 8) (Ptrofs.repr 0);
    Pret
  ].
End CODE.

Definition secret_main_fundef: Asm.function :=
  Asm.mkfunction signature_main secret_main_code.

Definition secret_asm_program: Asm.program :=
  {|
    prog_defs := [
      (secret_main_id, Gfun (Internal secret_main_fundef));
      (secret_rot13_id, Gfun rot13);
      (secret_write_id, Gfun write);
      (secret_msg_id, Gvar msg_globvar)];
    prog_public := nil;
    prog_main := Some secret_main_id;
  |}.

Require Import LanguageInterface Smallstep Memory Values Globalenvs Events.

Section SECRET_SPEC.

  Variant secret_state :=
    | secret1 | secret2 | secret3 | secret4 | secret5 | secret6.

  Section WITH_SE.
    Context (se: Genv.symtbl).
    Inductive secret_spec_initial_state: query li_c -> secret_state * mem -> Prop :=
    | secret_spec_initial_state_intro sg m b
        (HF: Genv.find_symbol se secret_main_id = Some b)
        (HSG: sg = signature_main):
      secret_spec_initial_state (cq (Vptr b Ptrofs.zero) sg nil m) (secret1, m).
    Inductive secret_spec_at_external: secret_state * mem -> query li_c -> Prop :=
    | secret_spec_at_external_intro1 m sg b1 b2
        (HB1: Genv.find_symbol se secret_rot13_id = Some b1)
        (HB2: Genv.find_symbol se secret_msg_id = Some b2)
        (HSG: sg = rot13_sig):
      secret_spec_at_external (secret2, m)
        (cq (Vptr b1 Ptrofs.zero) sg [ Vptr b2 Ptrofs.zero; Vint (Int.repr 5) ] m)
    | secret_spec_at_external_intro2 m sg b1 b2
        (HB1: Genv.find_symbol se secret_write_id = Some b1)
        (HB2: Genv.find_symbol se secret_msg_id = Some b2)
        (HSG: sg = write_sig):
      secret_spec_at_external (secret4, m)
        (cq (Vptr b1 Ptrofs.zero) sg [ Vint (Int.repr 1); Vptr b2 Ptrofs.zero; Vint (Int.repr 5) ] m).
    Inductive secret_spec_after_external: secret_state * mem -> reply li_c -> secret_state * mem -> Prop :=
    | secret_spec_after_external_intro1 m m' v b
        (HB: Genv.find_symbol se secret_msg_id = Some b):
        secret_spec_after_external (secret2, m) (cr v m') (secret3, m')
    | secret_spec_after_external_intro2 m m' v:
        secret_spec_after_external (secret4, m) (cr v m') (secret5, m').
    Inductive secret_spec_final_state: secret_state * mem -> reply li_c -> Prop :=
    | secret_spec_final_state_intro m:
        secret_spec_final_state (secret6, m) (cr (Vint Int.zero) m).
    Inductive secret_step : secret_state * mem -> trace -> secret_state * mem -> Prop :=
    | secret_step1 m (HFlag: Mem.alloc_flag m = true):
      secret_step (secret1, m) E0 (secret2, m)
    | secret_step2 m: secret_step (secret3, m) E0 (secret4, m)
    | secret_step3 m: secret_step (secret5, m) E0 (secret6, m).

  End WITH_SE.

  Definition secret_spec: semantics li_c li_c :=
    {|
      activate se :=
        {|
          Smallstep.step _ := secret_step;
          Smallstep.initial_state := secret_spec_initial_state se;
          Smallstep.at_external := secret_spec_at_external se;
          Smallstep.after_external := secret_spec_after_external se;
          Smallstep.final_state := secret_spec_final_state;
          Smallstep.globalenv := tt;
        |};
      skel := AST.erase_program secret_asm_program;
      footprint := AST.footprint_of_program secret_asm_program;
    |}.

End SECRET_SPEC.

Require Import InjectFootprint.

Section CODE_PROOF.

  Import Maps.

  Lemma find_funct_spec {F V} b id se (p: AST.program F V):
    Genv.find_symbol se id = Some b ->
    Genv.find_funct (Genv.globalenv se p) (Vptr b Ptrofs.zero) =
      match (prog_defmap p) ! id with
      | Some (Gfun f) => Some f
      | _ => None
      end.
  Proof.
    intros Hf. cbn.
    destruct Ptrofs.eq_dec; try easy.
    unfold Genv.find_funct_ptr. rewrite Genv.find_def_spec.
    erewrite Genv.find_invert_symbol; eauto.
  Qed.

  Import Asm.
  Require Import Lifting.       (* eprod_crush *)

  Inductive secret_match_state: ccworld (cc_c injp @ cc_c_asm) -> secret_state * mem -> block * Asm.state -> Prop :=
  | secret_match_state1 rs nb b sg j m1 m2 Hm se
      (HPC: rs PC = Vptr b Ptrofs.zero)
      (HB: Genv.find_symbol se secret_main_id = Some b)
      (HSP: Mach.valid_blockv (Mem.nextblock m2) (rs RSP))
      (HSG: sg = signature_main)
      (HNB: nb = Mem.nextblock m2)
      (HRA: Val.has_type (rs RA) Tptr):
    secret_match_state (se, injpw j m1 m2 Hm, caw sg rs m2)
      (secret1, m1) (nb, State rs m2 true)
  | secret_match_state2 rs nb se b1 b2 b3 sg wi m1 m2 j Hm mx1 mx2 Hmx sp_b (rs0: regset)
      (HWI: wi = injpw j m1 m2 Hm)
      (HACC: injp_acc wi (injpw j mx1 mx2 Hmx))
      (HB1: Genv.find_symbol se secret_rot13_id = Some b1)
      (HB2: Genv.find_symbol se secret_main_id = Some b2)
      (HB3: Genv.find_symbol se secret_msg_id = Some b3)
      (HPC: rs PC = Vptr b1 Ptrofs.zero)
      (HRA: rs RA = Vptr b2 (Ptrofs.repr 4))
      (HRSI: rs (IR RSI) = Vint (Int.repr 5))
      (HRDI: rs (IR RDI) = Vptr b3 Ptrofs.zero)
      (HLSP: Mem.loadv Mptr mx2 (Val.offset_ptr rs#RSP (Ptrofs.repr 0)) = Some (rs0 RSP))
      (HLRA: Mem.loadv Mptr mx2 (Val.offset_ptr rs#RSP (Ptrofs.repr 8)) = Some (rs0 RA))
      (HCALLEE: forall r, Conventions1.is_callee_save r = true -> rs (preg_of r) = rs0 (preg_of r))
      (HSG: sg = signature_main)
      (HSP: Mach.valid_blockv nb (rs0 RSP))
      (HSPB1: Plt sp_b (Mem.nextblock mx2))
      (HSPB2: ~ Plt sp_b nb)
      (HSPB: rs#RSP = Vptr sp_b Ptrofs.zero)
      (HSPB3: forall b d, j b = Some (sp_b, d) -> False)
      (HFREE: Mem.range_perm mx2 sp_b 0 16 Cur Freeable)
      (HNB: nb = Mem.nextblock m2):
    secret_match_state (se, wi, caw sg rs0 m2)
      (secret2, mx1) (nb, State rs mx2 true)
  | secret_match_state3  rs nb se sg wi m1 m2 j Hm mx1 mx2 jx Hmx sp_b (rs0: regset) b
      (HWI: wi = injpw j m1 m2 Hm)
      (HACC: injp_acc wi (injpw jx mx1 mx2 Hmx))
      (HPC: rs PC = Vptr b (Ptrofs.repr 4))
      (HB: Genv.find_symbol se secret_main_id = Some b)
      (HSP: Mach.valid_blockv nb (rs0 RSP))
      (HLSP: Mem.loadv Mptr mx2 (Val.offset_ptr rs#RSP (Ptrofs.repr 0)) = Some (rs0 RSP))
      (HLRA: Mem.loadv Mptr mx2 (Val.offset_ptr rs#RSP (Ptrofs.repr 8)) = Some (rs0 RA))
      (HCALLEE: forall r, Conventions1.is_callee_save r = true -> rs (preg_of r) = rs0 (preg_of r))
      (HSG: sg = signature_main)
      (HSPB: rs#RSP = Vptr sp_b Ptrofs.zero)
      (HSPB1: Plt sp_b (Mem.nextblock mx2))
      (HSPB2: ~ Plt sp_b nb)
      (HSPB: rs#RSP = Vptr sp_b Ptrofs.zero)
      (HSPB3: forall b d, jx b = Some (sp_b, d) -> False)
      (HFREE: Mem.range_perm mx2 sp_b 0 16 Cur Freeable)
      (HNB: nb = Mem.nextblock m2):
    secret_match_state  (se, wi, caw sg rs0 m2)
      (secret3, mx1) (nb, State rs mx2 true)
  | secret_match_state4 rs nb se b1 b2 b3 sg wi m1 m2 j jx Hm mx1 mx2 Hmx sp_b (rs0: regset)
      (HWI: wi = injpw j m1 m2 Hm)
      (HACC: injp_acc wi (injpw jx mx1 mx2 Hmx))
      (HB1: Genv.find_symbol se secret_write_id = Some b1)
      (HB2: Genv.find_symbol se secret_main_id = Some b2)
      (HB3: Genv.find_symbol se secret_msg_id = Some b3)
      (HPC: rs PC = Vptr b1 Ptrofs.zero)
      (HRA: rs RA = Vptr b2 (Ptrofs.repr 8))
      (HRDX: rs (IR RDX) = Vint (Int.repr 5))
      (HRSI: rs (IR RSI) = Vptr b3 Ptrofs.zero)
      (HRDI: rs (IR RDI) = Vint (Int.repr 1))
      (HLSP: Mem.loadv Mptr mx2 (Val.offset_ptr rs#RSP (Ptrofs.repr 0)) = Some (rs0 RSP))
      (HLRA: Mem.loadv Mptr mx2 (Val.offset_ptr rs#RSP (Ptrofs.repr 8)) = Some (rs0 RA))
      (HCALLEE: forall r, Conventions1.is_callee_save r = true -> rs (preg_of r) = rs0 (preg_of r))
      (HSG: sg = signature_main)
      (HSP: Mach.valid_blockv nb (rs0 RSP))
      (HSPB1: Plt sp_b (Mem.nextblock mx2))
      (HSPB2: ~ Plt sp_b nb)
      (HSPB: rs#RSP = Vptr sp_b Ptrofs.zero)
      (HSPB3: forall b d, jx b = Some (sp_b, d) -> False)
      (HFREE: Mem.range_perm mx2 sp_b 0 16 Cur Freeable)
      (HNB: nb = Mem.nextblock m2):
    secret_match_state (se, wi, caw sg rs0 m2)
      (secret4, mx1) (nb, State rs mx2 true)
  | secret_match_state5  rs nb se sg wi m1 m2 j Hm mx1 mx2 jx Hmx sp_b (rs0: regset) b
      (HWI: wi = injpw j m1 m2 Hm)
      (HACC: injp_acc wi (injpw jx mx1 mx2 Hmx))
      (HPC: rs PC = Vptr b (Ptrofs.repr 8))
      (HB: Genv.find_symbol se secret_main_id = Some b)
      (HSP: Mach.valid_blockv nb (rs0 RSP))
      (HLSP: Mem.loadv Mptr mx2 (Val.offset_ptr rs#RSP (Ptrofs.repr 0)) = Some (rs0 RSP))
      (HLRA: Mem.loadv Mptr mx2 (Val.offset_ptr rs#RSP (Ptrofs.repr 8)) = Some (rs0 RA))
      (HCALLEE: forall r, Conventions1.is_callee_save r = true -> rs (preg_of r) = rs0 (preg_of r))
      (HSG: sg = signature_main)
      (HSPB: rs#RSP = Vptr sp_b Ptrofs.zero)
      (HSPB1: Plt sp_b (Mem.nextblock mx2))
      (HSPB2: ~ Plt sp_b nb)
      (HSPB: rs#RSP = Vptr sp_b Ptrofs.zero)
      (HSPB3: forall b d, jx b = Some (sp_b, d) -> False)
      (HFREE: Mem.range_perm mx2 sp_b 0 16 Cur Freeable)
      (HNB: nb = Mem.nextblock m2):
    secret_match_state  (se, wi, caw sg rs0 m2)
      (secret5, mx1) (nb, State rs mx2 true)
  | secret_match_state6 rs mx1 mx2 m1 m2 j Hm jx Hmx wi nb rs0 sg se
      (HACC:injp_acc wi (injpw jx mx1 mx2 Hmx))
      (HWI: wi = injpw j m1 m2 Hm)
      (HRAX: rs (IR RAX) = Vint Int.zero)
      (HCALLEE: forall r, Conventions1.is_callee_save r = true -> rs (preg_of r) = rs0 (preg_of r))
      (HSG: sg = signature_main)
      (HPC: rs PC = rs0 RA)
      (HSP: rs RSP = rs0 RSP):
      secret_match_state  (se, wi, caw sg rs0 m2)
        (secret6, mx1) (nb, State rs mx2 false).

  Transparent Archi.ptr64.
  Hypothesis (Hwin64: Archi.win64 = false).

  Lemma secret_prog_defmap_msg:
    (prog_defmap secret_asm_program) ! secret_msg_id = Some (Gvar msg_globvar).
  Proof. reflexivity. Qed.
  Lemma secret_prog_defmap_rot13:
    (prog_defmap secret_asm_program) ! secret_rot13_id = Some (Gfun rot13).
  Proof. reflexivity. Qed.
  Lemma secret_prog_defmap_write:
    (prog_defmap secret_asm_program) ! secret_write_id = Some (Gfun write).
  Proof. reflexivity. Qed.
  Lemma msg_block se:
    Genv.valid_for (AST.erase_program secret_asm_program) se ->
    exists b, Genv.find_symbol se secret_msg_id = Some b.
  Proof.
    intros Hse.
    exploit @Genv.find_def_symbol; eauto.
    intros [H _]. specialize (H secret_prog_defmap_msg).
    destruct H as (b & Hb1 & Hb2); eauto.
  Qed.
  Lemma rot13_block se:
    Genv.valid_for (AST.erase_program secret_asm_program) se ->
    exists b, Genv.find_symbol se secret_rot13_id = Some b.
  Proof.
    intros Hse.
    exploit @Genv.find_def_symbol; eauto.
    intros [H _]. specialize (H secret_prog_defmap_rot13).
    destruct H as (b & Hb1 & Hb2); eauto.
  Qed.
  Lemma write_block se:
    Genv.valid_for (AST.erase_program secret_asm_program) se ->
    exists b, Genv.find_symbol se secret_write_id = Some b.
  Proof.
    intros Hse.
    exploit @Genv.find_def_symbol; eauto.
    intros [H _]. specialize (H secret_prog_defmap_write).
    destruct H as (b & Hb1 & Hb2); eauto.
  Qed.

  Ltac one_step := eapply star_left with (t1 := E0) (t2 := E0); [ | | reflexivity ].
  Ltac rewrite_pc :=
    match goal with
    | [ H: (_ PC) = _ |- _ ] => rewrite H
    | [ H: _ = (_ PC) |- _ ] => rewrite <- H
    end.
  Ltac asm_step :=
    instantiate (1 := (_, _)); split; eauto; eapply exec_step_internal;
    [ cbn; rewrite_pc; reflexivity
    | setoid_rewrite find_funct_spec; eauto; reflexivity
    | cbn; rewrite zeq_true by easy; repeat rewrite zeq_false by easy; reflexivity
    | ].

  Lemma main_size_arguments:
    Conventions.size_arguments signature_main = 0.
  Proof. cbn. rewrite Hwin64. reflexivity. Qed.
  Lemma rot13_size_arguments:
    Conventions.size_arguments rot13_sig = 0.
  Proof. cbn. rewrite Hwin64. reflexivity. Qed.
  Lemma write_size_arguments:
    Conventions.size_arguments write_sig = 0.
  Proof. cbn. rewrite Hwin64. reflexivity. Qed.

  Lemma no_init_args sp:
    CallConv.not_init_args 0 sp = fun (_: block) (_: Z) => True.
  Proof.
    repeat (apply Axioms.functional_extensionality; intros).
    apply PropExtensionality.propositional_extensionality.
    split; eauto. intros.
    red. intros A. inv A. lia.
  Qed.

  Lemma no_init_args_loc sp:
    Mach.loc_init_args 0 sp = fun (_: block) (_: Z) => False.
  Proof.
    repeat (apply Axioms.functional_extensionality; intros).
    apply PropExtensionality.propositional_extensionality.
    split.
    - intros. inv H. lia.
    - inversion 1.
  Qed.

  Lemma match_program_id:
    Linking.match_program (fun _ f0 tf => tf = id f0) eq secret_asm_program secret_asm_program.
  Proof.
    red. red. constructor; eauto.
    constructor. constructor. eauto. simpl. econstructor; eauto.
    apply Linking.linkorder_refl.
    constructor. constructor; eauto. cbn. econstructor; eauto.
    apply Linking.linkorder_refl.
    constructor; eauto.
    constructor; eauto. econstructor; eauto.
    apply Linking.linkorder_refl.
    repeat econstructor; eauto.
  Qed.

  Lemma loadv_unchanged_on : forall P m m' chunk b ptrofs v,
      Mem.unchanged_on P m m' ->
      (forall i, let ofs := Ptrofs.unsigned ptrofs in
            ofs <= i < ofs + size_chunk chunk -> P b i) ->
      Mem.loadv chunk m (Vptr b ptrofs) = Some v ->
      Mem.loadv chunk m' (Vptr b ptrofs) = Some v.
  Proof.
    intros. unfold Mem.loadv in *. cbn in *.
    eapply Mem.load_unchanged_on; eauto.
  Qed.

  Lemma inj_unchanged_on_right j m1 m2 m3:
    Mem.inject j m1 m2 ->
    Mem.unchanged_on (fun (_ : block) (_ : Z) => True) m2 m3 ->
    Mem.nextblock m2 = Mem.nextblock m3 ->
    Mem.inject j m1 m3.
  Proof.
    intros Hj Hu Hn. destruct Hu. destruct Hj. split; eauto.
    destruct mi_inj. split; eauto.
    (* mi_perm *)
    - intros; apply unchanged_on_perm; eauto.
    (* mi_memval *)
    - intros; rewrite unchanged_on_contents; eauto.
    (* mi_mappedblocks *)
    - intros. unfold Mem.valid_block in mi_mappedblocks |- *.
      rewrite <- Hn. eauto.
    (* mi_perm_inv *)
    - intros. eapply mi_perm_inv; eauto.
      apply unchanged_on_perm; eauto.
  Qed.

  Lemma symbol_address_inject : forall ge tge f b ofs id,
      Genv.match_stbls f ge tge ->
      Genv.symbol_address ge id  ofs = Vptr b ofs ->
      exists b' d, f b = Some (b',d) /\
                Ptrofs.add ofs (Ptrofs.repr d) = ofs /\
                Genv.symbol_address tge id ofs = Vptr b' ofs.
  Proof.
    intros.
    eapply Op.symbol_address_inject in H as H1. rewrite H0 in H1.
    inv H1. unfold Genv.symbol_address in H4.
    destruct Genv.find_symbol; try congruence.
    inv H4.
    exists b0, delta. intuition eauto.
    rewrite !H3. eauto.
    rewrite !H3. eauto.
  Qed.

  Lemma mem_unchanged_on_trans_implies_valid (P Q: block -> Z -> Prop) m m' m'':
    Mem.unchanged_on P m m' ->
    Mem.unchanged_on Q m' m'' ->
    (forall b ofs, P b ofs -> Mem.valid_block m b -> Q b ofs) ->
    Mem.unchanged_on P m m''.
  Proof.
    intros H HPQ H'.
    eapply (Mem.unchanged_on_implies (fun b o => P b o /\ Mem.valid_block m b)).
    - eapply Mem.unchanged_on_trans; eauto.
      + eapply Mem.unchanged_on_implies; eauto.
        tauto.
      + eapply Mem.unchanged_on_implies; eauto.
        firstorder.
    - eauto.
  Qed.

  Lemma secret_correct':
    forward_simulation (cc_c injp @ cc_c_asm) (cc_c injp @ cc_c_asm)
      secret_spec (semantics secret_asm_program).
  Proof.
    constructor. econstructor. reflexivity. reflexivity.
    intros. instantiate (1 := fun _ _ _ => _). cbn beta.
    eapply forward_simulation_plus with
      (match_states := fun s1 s2 => secret_match_state wB s1 s2).
    - intros * Hq Hi. cbn in *. destruct wB as [[se winjp] wca].
      destruct H as [Hse ->]. inv Hse. destruct Hq as (qx & Hq1 & Hq2).
      inv Hq1. inv Hq2. inv Hi. inv H5.
      inv HRM. 2: { pose proof main_size_arguments. extlia. }
      eexists (Mem.nextblock m3, Asm.State rs m3 true).
      pose proof match_program_id as Hmatch.
      eapply Genv.find_funct_transf in Hmatch; eauto.
      2: { inv H3. erewrite find_funct_spec; eauto. reflexivity. }
      cbn in *.
      split. split; eauto. econstructor; eauto. inv HV. congruence.
      eapply Genv.find_symbol_match in HF as (bf & Hbf1 & Hbf2); eauto.
      inv H3. rewrite Hbf1 in H10. inv H10. rewrite Ptrofs.add_zero_l in H9.
      econstructor; eauto.
    - (* final state *)
      intros * Hs Hf. inv Hf. inv Hs.
      exists (rs, mx2). split. constructor.
      exists (cr (Vint Int.zero) mx2). split.
      exists (injpw jx m mx2 Hmx). split; eauto.
      constructor; eauto. constructor; eauto.
      constructor; eauto with mem.
      (* + rewrite main_size_arguments. rewrite no_init_args. eauto. *)
      + rewrite main_size_arguments. rewrite no_init_args_loc.
        inv HACC. split. etransitivity. apply H10. reflexivity.
        inversion 1. inversion 1. apply H10.
      + rewrite main_size_arguments. rewrite no_init_args_loc. inversion 1.
    - (* at external *)
      intros * Hs Ha. inv Ha; inv Hs.
      + (* external call rot13 *)
        eexists (se, injpw j m mx2 Hmx, caw rot13_sig rs mx2), (rs, mx2).
        destruct H as (Hse1 & Hse2). inv Hse2. inv Hse1.
        repeat apply conj.
        * econstructor. rewrite_pc; eauto.
          erewrite find_funct_spec; eauto. reflexivity.
        (* match_query *)
        * eexists (cq _ _ _ _). split; econstructor; eauto; cbn; try congruence.
          (* pc injection *)
          -- rewrite_pc.
             eapply Genv.find_symbol_match in HB1 as (bf & Hbf1 & Hbf2); eauto.
             inv HACC. eapply val_inject_incr; eauto.
             econstructor. 2: rewrite Ptrofs.add_zero_l; reflexivity. congruence.
          (* args injection *)
          -- rewrite Hwin64. cbn. rewrite HRDI. rewrite HRSI.
             constructor.
             exploit @Genv.find_symbol_match; eauto.
             intros (tb & Htb1 & Htb2).
             rewrite Htb2 in HB4. inv HB4. econstructor; eauto.
             repeat constructor.
          (* match_mem *)
          -- constructor.
          (* args_removed *)
          -- constructor. unfold rot13_sig. red. cbn.
             rewrite Hwin64. reflexivity.
          (* rsp has type *)
          -- rewrite HSPB. constructor.
          (* rs has type *)
          -- rewrite HRA. constructor.
          (* valid_blockv *)
          -- rewrite HSPB. constructor. apply HSPB1.
        (* match_senv *)
        * split. 2: reflexivity. inv HACC. constructor.
          -- eapply Genv.match_stbls_incr; eauto.
             intros. specialize (H14 _ _ _ H H1) as (HA & HB).
             unfold Mem.valid_block in HA, HB. split; extlia.
          -- etransitivity; eauto. apply H11.
          -- etransitivity; eauto. apply H12.
        (* after external *)
        * intros * Hr Ha. destruct s1' as (st1 & mx).
          destruct Hr as (rx1 & (wx & Hwx & Hr1) & Hr2).
          inv Hr1. inv Hr2. inv Ha.
          exists ((Mem.nextblock m2), State rs' tm' true).
          split. split; eauto. econstructor.
          -- apply H13.
          -- rewrite H17. rewrite HSPB. cbn.
             destruct plt; eauto. exfalso. apply HSPB2. eauto.
          -- (* match_state *)
             inv Hwx. inv H1.
             rewrite rot13_size_arguments in H12. rewrite no_init_args in H12.
             rewrite rot13_size_arguments in H13. rewrite no_init_args_loc in H13.
             assert (HUN: Mem.unchanged_on (loc_out_of_reach j m) mx2 tm').
             { eapply Mem.unchanged_on_trans. eauto.
               eapply Mem.unchanged_on_implies; eauto.
               cbn. eauto. }
             assert (HFREE1: Mem.range_perm tm' sp_b 0 16 Cur Freeable).
             { red. intros. red in HFREE. inv HUN.
               eapply unchanged_on_perm; eauto.
               red. intros. exploit HSPB3; eauto. }
             assert (HINJ: Mem.inject f' mx tm').
             { eapply inj_unchanged_on_right; eauto. }
             eapply secret_match_state3 with (jx := f'); eauto; try congruence.
             (* acc *)
             ++ etransitivity; eauto. instantiate (1 := HINJ).
                constructor; eauto.
                (* injp_max_perm_decrease *)
                intros ? ? A B C. apply H9; eauto.
                apply H12; eauto.
                unfold Mem.valid_block in B |- *.
                destruct H13. extlia.
             (* load sp *)
             ++ rewrite H17. rewrite HSPB in HLSP |- *. cbn in HLSP |- *.
                rewrite Ptrofs.add_zero_l in HLSP |- *.
                rewrite Ptrofs.unsigned_repr in HLSP |- * by (cbn; lia).
                eapply Mem.load_unchanged_on. apply H12.
                intros. easy.
                eapply Mem.load_unchanged_on; eauto.
                intros. red. intros. exploit HSPB3; eauto.
             (* load ra *)
             ++ rewrite H17. rewrite HSPB in HLRA |- *. cbn in HLRA |- *.
                rewrite Ptrofs.add_zero_l in HLRA |- *.
                rewrite Ptrofs.unsigned_repr in HLRA |- * by (cbn; lia).
                eapply Mem.load_unchanged_on. apply H12.
                intros. easy.
                eapply Mem.load_unchanged_on; eauto.
                intros. red. intros. exploit HSPB3; eauto.
             (* HCALLEE *)
             ++ intros. rewrite <- HCALLEE; eauto.
             (* Plt sp_b nextblock *)
             ++ eapply Plt_Ple_trans. apply HSPB1.
                etransitivity. apply H15. apply H12.
             ++ intros. destruct (j b5) as [[sb dsb]|] eqn: Hf.
                ** apply H20 in Hf as Hf'. rewrite H1 in Hf'. inv Hf'. eauto.
                ** specialize (H21 _ _ _ Hf H1) as [A B]. eauto.
      + (* external call write *)
        eexists (se, injpw jx m mx2 Hmx, caw write_sig rs mx2), (rs, mx2).
        destruct H as (Hse1 & Hse2). inv Hse2. inv Hse1.
        repeat apply conj.
        * econstructor. rewrite_pc; eauto.
          erewrite find_funct_spec; eauto. reflexivity.
        (* match_query *)
        * eexists (cq _ _ _ mx2). split; econstructor; eauto; cbn; try congruence.
          (* pc injection *)
          -- rewrite_pc.
             eapply Genv.find_symbol_match in HB1 as (bf & Hbf1 & Hbf2); eauto.
             inv HACC. eapply val_inject_incr; eauto.
             econstructor. 2: rewrite Ptrofs.add_zero_l; reflexivity. congruence.
          (* args injection *)
          -- rewrite Hwin64. cbn. rewrite HRDI. rewrite HRSI. rewrite HRDX.
             constructor. constructor. constructor.
             exploit @Genv.find_symbol_match; eauto.
             intros (tb & Htb1 & Htb2).
             inv HACC. apply H13 in Htb1.
             rewrite Htb2 in HB4. inv HB4. econstructor; eauto.
             repeat constructor.
          (* match_mem *)
          -- constructor.
          (* args_removed *)
          -- constructor. unfold write_sig. red. cbn.
             rewrite Hwin64. reflexivity.
          (* rsp has type *)
          -- rewrite HSPB. constructor.
          (* rs has type *)
          -- rewrite HRA. constructor.
          (* valid_blockv *)
          -- rewrite HSPB. constructor. apply HSPB1.
        (* match_senv *)
        * split. 2: reflexivity. inv HACC. constructor.
          -- eapply Genv.match_stbls_incr; eauto.
             intros. specialize (H14 _ _ _ H H1) as (HA & HB).
             unfold Mem.valid_block in HA, HB. split; extlia.
          -- etransitivity; eauto. apply H11.
          -- etransitivity; eauto. apply H12.
        (* after external *)
        * intros * Hr Ha. destruct s1' as (st1 & mx).
          destruct Hr as (rx1 & (wx & Hwx & Hr1) & Hr2).
          inv Hr1. inv Hr2. inv Ha.
          exists (Mem.nextblock m2, State rs' tm' true).
          split. split; eauto. econstructor.
          -- apply H13.
          -- rewrite H17. rewrite HSPB. cbn.
             destruct plt; eauto. exfalso. apply HSPB2. eauto.
          -- (* match_state *)
             inv Hwx. inv H1.
             rewrite write_size_arguments in H12. rewrite no_init_args in H12.
             rewrite write_size_arguments in H13. rewrite no_init_args_loc in H13.
             assert (HUN: Mem.unchanged_on (loc_out_of_reach jx m) mx2 tm').
             { eapply Mem.unchanged_on_trans. eauto.
               eapply Mem.unchanged_on_implies; eauto.
               cbn. eauto. }
             assert (HFREE1: Mem.range_perm tm' sp_b 0 16 Cur Freeable).
             { red. intros. red in HFREE. inv HUN.
               eapply unchanged_on_perm; eauto.
               red. intros. exploit HSPB3; eauto. }
             assert (HINJ: Mem.inject f' mx tm').
             { eapply inj_unchanged_on_right; eauto. }
             eapply secret_match_state5 with (jx := f'); eauto; try congruence.
             (* acc *)
             ++ etransitivity; eauto. instantiate (1 := HINJ).
                constructor; eauto.
                (* injp_max_perm_decrease *)
                intros ? ? A B C. apply H9; eauto.
                apply H12; eauto.
                unfold Mem.valid_block in B |- *.
                destruct H13. extlia.
             (* load sp *)
             ++ rewrite H17. rewrite HSPB in HLSP |- *. cbn in HLSP |- *.
                rewrite Ptrofs.add_zero_l in HLSP |- *.
                rewrite Ptrofs.unsigned_repr in HLSP |- * by (cbn; lia).
                eapply Mem.load_unchanged_on. apply H12.
                intros. easy.
                eapply Mem.load_unchanged_on; eauto.
                intros. red. intros. exploit HSPB3; eauto.
             (* load ra *)
             ++ rewrite H17. rewrite HSPB in HLRA |- *. cbn in HLRA |- *.
                rewrite Ptrofs.add_zero_l in HLRA |- *.
                rewrite Ptrofs.unsigned_repr in HLRA |- * by (cbn; lia).
                eapply Mem.load_unchanged_on. apply H12.
                intros. easy.
                eapply Mem.load_unchanged_on; eauto.
                intros. red. intros. exploit HSPB3; eauto.
             (* HCALLEE *)
             ++ intros. rewrite <- HCALLEE; eauto.
             (* Plt sp_b nextblock *)
             ++ eapply Plt_Ple_trans. apply HSPB1.
                etransitivity. apply H15. apply H12.
             ++ intros. destruct (jx b) as [[sb dsb]|] eqn: Hf.
                ** apply H20 in Hf as Hf'. rewrite H1 in Hf'. inv Hf'. eauto.
                ** specialize (H21 _ _ _ Hf H1) as [A B]. eauto.
    - (* internal step *)
      intros * HS * Hs. inv HS; inv Hs.
      + (* initial state to call rot13 *)
        Ltac zero_l :=
          rewrite Ptrofs.add_zero_l;
          try rewrite Ptrofs.unsigned_repr by (cbn; lia).
        destruct H as [Hse1 <-]. inv Hse1.
        edestruct msg_block as [b1 Hb1]; eauto.
        edestruct rot13_block as [b2 Hb2]; eauto.
        eapply Genv.find_symbol_match in Hb1 as (tb_msg & B1 & B2); eauto.
        eapply Genv.find_symbol_match in Hb2 as (tb_rot13 & B3 & B4); eauto.
        assert (exists mt1 tsp, Mem.alloc m2 0 16 = Some (mt1, tsp))
          as (mt1 & tsp & HM1).
        { inv Hm3. rewrite mi_alloc_flag in HFlag.
          edestruct Mem.alloc_succeed as ((mt & tsp) & HM); eauto. }
        assert (exists mt2, Mem.store Mint64 mt1 tsp 0 (rs RSP) = Some mt2)
          as (mt2 & HM2).
        { edestruct Mem.valid_access_store as (? & ?); eauto. split.
          - cbn. intros o Ho.
            eapply Mem.perm_alloc_2 with (ofs := o) in HM1. eauto with mem.
            lia.
          - apply Z.divide_0_r. }
        assert (exists mt3, Mem.store Mint64 mt2 tsp 8 (rs RA) = Some mt3)
          as (mt3 & HM3).
        { edestruct Mem.valid_access_store as (? & ?); eauto. split.
          - cbn. intros o Ho.
            eapply Mem.perm_store_1. eauto.
            eapply Mem.perm_alloc_2 with (ofs := o) in HM1. eauto with mem.
            lia.
          - cbn. apply Z.divide_refl. }
        eexists (_, _). split.
        eapply plus_left. asm_step.
        { cbn. repeat zero_l. rewrite HM1, HM2, HM3. reflexivity. }
        2: { traceEq. }
        one_step. asm_step.
        { cbn. unfold Genv.symbol_address. rewrite B2.
          replace (Ptrofs.of_int64 Int64.zero) with Ptrofs.zero by reflexivity.
          zero_l. reflexivity. }
        one_step. asm_step. reflexivity.
        one_step. asm_step.
        { cbn. rewrite_pc.
          replace (Val.offset_ptr (Val.offset_ptr (Val.offset_ptr (Vptr b Ptrofs.zero) Ptrofs.one) Ptrofs.one) Ptrofs.one)
            with (Vptr b (Ptrofs.repr 3)) by easy. reflexivity. }
        apply star_refl.
        (* match_state *)
        assert (INJ: Mem.inject j m mt3).
        { apply Mem.fresh_block_alloc in HM1 as FRESH.
          eapply Mem.store_outside_inject. 3: eauto.
          2: { intros; inv Hm3; eauto. }
          eapply Mem.store_outside_inject. 3: eauto.
          2: { intros; inv Hm3; eauto. }
          eapply Mem.alloc_right_inject; eauto. }
        econstructor; cbn; eauto.
        * instantiate (1 := INJ). constructor; eauto with mem.
          -- unfold injp_max_perm_decrease; eauto.
          -- intros bx ofsx p A B.
             eapply Mem.perm_alloc_4. eauto.
             2: intros <-; eapply Mem.fresh_block_alloc; eauto.
             eapply Mem.perm_store_2. eauto.
             eapply Mem.perm_store_2. eauto. eauto.
          -- eapply mem_unchanged_on_trans_implies_valid
               with (Q := fun b ofs => b <> tsp).
             ++ eapply Mem.alloc_unchanged_on; eauto.
             ++ eapply Mem.unchanged_on_trans;
                  eapply Mem.store_unchanged_on; eauto.
             ++ intros. intros ->.
                apply Mem.fresh_block_alloc in HM1 as FRESH.
                congruence.
          -- intros x1 x2 d A B. congruence.
        * unfold Genv.symbol_address. rewrite B4. reflexivity.
        * zero_l.
          erewrite Mem.load_store_other; eauto.
          erewrite Mem.load_store_same; eauto. cbn. inv HSP. reflexivity.
          right. cbn. lia.
        * zero_l.
          erewrite Mem.load_store_same; eauto. cbn.
          destruct (rs RA); cbn in *; try easy.
        * intros r Hr. destruct r; cbn in *; try congruence.
        * apply Mem.valid_new_block in HM1 as FRESH.
          apply Mem.nextblock_store in HM2.
          apply Mem.nextblock_store in HM3.
          unfold Mem.valid_block in FRESH. congruence.
        * eapply Mem.fresh_block_alloc; eauto.
        * intros * Hj.
          eapply Mem.mi_mappedblocks in Hj. 2:apply Hm0.
          eapply Mem.fresh_block_alloc; eauto.
        * intros o Ho.
          eapply Mem.perm_store_1. eauto.
          eapply Mem.perm_store_1. eauto.
          eapply Mem.perm_alloc_2; eauto.
      + (* after rot13 to call write *)
        destruct H as [Hse1 <-]. inv Hse1.
        edestruct msg_block as [b1 Hb1]; eauto.
        edestruct write_block as [b2 Hb2]; eauto.
        eapply Genv.find_symbol_match in Hb1 as (tb_msg & B1 & B2); eauto.
        eapply Genv.find_symbol_match in Hb2 as (tb_write & B3 & B4); eauto.
        eexists (_, _). split.
        eapply plus_left. asm_step.
        { cbn. reflexivity. } 2: { traceEq. }
        one_step. asm_step.
        { cbn. unfold Genv.symbol_address. rewrite B2.
          replace (Ptrofs.of_int64 Int64.zero) with Ptrofs.zero by reflexivity.
          zero_l. reflexivity. }
        one_step. asm_step. reflexivity.
        one_step. asm_step.
        { cbn. rewrite_pc.
          replace (Val.offset_ptr (Val.offset_ptr (Val.offset_ptr (Vptr b (Ptrofs.repr 4)) Ptrofs.one) Ptrofs.one) Ptrofs.one)
            with (Vptr b (Ptrofs.repr 7)) by easy. reflexivity. }
        apply star_refl.
        (* match_state *)
        econstructor; cbn; eauto.
        * unfold Genv.symbol_address. rewrite B4. reflexivity.
        * intros r Hr. specialize (HCALLEE r Hr).
          destruct r; cbn in *; try congruence; try apply HCALLEE; eauto.
      + (* after write to return *)
        destruct H as [Hse1 <-]. inv Hse1.
        apply Mem.range_perm_free in HFREE as (mt & Hmt).
        assert (INJ: Mem.inject jx m mt).
        { eapply Mem.free_right_inject; eauto. }
        inv HSP.
        eexists (_, _). split.
        eapply plus_left. asm_step.
        { cbn. reflexivity. } 2: { traceEq. }
        one_step. asm_step.
        { cbn. setoid_rewrite HLRA.
          setoid_rewrite HLSP. rewrite HSPB.
          rewrite !Ptrofs.unsigned_zero. cbn.
          rewrite Hmt. reflexivity. }
        one_step. asm_step.
        { cbn. rewrite <- H. cbn.
          destruct plt; try congruence.
          reflexivity. }
        apply star_refl.
        (* match_state *)
        econstructor; cbn; eauto.
        (* injp_acc *)
        * instantiate (1 := INJ).
          inv HACC.  constructor; eauto.
          -- intros ? ? A B C. apply H12; eauto with mem.
          -- eapply mem_unchanged_on_trans_implies_valid. eauto.
             instantiate (1 := fun b ofs => loc_out_of_reach j m1 b ofs /\ b <> sp_b).
             eapply Mem.free_unchanged_on; eauto.
             intros * A (B & C). congruence.
             intros. cbn. split; eauto.
             intros X. subst b1.
             unfold Mem.valid_block in H4.
             apply HSPB2. eauto.
        (* callee_save *)
        * intros r Hr. specialize (HCALLEE r Hr).
          destruct r; cbn in *; try congruence; try apply HCALLEE; eauto.
    - easy.
  Qed.

End CODE_PROOF.

Import CallconvAlgebra CKLR CKLRAlgebra.
Import Invariant.
Import CallConv.
Import Asm VAInject Inject.

Lemma inj_injp: subcklr inj injp.
Proof.
  intros wq se1 se2 m1 m2. cbn.
  intros Hse Hm. inv Hm. inv Hse. cbn in *.
  exists (injpw f m1 m2 H). repeat apply conj.
  - constructor; eauto.
  - constructor.
  - apply inject_incr_refl.
  - intros wr' m1' m2' Hm' Hacc.
    inv Hm'. inv Hacc.
    exists (injw f0 (Mem.nextblock m1') (Mem.nextblock m2')).
    repeat apply conj.
    + constructor; eauto.
    + constructor; eauto.
      * intros * A B. specialize (H11 _ _ _ A B) as (C & D).
        split; unfold Mem.valid_block in C, D; extlia.
      * apply H8.
      * apply H9.
    + apply inject_incr_refl.
Qed.

Section NOT_WIN.
  Hypothesis (Hwin: Archi.win64 = false).

  (* This could be proved directly *)
  Lemma secret_correct'':
    forward_simulation (cc_c injp @ cc_c_asm) (cc_c Inject.inj @ cc_c_asm)
      secret_spec (semantics secret_asm_program).
  Proof.
    eapply CallconvAlgebra.open_fsim_ccref. 3: apply secret_correct'.
    reflexivity. unfold Basics.flip.
    apply CallconvAlgebra.cc_compose_ref. 2: reflexivity.
    apply CKLRAlgebra.cc_c_ref. apply inj_injp.
    eauto.
  Qed.
End NOT_WIN.

Lemma secret_spec_self_sim (R: cklr):
  forward_simulation (cc_c R) (cc_c R) secret_spec secret_spec.
Proof.
  constructor. econstructor; eauto.
  { intros i; firstorder. }
  instantiate (1 := fun _ _ _ => _). cbn beta.
  intros se1 se2 w Hse Hse1. cbn -[secret_spec] in *.
  apply forward_simulation_step
    with (match_states := fun '(s1, m1) '(s2, m2) =>
                            s1 = s2 /\ klr_diam tt (CKLR.match_mem R) w m1 m2); cbn.
  - intros * Hq Hi. inv Hq. inv Hi. inv H0. inv H.
    apply match_stbls_proj in Hse.
    edestruct @Genv.find_symbol_match as (bx & A & B); eauto.
    rewrite A in H4. inv H4.
    rewrite Ptrofs.add_zero_l.
    replace (Ptrofs.repr 0) with Ptrofs.zero by reflexivity.
    exists (secret1, m2). split. econstructor; eauto.
    split; eauto. exists w. split; eauto. reflexivity.
  - intros [s1 m1] [s2 m2] r1 [<- (wx & Hw & Hm)] Hf. inv Hf.
    eexists. split. econstructor; eauto.
    exists wx. split; eauto. constructor; eauto.
  - intros [s1 m1] [s2 m2] q1 [<- (wx & Hw & Hm)] He.
    exploit match_stbls_acc. apply Hw. apply Hse. intros SE.
    exploit match_stbls_proj. apply SE. intros HSE. inv He.
    + exploit @Genv.find_symbol_match. apply HSE. apply HB1.
      intros (tb1 & Htb1 & Htb2).
      exploit @Genv.find_symbol_match. apply HSE. apply HB2.
      intros (tb2 & Htb3 & Htn4).
      exists wx, (cq (Vptr tb1 Ptrofs.zero) rot13_sig [Vptr tb2 Ptrofs.zero; Vint (Int.repr 5)] m2).
      split. econstructor; eauto.
      split. repeat econstructor; eauto. congruence.
      split; eauto.
      intros r1 r2 [s1' m1'] (wxx & Hwx & Hr) Hf. inv Hf.
      inv Hr. exists (secret3, m2'). split. econstructor; eauto.
      split; eauto. exists wxx. split; eauto.
      etransitivity; eauto.
    + exploit @Genv.find_symbol_match. apply HSE. apply HB1.
      intros (tb1 & Htb1 & Htb2).
      exploit @Genv.find_symbol_match. apply HSE. apply HB2.
      intros (tb2 & Htb3 & Htn4).
      exists wx, (cq (Vptr tb1 Ptrofs.zero) write_sig [Vint (Int.repr 1); Vptr tb2 Ptrofs.zero; Vint (Int.repr 5)] m2).
      split. econstructor; eauto.
      split. repeat econstructor; eauto. congruence.
      split; eauto.
      intros r1 r2 [s1' m1'] (wxx & Hwx & Hr) Hf. inv Hf.
      inv Hr. exists (secret5, m2'). split. econstructor; eauto.
      split; eauto. exists wxx. split; eauto.
      etransitivity; eauto.
  - intros [s1 m1] t [s2 m2] Hstep [s1' m1'] [<- (wx & Hw & Hm)].
    inv Hstep; eexists (_, m1'); repeat split; try econstructor; eauto.
    apply cklr_alloc_flag in Hm. congruence.
  - easy.
Qed.

Lemma secret_spec_wt_lessdef:
  forward_simulation (wt_c @ lessdef_c) (wt_c @ lessdef_c)
    secret_spec secret_spec.
Proof.
  constructor. econstructor; eauto.
  { intros i; firstorder. }
  instantiate (1 := fun _ _ _ => _). cbn beta.
  intros se1 se2 w Hse Hse1. cbn -[secret_spec] in *.
  set (sg_prop := fun (w: ccworld (wt_c @ lessdef_c)) => snd (snd (fst w)) = signature_main).
  apply forward_simulation_step
    with (match_states := fun s1 s2 => sg_prop w /\ s1 = s2); cbn.
  - intros. inv H0. eprod_crush. inv H. inv H0.
    eprod_crush. inv H2. inv H7.
    eexists (_, _). split; econstructor; eauto.
    reflexivity.
  - intros. inv H0. eexists (cr (Vint Int.zero) m).
    subst sg_prop. cbn in *.
    eprod_crush. inv H0.
    repeat split; repeat econstructor; eauto.
  - intros. subst sg_prop. cbn in *. eprod_crush. inv H. inv H0.
    + eexists (_, (_, _), _), _.
      repeat apply conj; eauto; try constructor; eauto.
      * eexists. split; repeat constructor; eauto.
      * intros. inv H0. eprod_crush. inv H. inv H0.
        eexists (_, _). repeat split. econstructor; eauto.
    + eexists (_, (_, _), _), _.
      repeat apply conj; eauto; try constructor; eauto.
      * eexists. split; repeat constructor; eauto.
      * intros. inv H0. eprod_crush. inv H. inv H0.
        eexists (_, _). repeat split. econstructor; eauto.
  - intros. subst sg_prop. cbn in *. eprod_crush. inv H0. inv H.
    + eexists (_, _). repeat split; econstructor; eauto.
    + eexists (_, _). repeat split; econstructor; eauto.
    + eexists (_, _). repeat split; econstructor; eauto.
  - easy.
    Unshelve. exact tt. exact tt.
Qed.

Lemma cc_join_fsim {liA1 liA2 liB1 liB2}
  (ccA1 ccA2: callconv liA1 liA2)
  (ccB1 ccB2: callconv liB1 liB2) L1 L2:
  forward_simulation ccA1 ccB1 L1 L2 ->
  forward_simulation ccA2 ccB2 L1 L2 ->
  forward_simulation (cc_join ccA1 ccA2) (cc_join ccB1 ccB2) L1 L2.
Proof.
  intros A B.
  rewrite cc_join_l in A, B by reflexivity.
  rewrite cc_join_comm in B.
  eapply cc_join_fsim; eauto.
Qed.

Lemma cc_compcert_ref1:
  ccref cc_compcert
    (Compiler.cc_cklrs ^ {*} @ (wt_c @ lessdef_c) @ (inj @ cc_c_asm) @ (Asm.cc_asm vainj)).
Proof.
  unfold cc_compcert. rewrite ca_cllmma_equiv.
  rewrite !cc_compose_assoc.
  etransitivity.
  {
    rewrite vainj_vainj, vainj_inj, !cc_asm_compose, !cc_compose_assoc at 1.
    rewrite <- (cc_compose_assoc wt_c lessdef_c).
    do 4 rewrite (commute_around _ (R2 := _ vainj)).
    rewrite cc_star_absorb_r by eauto with cc.
    do 3 rewrite (commute_around _ (R2 := _ inj)).
    reflexivity.
  }
  rewrite !cc_compose_assoc.
  reflexivity.
Qed.

Lemma cc_compcert_ref2:
  ccref (Compiler.cc_cklrs ^ {*} @ (wt_c @ lessdef_c) @ (injp @ cc_c_asm) @ (Asm.cc_asm vainj))
    cc_compcert.
Proof.
  unfold cc_compcert.
  rewrite !cc_compose_assoc.
  rewrite <- (cc_compose_assoc wt_c lessdef_c).
  rewrite (commute_around _ (R2 := injp)).
  rewrite cc_star_absorb_r by eauto with cc.
  rewrite !cc_compose_assoc.
  reflexivity.
Qed.

Section NOT_WIN.
  Hypothesis (Hwin: Archi.win64 = false).
  Lemma secret_correct:
    forward_simulation cc_compcert cc_compcert secret_spec
      (Asm.semantics secret_asm_program).
  Proof.
    (* why rewrite not work here? *)
    eapply open_fsim_ccref. apply cc_compcert_ref2. apply cc_compcert_ref1.
    eapply compose_forward_simulations.
    apply cc_star_fsim.
    repeat apply cc_join_fsim; try apply secret_spec_self_sim.
    eapply compose_forward_simulations.
    apply secret_spec_wt_lessdef.
    eapply compose_forward_simulations.
    apply secret_correct''. apply Hwin.
    apply Asmrel.semantics_asm_rel.
  Qed.
End NOT_WIN.
