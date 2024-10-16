(* TODO: cleanup imports *)
Require Import Coqlib Integers.

Require Import Events LanguageInterface Smallstep Globalenvs Values Memory.
Require Import AST Ctypes Clight.
Require Import Lifting Encapsulation.

Require Import List Maps.
Import ListNotations.
Require Import Conventions Mach Asm.

Require Import Locations CallConv.
Require Import Compiler.

(* Conventions.cc_c_locset @ cc_locset_mach @ cc_mach_asm *)

Section CA.

  Record cc_ca_world :=
    caw {
        caw_sg : signature;
        caw_rs : regset;
        caw_m : mem
      }.

  Definition make_locset_rs (rs: regset) (m:mem) (sp: val) (l:loc):=
    match l with
    |R r => rs (preg_of r)
    |S Outgoing ofs ty =>
       let v := load_stack m sp ty (Ptrofs.repr (Stacklayout.fe_ofs_arg + 4 * ofs)) in Val.maketotal v
    |_ => Vundef
    end.

  Inductive cc_c_asm_mq : cc_ca_world -> c_query -> query li_asm -> Prop:=
    cc_c_asm_mq_intro sg args m (rs: regset) tm (ls : Locmap.t) sp ra vf
      (HSP: sp = rs#SP)
      (HRA: ra = rs#RA)
      (HVF: vf = rs#PC)
      (HARGS: args = (map (fun p => Locmap.getpair p ls) (loc_arguments sg)))
      (HLS: ls = make_locset_rs rs tm sp)
      (HRM: args_removed sg sp tm m)
      (HSPT: Val.has_type sp Tptr)
      (HRAT: Val.has_type ra Tptr)
      (HV: valid_blockv (Mem.nextblock tm) sp)
      (HDVF: vf <> Vundef)
      (HDRA: ra <> Vundef):
      cc_c_asm_mq
        (caw sg rs tm)
        (cq vf sg args m)
        (rs,tm).

  Definition rs_getpair (p: rpair preg) (rs : regset) :=
    match p with
    |One r => rs r
    |Twolong r1 r2 => Val.longofwords (rs r1) (rs r2)
    end.

  Inductive cc_c_asm_mr : cc_ca_world -> c_reply -> reply li_asm -> Prop :=
    cc_c_asm_mr_intro sg res tm m' tm' (rs rs' :regset) :
      let sp := rs#SP in
      res = rs_getpair (map_rpair preg_of (loc_result sg)) rs' ->
      (forall r, is_callee_save r = true -> rs' (preg_of r) = rs (preg_of r)) ->
      Mem.unchanged_on (not_init_args (size_arguments sg) sp) m' tm' ->
      Mem.unchanged_on (loc_init_args (size_arguments sg) sp) tm tm' ->
      Mem.nextblock m' = Mem.nextblock tm' ->
      (forall b ofs k p, loc_init_args (size_arguments sg) sp b ofs ->
                    ~ Mem.perm m' b ofs k p) ->
      rs'#SP = rs#SP -> rs'#PC = rs#RA ->
      cc_c_asm_mr
        (caw sg rs tm)
        (cr res m')
        (rs', tm').

  Program Definition cc_c_asm : callconv li_c li_asm :=
    {|
      match_senv _ := eq;
      match_query := cc_c_asm_mq;
      match_reply := cc_c_asm_mr
    |}.
  Next Obligation. reflexivity. Qed.
  Next Obligation. inv H0. cbn. reflexivity. Qed.
  Next Obligation. inv H. cbn. reflexivity. Qed.

  Definition rs_to_mrs (rs : regset) := fun r: mreg => rs (preg_of r).

  Require Import CallconvAlgebra.

  Lemma cc_ca_cllmma :
    ccref (cc_c_asm) (cc_c_locset @ cc_locset_mach @ cc_mach_asm).
  Proof.
    intros [sg rs tm] se1 se2 q1 q2 Hse. destruct Hse.
    intros Hq. inversion Hq. subst sg0 rs0 tm0 q1 q2.
    exists (se1,sg,(se1,(lmw sg (rs_to_mrs rs) tm sp),
                (rs,Mem.nextblock tm))).
    repeat apply conj; cbn in *; eauto.
    - exists (lq vf sg ls m). split.
      econstructor; eauto.
      exists (mq vf sp ra (rs_to_mrs rs) tm). split; subst.
      econstructor; eauto.
      econstructor; eauto.
    - intros cr ar [lr [Hr1 [mr [Hr2 Hr3]]]].
      inv Hr1. inv Hr2. inv Hr3.
      econstructor; eauto.
      + destruct (loc_result sg).
        -- simpl. rewrite <- H7. rewrite H5. reflexivity. simpl. auto.
        -- simpl. f_equal.
           rewrite <- H7. rewrite H5. reflexivity. simpl. eauto.
           rewrite <- H7. rewrite H5. reflexivity. simpl. eauto.
      + intros. rewrite <- H7. rewrite H6. reflexivity. eauto.
  Qed.

  Lemma cc_cllmma_ca :
    ccref (cc_c_locset @ cc_locset_mach @ cc_mach_asm) (cc_c_asm).
  Proof.
    intros [[se' sg] [[se'' w2] [rs tm]]] se''' se q1 q2 Hse Hq.
    destruct Hse. inv H. destruct H0. inv H. inv H0.
    destruct Hq as [lq [Hq1 [mq [Hq2 Hq3]]]]. cbn in *.
    inv Hq1. inv Hq2. inv Hq3.
    rename rs1 into mrs. rename m0 into tm.
    exists (caw sg rs tm).
    repeat apply conj; eauto.
    - econstructor; eauto.
      apply Axioms.extensionality.
      intro r. destruct r; simpl; eauto.
    - intros r1 r2 Hr. inv Hr.
      set (ls' loc :=
             match loc with
             |R r => rs' (preg_of r)
             |_ => Vundef
             end
          ).
      exists (lr ls'  m'). split.
      constructor; eauto.
      destruct (loc_result); simpl; eauto.
      exists (mr (rs_to_mrs rs') tm'). split.
      constructor; eauto.
      intros. unfold rs_to_mrs. rewrite H3. eauto. eauto.
      constructor; eauto.
      inversion H8. eauto.
  Qed.

  Lemma ca_cllmma_equiv :
    cceqv cc_c_asm (cc_c_locset @ cc_locset_mach @ cc_mach_asm).
  Proof. split. apply cc_ca_cllmma. apply cc_cllmma_ca. Qed.

End CA.

Definition cc_compcert : callconv li_c li_asm :=
  cc_cklrs^{*} @ Invariant.cc_inv Invariant.wt_c @ lessdef_c @ cc_c_asm @ cc_asm VAInject.vainj.
