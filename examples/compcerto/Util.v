Require Import LanguageInterface Smallstep CallconvAlgebra.
Require Import Compiler CallConv Asmrel.
Require Import Clight.
Require Import  Linking.
Require Import Coqlib.

Ltac eprod_crush :=
  repeat
    (match goal with
     | [ H: ?a * ?b |- _ ] => destruct H;cbn [fst snd] in *; subst
     | [ H: (?a, ?b) = (?c, ?d) |- _ ] => inv H
     | [ H: (?x * ?y)%rel _ _ |- _] => destruct H; cbn [fst snd] in *; subst
     | [ H: ?x /\ ?y |- _] => destruct H
     | [ H: (exists _, _) |- _] => destruct H
     | [ H: unit |- _] => destruct H
     end).

Local Open Scope linking_scope.

Definition CompCertO's_passes :=
  mkpass Cshmgenproof.match_prog
  ::: mkpass Cminorgenproof.match_prog
  ::: mkpass Selectionproof.match_prog
  ::: mkpass RTLgenproof.match_prog
  ::: mkpass (match_if Compopts.optim_tailcalls Tailcallproof.match_prog)
  ::: mkpass Inliningproof.match_prog
  ::: mkpass Renumberproof.match_prog
  ::: mkpass (match_if Compopts.optim_constprop Constpropproof.match_prog)
  ::: mkpass (match_if Compopts.optim_constprop Renumberproof.match_prog)
  ::: mkpass (match_if Compopts.optim_CSE CSEproof.match_prog)
  ::: mkpass (match_if Compopts.optim_redundancy Deadcodeproof.match_prog)
  ::: mkpass Allocproof.match_prog
  ::: mkpass Tunnelingproof.match_prog
  ::: mkpass Linearizeproof.match_prog
  ::: mkpass CleanupLabelsproof.match_prog
  ::: mkpass (match_if Compopts.debug Debugvarproof.match_prog)
  ::: mkpass Stackingproof.match_prog
  ::: mkpass Asmgenproof.match_prog
  ::: pass_nil _.

(** Composing the [match_prog] relations above, we obtain the relation
  between CompCert C sources and Asm code that characterize CompCert's
  compilation. *)

Definition match_prog: Clight.program -> Asm.program -> Prop :=
  pass_match (compose_passes CompCertO's_passes).

Section COMPOSE_C_PASSES.

Context {li} (ccA ccB: callconv li_c li).

Lemma compose_clight_properties prog tsem:
  forward_simulation (cc_dom @ ccA) (cc_cod @ ccB) (Clight.semantics2 prog) tsem ->
  forward_simulation (cc_dom @ ccA) (cc_dom @ ccB) (Clight.semantics2 prog) tsem.
Proof.
  unfold cc_dom. intro.
  rewrite <- cc_star_idemp at 1.
  rewrite !cc_compose_assoc at 1.
  rewrite !cc_compose_assoc in H.
  eapply compose_forward_simulations; eauto.
  eapply cc_star_fsim.
  repeat eapply cc_join_fsim;
    (eapply open_fsim_ccref;
     [ | reflexivity | eapply Clightrel.semantics2_rel];
     eauto with cc).
Qed.

End COMPOSE_C_PASSES.

Lemma clight2_semantic_preservation':
  forall p tp,
  match_prog p tp ->
  forward_simulation cc_compcert cc_compcert (Clight.semantics2 p) (Asm.semantics tp).
Proof.
  intros p tp M. unfold match_prog, pass_match in M; simpl in M.
Ltac DestructM :=
  match goal with
    [ H: exists p, _ /\ _ |- _ ] =>
      let p := fresh "p" in let M := fresh "M" in let MM := fresh "MM" in
      destruct H as (p & M & MM); clear H
  end.
  repeat DestructM. subst tp.
  rewrite cc_compcert_expand at 2.
  rewrite <- cc_compcert_collapse at 1.
  eapply compose_clight_properties.
  (* eapply compose_injection_pass. *)
  (*   eapply SimplLocalsproof.transf_program_correct; eassumption. *)
  eapply compose_identity_pass.
    eapply Cshmgenproof.transl_program_correct; eassumption.
  eapply compose_injection_pass.
    eapply Cminorgenproof.transl_program_correct; eassumption.
  eapply compose_selection_pass.
    eapply Selectionproof.transf_program_correct; eassumption.
  eapply compose_extension_pass.
    eapply RTLgenproof.transf_program_correct; eassumption.
  eapply compose_optional_pass; eauto using compose_extension_pass.
    exact Tailcallproof.transf_program_correct.
  eapply compose_injection_pass.
    eapply Inliningproof.transf_program_correct; eassumption.
  eapply compose_identity_pass.
    eapply Renumberproof.transf_program_correct; eassumption.
  eapply compose_optional_pass; eauto using compose_va_pass.
    exact Constpropproof.transf_program_correct.
  eapply compose_optional_pass; eauto using compose_identity_pass.
    exact Renumberproof.transf_program_correct.
  eapply compose_optional_pass; eauto using compose_va_pass.
    exact CSEproof.transf_program_correct.
  eapply compose_optional_pass; eauto using compose_va_pass.
    exact Deadcodeproof.transf_program_correct; eauto.
  eapply compose_backend_passes; eauto using Allocproof.wt_prog.
  eapply compose_forward_simulations.
    eapply Allocproof.transf_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply Tunnelingproof.transf_program_correct; eassumption.
  eapply compose_identity_pass.
    eapply Linearizeproof.transf_program_correct; eassumption.
  eapply compose_identity_pass.
    eapply CleanupLabelsproof.transf_program_correct; eassumption.
  eapply compose_optional_pass; eauto using compose_identity_pass.
    exact Debugvarproof.transf_program_correct.
  eapply compose_forward_simulations.
    rewrite <- cc_stacking_lm, cc_lm_stacking.
    eapply Stackingproof.transf_program_correct with (rao := Asmgenproof0.return_address_offset).
    exact Asmgenproof.return_address_exists.
    eassumption.
  eapply compose_forward_simulations.
    eapply Asmgenproof.transf_program_correct; eassumption.
  apply semantics_asm_rel.
Qed.

Require Import CAsm.

Lemma cc_compcert_equiv:
  cceqv cc_compcert Compiler.cc_compcert.
Proof.
  unfold cc_compcert, Compiler.cc_compcert.
  rewrite ca_cllmma_equiv. rewrite !cc_compose_assoc. reflexivity.
Qed.

Lemma clight2_semantic_preservation:
  forall p tp,
  match_prog p tp ->
  forward_simulation cc_compcert cc_compcert (Clight.semantics2 p) (Asm.semantics tp).
Proof.
  intros.
  eapply open_fsim_ccref. 3: apply clight2_semantic_preservation'; eauto.
  1-2: apply cc_compcert_equiv.
Qed.

Require Import Errors.
Require Import String.
Require Import Compopts.
Local Open Scope string_scope.

Definition transf_clight_program (p: Clight.program) : res Asm.program :=
  OK p
  !@@ print print_Clight
  @@@ time "C#minor generation" Cshmgen.transl_program
  @@@ time "Cminor generation" Cminorgen.transl_program
  @@@ transf_cminor_program.

Theorem transf_clight_program_match:
  forall p tp,
  transf_clight_program p = OK tp ->
  match_prog p tp.
Proof.
  intros p1 tp T.
  unfold transf_clight_program, time in T. rewrite ! compose_print_identity in T. simpl in T.
  destruct (Cshmgen.transl_program p1) as [p3|e] eqn:P3; simpl in T; try discriminate.
  destruct (Cminorgen.transl_program p3) as [p4|e] eqn:P4; simpl in T; try discriminate.
  unfold transf_cminor_program, time in T. rewrite ! compose_print_identity in T. simpl in T.
  destruct (Selection.sel_program p4) as [p5|e] eqn:P5; simpl in T; try discriminate.
  destruct (RTLgen.transl_program p5) as [p6|e] eqn:P6; simpl in T; try discriminate.
  unfold transf_rtl_program, time in T. rewrite ! compose_print_identity in T. simpl in T.
  set (p7 := total_if optim_tailcalls Tailcall.transf_program p6) in *.
  destruct (Inlining.transf_program p7) as [p8|e] eqn:P8; simpl in T; try discriminate.
  set (p9 := Renumber.transf_program p8) in *.
  set (p10 := total_if optim_constprop Constprop.transf_program p9) in *.
  set (p11 := total_if optim_constprop Renumber.transf_program p10) in *.
  destruct (partial_if optim_CSE CSE.transf_program p11) as [p12|e] eqn:P12; simpl in T; try discriminate.
  destruct (partial_if optim_redundancy Deadcode.transf_program p12) as [p13|e] eqn:P13; simpl in T; try discriminate.
  destruct (Allocation.transf_program p13) as [p15|e] eqn:P15; simpl in T; try discriminate.
  set (p16 := Tunneling.tunnel_program p15) in *.
  destruct (Linearize.transf_program p16) as [p17|e] eqn:P17; simpl in T; try discriminate.
  set (p18 := CleanupLabels.transf_program p17) in *.
  destruct (partial_if debug Debugvar.transf_program p18) as [p19|e] eqn:P19; simpl in T; try discriminate.
  destruct (Stacking.transf_program p19) as [p20|e] eqn:P20; simpl in T; try discriminate.
  unfold match_prog; simpl.
  exists p3; split. apply Cshmgenproof.transf_program_match; auto.
  exists p4; split. apply Cminorgenproof.transf_program_match; auto.
  exists p5; split. apply Selectionproof.transf_program_match; auto.
  exists p6; split. apply RTLgenproof.transf_program_match; auto.
  exists p7; split. apply total_if_match. apply Tailcallproof.transf_program_match.
  exists p8; split. apply Inliningproof.transf_program_match; auto.
  exists p9; split. apply Renumberproof.transf_program_match; auto.
  exists p10; split. apply total_if_match. apply Constpropproof.transf_program_match.
  exists p11; split. apply total_if_match. apply Renumberproof.transf_program_match.
  exists p12; split. eapply partial_if_match; eauto. apply CSEproof.transf_program_match.
  exists p13; split. eapply partial_if_match; eauto. apply Deadcodeproof.transf_program_match.
  exists p15; split. apply Allocproof.transf_program_match; auto.
  exists p16; split. apply Tunnelingproof.transf_program_match.
  exists p17; split. apply Linearizeproof.transf_program_match; auto.
  exists p18; split. apply CleanupLabelsproof.transf_program_match; auto.
  exists p19; split. eapply partial_if_match; eauto. apply Debugvarproof.transf_program_match.
  exists p20; split. apply Stackingproof.transf_program_match; auto.
  exists tp; split. apply Asmgenproof.transf_program_match; auto.
  reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(** ** Find_funct utilities, used in Rot13 example *)

Require Import AST Ctypes.

Notation tvoid := (Tvoid).
Notation tint := (Tint I32 Unsigned noattr).
Notation tchar := (Tint I8 Unsigned noattr).
Notation tlong := (Tlong Unsigned noattr).
Notation tptr := (fun ty => Tpointer ty noattr).
Notation tarray := (fun ty size => Tarray ty size noattr).

Definition rw_parameters := Tcons tint (Tcons (tptr tchar) (Tcons tint Tnil)).
Definition rw_type :=
  Tfunction rw_parameters tint cc_default.
Definition rw_sig : signature :=
  signature_of_type rw_parameters tint cc_default.
Definition write : Clight.fundef :=
  External (EF_external "write" rw_sig) rw_parameters tint cc_default.
Definition read : Clight.fundef :=
  External (EF_external "read" rw_sig) rw_parameters tint cc_default.
Definition read_asm : Asm.fundef := AST.External (EF_external "read" rw_sig).
Definition write_asm : Asm.fundef := AST.External (EF_external "write" rw_sig).
Definition main_sig := signature_of_type Tnil tint cc_default.

Require Load.

Section FIND_FUNCT.
  Import Coqlib Linking AST Clight Values.

  Lemma compcert_match_program_gen p tp:
    match_prog p tp ->
    exists (C: Type) (LC: Linker C) (c: C) mf mv,
      match_program_gen mf mv c p tp /\
      forall x t def params ret cc, mf x (Ctypes.External def params ret cc) t ->
                               t = AST.External def.
  Proof.
    intros H. cbn in *. eprod_crush. subst.
    repeat match goal with
    | [ H: match_if _ ?m _ _ |- _] => unfold match_if, m in H; rewrite Load.if_commute in H
    end.
    (* destruct H as (A & A1). red in A.  *)
    pose proof (Load.match_program_gen_compose H H0) as B. clear H H0.
    pose proof (Load.match_program_gen_compose B H1) as C. clear B H1.
    pose proof (Load.match_program_gen_compose C H2) as D. clear C H2.
    pose proof (Load.match_program_gen_compose_match_if D H3) as E. clear D H3.
    pose proof (Load.match_program_gen_compose E H4) as F. clear E H4.
    pose proof (Load.match_program_gen_compose F H5) as G. clear F H5.
    pose proof (Load.match_program_gen_compose_match_if G H6) as H. clear G H6.
    pose proof (Load.match_program_gen_compose_match_if H H7) as I. clear H H7.
    pose proof (Load.match_program_gen_compose_match_if I H8) as J. clear I H8.
    pose proof (Load.match_program_gen_compose_match_if J H9) as K. clear J H9.
    pose proof (Load.match_program_gen_compose K H10) as L. clear K H10.
    pose proof (Load.match_program_gen_compose L H11) as M. clear L H11.
    pose proof (Load.match_program_gen_compose M H12) as N. clear M H12.
    pose proof (Load.match_program_gen_compose N H13) as O. clear N H13.
    pose proof (Load.match_program_gen_compose_match_if O H14) as P. clear O H14.
    pose proof (Load.match_program_gen_compose P H15) as Q. clear P H15.
    pose proof (Load.match_program_gen_compose Q H16) as R. clear Q H16.

    match goal with
    | [ H: @match_program_gen ?C ?F1 ?V1 ?F2 ?V2 ?LC ?mf ?mv ?c ?p1 ?p2 |- _ ] =>
        exists C, LC, c, mf, mv
    end.
    split; eauto.
    intros c t * Hx.
    repeat match goal with
           | [ H: Load.compose_match_fundef _ _ _ _ _ |- _ ] => inv H
           end.
    (* clear S. *)
    repeat match goal with
    | [ H: (if ?x then _ else _) _ _ _ |- _ ] => destruct x; subst
    end.
    all: repeat match goal with
    | [H: SimplLocals.transf_fundef _ = Errors.OK _ |- _] => inv H
    | [H: Cshmgenproof.match_fundef _ _ _ |- _ ] => inv H
    | [H: Cminorgen.transl_fundef _ = Errors.OK _ |- _] => inv H
    | [H: Selectionproof.match_fundef _ _ _ |- _ ] =>
        let H1 := fresh "H" in
        destruct H as (? & ? & H1); inv H1
    | [H: RTLgen.transl_fundef _ = Errors.OK _ |- _] => inv H
    | [H: Inlining.transf_fundef _ _ = Errors.OK _ |- _] => inv H
    | [H: CSE.transf_fundef _ _ = Errors.OK _ |- _] => inv H
    | [H: Deadcode.transf_fundef _ _ = Errors.OK _ |- _] => inv H
    | [H: Allocation.transf_fundef _ = Errors.OK _ |- _] => inv H
    | [H: Linearize.transf_fundef _ = Errors.OK _ |- _] => inv H
    | [H: Debugvar.transf_fundef _ = Errors.OK _ |- _] => inv H
    | [H: Renumber.transf_fundef _ = Errors.OK _ |- _] => inv H
    | [H: Stacking.transf_fundef _ = Errors.OK _ |- _] => inv H
    | [H: Asmgen.transf_fundef _ = Errors.OK _ |- _] => inv H
           end.
    all: reflexivity.
  Qed.

  Lemma match_prog_read p tp f se tse vf tvf:
    match_prog p tp ->
    Genv.match_stbls f se tse ->
    Val.inject f vf tvf ->
    Genv.find_funct (Clight.globalenv se p) vf = Some read ->
    Genv.find_funct (Genv.globalenv tse tp) tvf = Some read_asm.
  Proof.
    intros HP HS HI HF.
    eapply compcert_match_program_gen in HP
        as (C & LC & c & mf & mv & H & HX); eauto.
    eapply Genv.find_funct_match in H as (c0 & tfd & HW & HY & HZ); eauto.
    rewrite HW. f_equal. eapply HX; eauto.
  Qed.

  Lemma match_prog_write p tp f se tse vf tvf:
    match_prog p tp ->
    Genv.match_stbls f se tse ->
    Val.inject f vf tvf ->
    Genv.find_funct (Clight.globalenv se p) vf = Some write ->
    Genv.find_funct (Genv.globalenv tse tp) tvf = Some write_asm.
  Proof.
    intros HP HS HI HF.
    eapply compcert_match_program_gen in HP
        as (C & LC & c & mf & mv & H & HX); eauto.
    eapply Genv.find_funct_match in H as (c0 & tfd & HW & HY & HZ); eauto.
    rewrite HW. f_equal. eapply HX; eauto.
  Qed.

  Import CallconvAlgebra CKLR Compiler Inject.

  Lemma ca_find_funct_read p tp i se1 se2 se3 vf1 vf2 vf3 wn:
    Util.match_prog p tp ->
    match_senv (cc_cklrs ^ {*}) wn se1 se2 ->
    Load.mv_cklrs wn vf1 vf2 ->
    inj_stbls i se2 se3 ->
    Val.inject i vf2 vf3 ->
    Genv.find_funct (Clight.globalenv se1 p) vf1 = Some read ->
    Genv.find_funct (Genv.globalenv se3 tp) vf3 = Some read_asm.
  Proof.
    intros HMP HSE HVF HI HVF2 HF.
    eapply Load.cklrs_find_funct in HF. 2, 3: eauto. clear HSE HVF.
    eapply match_prog_read; eauto. apply HI. apply HF.
  Qed.

  Lemma ca_find_funct_write p tp i se1 se2 se3 vf1 vf2 vf3 wn:
    Util.match_prog p tp ->
    match_senv (cc_cklrs ^ {*}) wn se1 se2 ->
    Load.mv_cklrs wn vf1 vf2 ->
    inj_stbls i se2 se3 ->
    Val.inject i vf2 vf3 ->
    Genv.find_funct (Clight.globalenv se1 p) vf1 = Some write ->
    Genv.find_funct (Genv.globalenv se3 tp) vf3 = Some write_asm.
  Proof.
    intros HMP HSE HVF HI HVF2 HF.
    eapply Load.cklrs_find_funct in HF. 2, 3: eauto. clear HSE HVF.
    eapply match_prog_write; eauto. apply HI. apply HF.
  Qed.

End FIND_FUNCT.

(* ----------------------------------------------------------------- *)
(** ** Some more process example utilities *)

Ltac destruct_or H :=
  match type of H with
  | _ \/ _ => destruct H as [H|H]; [ |destruct_or H]
  | _ => idtac
  end.

Section FUNCT_SYMBOL.
Import Maps Values Integers.
Lemma genv_funct_symbol se id b f (p: Clight.program):
  Genv.find_symbol se id = Some b ->
  (prog_defmap p) ! id = Some (Gfun f) ->
  Genv.find_funct (globalenv se p) (Vptr b Ptrofs.zero) = Some f.
Proof.
  intros H1 H2.
  unfold Genv.find_funct, Genv.find_funct_ptr.
  destruct Ptrofs.eq_dec; try congruence.
  apply Genv.find_invert_symbol in H1. cbn.
  rewrite Genv.find_def_spec. rewrite H1.
  rewrite H2. reflexivity.
Qed.
End FUNCT_SYMBOL.

Section NTH.
  Import Memory Maps Values Integers.
  Inductive nth {A}: list A -> nat -> A -> Prop :=
  | nth_this a l: nth (a :: l) 0%nat a
  | nth_next a b n l:
    nth l n b -> nth (a :: l) (Datatypes.S n) b.

  Open Scope Z_scope.
  Local Transparent Mem.loadbytes Mem.load Mem.store.

Lemma getN_nth' len start i bytes byte memvals:
  Mem.getN len start memvals = map Byte bytes ->
  (0 <= i < len)%nat ->
  nth bytes i byte ->
  ZMap.get (start + (Z.of_nat i)) memvals = Byte byte.
Proof.
  (* TODO: cleanup *)
  revert start len i byte memvals. induction bytes.
  - intros. inv H1.
  - intros. inv H1.
    + cbn. destruct len. lia. cbn in H. inv H.
      rewrite Z.add_0_r. reflexivity.
    + cbn. destruct len. lia. cbn in H. inv H.
      exploit IHbytes. 1,3: eauto. lia.
      intros Hx.
      assert (Z.pos (Pos.of_succ_nat n) = 1 + Z.of_nat n). lia.
      rewrite H. rewrite Z.add_assoc. apply Hx.
Qed.

Lemma getN_nth len i bytes byte memvals:
  Mem.getN len 0 memvals = map Byte bytes ->
  (i < len)%nat ->
  nth bytes i byte ->
  ZMap.get (Z.of_nat i) memvals = Byte byte.
Proof. intros. exploit getN_nth'; eauto. lia. Qed.

Lemma loadbyte' m b bytes i len byte:
  Mem.loadbytes m b 0 len = Some (map Byte bytes) ->
  0 <= i < len ->
  nth bytes (Z.to_nat i) byte ->
  Mem.load Mint8unsigned m b i = Some (Vint (Int.repr (Byte.unsigned byte))).
Proof.
  intros H Hi Hb. unfold Mem.loadbytes in H. unfold Mem.load.
  destruct Mem.range_perm_dec eqn: Hp; try congruence. clear Hp.
  destruct Mem.valid_access_dec.
  2: { exfalso. apply n. unfold Mem.valid_access. split; cbn.
       - intros x Hx. apply r. lia.
       - apply Z.divide_1_l. }
  inv H. f_equal. cbn. change (Pos.to_nat 1) with 1%nat.
  unfold Mem.getN.
  exploit getN_nth. 1,3: eauto. lia. intros A.
  rewrite Z_to_nat_max in A. rewrite Z.max_l in A. 2: lia. rewrite A. cbn.
  f_equal. unfold Int.zero_ext.
  rewrite Zbits.Zzero_ext_mod. 2: lia.
  pose proof (Byte.unsigned_range_2 byte) as Hx; cbn in Hx.
  rewrite Int.unsigned_repr.
  2: { unfold decode_int, rev_if_be. destruct Archi.big_endian; cbn; lia. }
  change (two_p 8) with 256.
  f_equal. rewrite Z.mod_small.
  unfold decode_int, rev_if_be. destruct Archi.big_endian; cbn; lia.
  unfold decode_int, rev_if_be. destruct Archi.big_endian; cbn; lia.
Qed.

End NTH.

Import Maps.
Ltac prove_norepet H :=
  match type of H with
  | False => inversion H
  | (?a = ?b) \/ _ =>
      destruct H as [H|H]; [inversion H|prove_norepet H]
  end.

Ltac solve_list_norepet :=
  simpl;
  match goal with
  | |- list_norepet nil =>  apply list_norepet_nil
  | |- list_norepet (?x :: ?l) =>
      apply list_norepet_cons;
      [simpl; let H := fresh "H" in intro H; prove_norepet H |solve_list_norepet]
  end.

Ltac solve_list_disjoint :=
  simpl; unfold list_disjoint; simpl; red;
  let x := fresh "x" in
  let y := fresh "y" in
  let Lx := fresh "Lx" in
  let Ly := fresh "Ly" in
  let xyEq := fresh "xyEq" in
  intros x y Lx Ly xyEq; try rewrite xyEq in *; clear xyEq;
  destruct_or Lx; destruct_or Ly; subst; try solve [inversion Lx]; try solve [inversion Ly].

Ltac ptree_tac :=
  cbn -[PTree.get];
  lazymatch goal with
  | [ |- PTree.get ?x (PTree.set ?x _ _) = _ ] =>
      rewrite PTree.gss; reflexivity
  | [ |- PTree.get ?x (PTree.set ?y _ _) = _ ] =>
      rewrite PTree.gso by (unfold x, y; lia); eauto; ptree_tac
  end.

Ltac solve_ptree := solve [ eauto | ptree_tac ].

Ltac crush_eval_expr :=
  cbn;
  lazymatch goal with
  | [ |- eval_expr _ _ _ _ (Etempvar _ _) _ ] =>
      apply eval_Etempvar; try solve [ reflexivity | eassumption | solve_ptree ]
  | [ |- eval_expr _ _ _ _ (Econst_int _ _) _ ] => apply eval_Econst_int
  | [ |- eval_expr _ _ _ _ (Econst_long _ _) _ ] => apply eval_Econst_long
  | [ |- eval_expr _ _ _ _ (Ebinop _ _ _ _) _ ] => eapply eval_Ebinop
  | [ |- eval_expr _ _ _ _ (Evar _ _) _ ] => eapply eval_Elvalue
  | [ |- eval_expr _ _ _ _ (Ederef _ _) _ ] => eapply eval_Elvalue
  | [ |- eval_expr _ _ _ _ (Eaddrof _ _) _ ] => eapply eval_Eaddrof
  | [ |- eval_expr _ _ _ _ (Esizeof _ _) _ ] => eapply eval_Esizeof
  end.
Ltac crush_eval_lvalue :=
  cbn;
  lazymatch goal with
  | [ |- eval_lvalue _ _ _ _ (Evar _ _) _ _ _ ] =>
      solve [ apply eval_Evar_local; reflexivity
            | apply eval_Evar_global; [ reflexivity | eassumption ] ]
  | _ => constructor
  end.
Ltac crush_deref :=
  cbn;
  lazymatch goal with
  | [ |- deref_loc (Tarray _ _ _) _ _ _ _ _] => eapply deref_loc_reference; reflexivity
  | [ |- deref_loc (Tfunction _ _ _) _ _ _ _ _] => eapply deref_loc_reference; reflexivity
  | [ |- deref_loc (Tint _ _ _) _ _ _ _ _] => eapply deref_loc_value; [ reflexivity | ]
  end.

Ltac crush_expr :=
  repeat (cbn;
    match goal with
    | [ |- eval_expr _ _ _ _ _ _ ] => crush_eval_expr
    | [ |- eval_lvalue _ _ _ _ _ _ _ _ ] => crush_eval_lvalue
    | [ |- eval_exprlist _ _ _ _ _ _ _ ] => econstructor
    | [ |- deref_loc _ _ _ _ _ _ ] => crush_deref
    | [ |- Cop.sem_binary_operation _ _ _ _ _ _ _ = Some _] => try reflexivity
    | [ |- Cop.sem_cast _ ?ty ?ty _ = Some _ ] =>
        apply Cop.cast_val_casted; eauto
    | [ |- assign_loc _ (Tint _ _ _) _ _ _ _ _ _ ] =>
        eapply assign_loc_value; [ reflexivity | ]
    | _ => try solve [ easy | eassumption ]
    end).

Ltac crush_step := cbn;
  match goal with
  | [ |- Step _ (Callstate _ _ _ _) _ _ ] =>
      eapply step_internal_function;
      [ eauto | econstructor; cbn
        (* [ solve_list_norepet *)
        (* | solve_list_norepet *)
        (* | solve_list_disjoint *)
        (* | repeat (econstructor; simpl; auto) *)
        (* | reflexivity | eauto ] *) ]
  | [ |- Step _ (State _ (Ssequence _ _) _ _ _ _) _ _ ] => apply step_seq
  | [ |- Step _ (State _ (Sassign _ _) _ _ _ _) _ _ ] => eapply step_assign
  | [ |- Step _ (State _ (Sset _ _) _ _ _ _) _ _ ] => apply step_set
  | [ |- Step _ (State _ (Scall _ _ _) _ _ _ _) _ _ ] => eapply step_call
  | [ |- Step _ (Returnstate _ _ _) _ _ ] => eapply step_returnstate
  | [ |- Step _ (State _ Sskip (Kseq _ _) _ _ _) _ _ ] => apply step_skip_seq
  | [ |- Step _ (State _ Sskip (Kloop1 _ _ _) _ _ _) _ _ ] => apply step_skip_or_continue_loop1; left; reflexivity
  | [ |- Step _ (State _ Sskip (Kloop2 _ _ _) _ _ _) _ _ ] => apply step_skip_loop2
  | [ |- Step _ (State _ Sbreak (Kseq _ _) _ _ _) _ _ ] => apply step_break_seq
  | [ |- Step _ (State _ Sbreak (Kloop1 _ _ _) _ _ _) _ _ ] => apply step_break_loop1
  | [ |- Step _ (State _ (Sreturn None) _ _ _ _) _ _ ] => eapply step_return_0
  | [ |- Step _ (State _ (Sreturn (Some _)) _ _ _ _) _ _ ] => eapply step_return_1
  | [ |- Step _ (State _ (Sloop _ _) _ _ _ _) _ _ ] => eapply step_loop
  | [ |- Step _ (State _ (Sifthenelse _ _ _) _ _ _ _) _ _ ] => eapply step_ifthenelse
  | [ |- Step _ (State _ Sbreak _ _ _ _) _ _ ] => eapply step_break_loop1
  | [ |- Step _ (State _ ?s _ _ _ _) _ _ ] => is_const s; unfold s; crush_step
  end.

(* ----------------------------------------------------------------- *)
(** ** Misc utilities *)

Require Import Maps ClightP.

Lemma linkorder_erase_asm (p1 p2: Asm.program):
  Linking.linkorder p1 p2 ->
  Linking.linkorder (erase_program p1) (erase_program p2).
Proof.
  intros (A & B & C). split. apply A. split. apply B.
  intros * H1. destruct p1, p2.
  unfold prog_defmap in *. cbn - [PTree_Properties.of_list] in *.
  destruct ((PTree_Properties.of_list prog_defs) ! id) eqn: Hw.
  - specialize (C _ _ Hw) as  (x & Hx1 & Hx2 & Hx3).
    rewrite ClightP.ptree_of_list_map. rewrite Hx1.
    rewrite ClightP.ptree_of_list_map in H1. rewrite Hw in H1.
    cbn in *. eexists. split; eauto.
    split.
    + inv H1. inv Hx2. cbn. repeat constructor.
      cbn. inv H. repeat constructor; eauto.
    + intros. specialize (Hx3 H). congruence.
  - rewrite ClightP.ptree_of_list_map in H1. rewrite Hw in H1. inv H1.
Qed.

Require Import Integers.

Transparent Int.repr.
Lemma int_repr_inj i j:
  (0 <= i < Int.modulus - 1)%Z -> (0 <= j < Int.modulus - 1)%Z -> Int.repr i = Int.repr j -> i = j.
Proof.
  intros Hi Hj Hij.
  unfold Int.repr in Hij. inv Hij.
  rewrite !Int.Z_mod_modulus_eq in H0.
  rewrite !Z.mod_small in H0; eauto. lia. lia.
Qed.
Opaque Int.repr.

Lemma map_inj {A B} (f: A -> B) xs ys:
  (forall x y, f x = f y -> x = y) ->
  map f xs = map f ys -> xs = ys.
Proof.
  intros Hf. revert ys. induction xs; destruct ys; cbn; intros H; inv H; eauto.
  f_equal; eauto.
Qed.

Global Instance asm_program_sem p: ProgramSem (Asm.semantics p).
Proof.
  split.
  - intros. destruct s.
    destruct H as [H ?]. inv H. unfold valid_query; cbn. 
    unfold Genv.find_funct in H1.
    destruct (rs Asm.PC); try congruence.
    destruct Ptrofs.eq_dec; try congruence.
    split. intros X. discriminate X.
    subst. unfold Genv.find_funct_ptr in H1.
    destruct Genv.find_def eqn: Hdef; try congruence.
    destruct g; try congruence. inv H1.
    rewrite Genv.find_def_spec in Hdef.
    destruct Genv.invert_symbol eqn: Hse; try congruence.
    exists i. split. unfold footprint_of_program.
    rewrite Hdef. auto.
    unfold Genv.symbol_address.
    apply Genv.invert_find_symbol in Hse.
    rewrite Hse. auto.
  - intros. destruct s. cbn in *. inv H.
    unfold valid_query. cbn.
    intros [? (i & Hi & Hse)].
    unfold Genv.find_funct in H0.
    destruct (rs Asm.PC); try congruence.
    destruct Ptrofs.eq_dec; try congruence.
    unfold Genv.find_funct_ptr in H0.
    destruct Genv.find_def eqn: Hdef; try congruence.
    destruct g eqn: Hg; try congruence. inv H0.
    unfold globalenv in Hdef. cbn in *.
    rewrite Genv.find_def_spec in Hdef.
    destruct Genv.invert_symbol eqn: Hs; try congruence.
    apply Genv.invert_find_symbol in Hs.
    unfold Genv.symbol_address in Hse.
    destruct (Genv.find_symbol se i) eqn: Hxe; try congruence.
    inv Hse. exploit Genv.find_symbol_injective.
    apply Hs. apply Hxe. intros ->.
    unfold footprint_of_program in Hi. rewrite Hdef in Hi.
    discriminate Hi.
Qed.
