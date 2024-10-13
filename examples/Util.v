Require Import LanguageInterface Smallstep CallconvAlgebra.
Require Import Compiler CallConv Asmrel.
Require Import Clight.
Require Import  Linking.

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
