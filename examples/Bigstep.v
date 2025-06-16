Require Import Relations RelationClasses.
Require Import List.

Require Import Coqlib.
Require Import Maps.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import AST.
Require Import Memory.
Require Import LanguageInterface.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Ctypes.
Require Import Cop.
Require Import Clight.
Require Import models.Coherence.
Require Import CompCertSem.

Section BIGSTEP.

  Variable ge: genv.

  (** ** Big-step semantics for terminating statements and functions *)

  (** The execution of a statement produces an ``outcome'', indicating
  how the execution terminated: either normally or prematurely
  through the execution of a [break], [continue] or [return] statement. *)

  Inductive outcome: Type :=
  | Out_break: outcome                 (**r terminated by [break] *)
  | Out_continue: outcome              (**r terminated by [continue] *)
  | Out_normal: outcome                (**r terminated normally *)
  | Out_return: option (val * type) -> outcome. (**r terminated by [return] *)

  Inductive out_normal_or_continue : outcome -> Prop :=
  | Out_normal_or_continue_N: out_normal_or_continue Out_normal
  | Out_normal_or_continue_C: out_normal_or_continue Out_continue.

  Inductive out_break_or_return : outcome -> outcome -> Prop :=
  | Out_break_or_return_B: out_break_or_return Out_break Out_normal
  | Out_break_or_return_R: forall ov,
      out_break_or_return (Out_return ov) (Out_return ov).

  Definition outcome_switch (out: outcome) : outcome :=
    match out with
    | Out_break => Out_normal
    | o => o
    end.

  Definition outcome_result_value (out: outcome) (t: type) (v: val) (m: mem): Prop :=
    match out, t with
    | Out_normal, Tvoid => v = Vundef
    | Out_return None, Tvoid => v = Vundef
    | Out_return (Some (v',t')), ty => ty <> Tvoid /\ sem_cast v' t' t m = Some v
    | _, _ => False
    end.

  (** [exec_stmt ge e m1 s t m2 out] describes the execution of
  the statement [s].  [out] is the outcome for this execution.
  [m1] is the initial memory state, [m2] the final memory state.
  [t] is the trace of input/output events performed during this
  evaluation. *)
  
  Inductive exec_stmt: env -> temp_env -> mem -> statement ->
                       temp_env -> mem -> token (!li_c) -> outcome -> Prop :=
  | exec_Sskip: forall e le m,
      exec_stmt e le m Sskip
                le m nil Out_normal
  | exec_Sassign: forall e le m a1 a2 loc ofs v2 v m',
      eval_lvalue ge e le m a1 loc ofs ->
      eval_expr ge e le m a2 v2 ->
      sem_cast v2 (typeof a2) (typeof a1) m = Some v ->
      assign_loc ge (typeof a1) m loc ofs v m' ->
      exec_stmt e le m (Sassign a1 a2)
                le m' nil Out_normal
  | exec_Sset: forall e le m id a v,
      eval_expr ge e le m a v ->
      exec_stmt e le m (Sset id a)
                (PTree.set id v le) m nil Out_normal
  | exec_Scall: forall e le m optid a al tyargs tyres cconv vf vargs f m' vres tr,
      classify_fun (typeof a) = fun_case_f tyargs tyres cconv ->
      eval_expr ge e le m a vf ->
      eval_exprlist ge e le m al tyargs vargs ->
      Genv.find_funct ge vf = Some f ->
      type_of_fundef f = Tfunction tyargs tyres cconv ->
      eval_funcall m vf vargs m' tr vres ->
      exec_stmt e le m (Scall optid a al)
                (set_opttemp optid vres le) m' tr Out_normal
  | exec_Sbuiltin:   forall e le m optid ef al tyargs vargs m' vres,
      eval_exprlist ge e le m al tyargs vargs ->
      (* require the trace to be empty because we don't want undeterministic behaviour  *)
      (* predefined external calls that generate events are treated as undefined behaviour *)
      external_call ef ge vargs m E0 vres m' ->
      exec_stmt e le m (Sbuiltin optid ef tyargs al)
                (set_opttemp optid vres le) m' nil Out_normal
  | exec_Sseq_1:   forall e le m s1 s2 le1 m1 le2 m2 out tr1 tr2,
      exec_stmt e le m s1 le1 m1 tr1 Out_normal ->
      exec_stmt e le1 m1 s2 le2 m2 tr2 out ->
      exec_stmt e le m (Ssequence s1 s2)
                le2 m2 (tr1 ++ tr2) out
  | exec_Sseq_2:   forall e le m s1 s2 le1 m1 out tr,
      exec_stmt e le m s1 le1 m1 tr out ->
      out <> Out_normal ->
      exec_stmt e le m (Ssequence s1 s2)
                le1 m1 tr out
  | exec_Sifthenelse: forall e le m a s1 s2 v1 b le' m' out tr,
      eval_expr ge e le m a v1 ->
      bool_val v1 (typeof a) m = Some b ->
      exec_stmt e le m (if b then s1 else s2) le' m' tr out ->
      exec_stmt e le m (Sifthenelse a s1 s2)
                le' m' tr out
  | exec_Sreturn_none:   forall e le m,
      exec_stmt e le m (Sreturn None)
                le m nil (Out_return None)
  | exec_Sreturn_some: forall e le m a v,
      eval_expr ge e le m a v ->
      exec_stmt e le m (Sreturn (Some a))
                le m nil (Out_return (Some (v, typeof a)))
  | exec_Sbreak:   forall e le m,
      exec_stmt e le m Sbreak
                le m nil Out_break
  | exec_Scontinue:   forall e le m,
      exec_stmt e le m Scontinue
                le m nil Out_continue
  | exec_Sloop_stop1: forall e le m s1 s2 le' m' out' out tr,
      exec_stmt e le m s1 le' m' tr out' ->
      out_break_or_return out' out ->
      exec_stmt e le m (Sloop s1 s2)
                le' m' tr out
  | exec_Sloop_stop2: forall e le m s1 s2 le1 m1 out1 le2 m2 out2 out tr1 tr2,
      exec_stmt e le m s1 le1 m1 tr1 out1 ->
      out_normal_or_continue out1 ->
      exec_stmt e le1 m1 s2 le2 m2 tr2 out2 ->
      out_break_or_return out2 out ->
      exec_stmt e le m (Sloop s1 s2)
                le2 m2 (tr1++tr2) out
  | exec_Sloop_loop: forall e le m s1 s2 le1 m1 out1 le2 m2 le3 m3 out tr1 tr2 tr3,
      exec_stmt e le m s1 le1 m1 tr1 out1 ->
      out_normal_or_continue out1 ->
      exec_stmt e le1 m1 s2 le2 m2 tr2 Out_normal ->
      exec_stmt e le2 m2 (Sloop s1 s2) le3 m3 tr3 out ->
      exec_stmt e le m (Sloop s1 s2)
                le3 m3 (tr1++tr2++tr3) out
  | exec_Sswitch:   forall e le m a v n sl le1 m1 out tr,
      eval_expr ge e le m a v ->
      sem_switch_arg v (typeof a) = Some n ->
      exec_stmt e le m (seq_of_labeled_statement (select_switch n sl)) le1 m1 tr out ->
      exec_stmt e le m (Sswitch a sl)
                le1 m1 tr (outcome_switch out)

  (** [eval_funcall m1 fd args t m2 res] describes the invocation of
  function [fd] with arguments [args].  [res] is the value returned
  by the call.  *)

  with eval_funcall: mem -> val -> list val ->
                     mem -> token (!li_c) -> val -> Prop :=
  | eval_funcall_internal: forall le m f vargs e m1 m2 m3 out vres m4 tr vf,
      Genv.find_funct ge vf = Some (Internal f) ->
      alloc_variables ge empty_env m (f.(fn_params) ++ f.(fn_vars)) e m1 ->
      list_norepet (var_names f.(fn_params) ++ var_names f.(fn_vars)) ->
      bind_parameters ge e m1 f.(fn_params) vargs m2 ->
      exec_stmt e (create_undef_temps f.(fn_temps)) m2 f.(fn_body) le m3 tr out ->
      outcome_result_value out f.(fn_return) vres m3 ->
      Mem.free_list m3 (blocks_of_env ge e) = Some m4 ->
      eval_funcall m vf vargs m4 tr vres
  | eval_funcall_external: forall m ef targs tres cconv vargs vres m' vf,
      Genv.find_funct ge vf = Some (External ef targs tres cconv) ->
      (* require the trace to be empty because we don't want undeterministic behaviour  *)
      (* predefined external calls that generate events are treated as undefined behaviour *)
      external_call ef ge vargs m E0 vres m' ->
      eval_funcall m vf vargs m' nil vres
  | eval_funcall_ef : forall name sg targs tres cconv vf vargs m vres m' qx rx,
      let f := External (EF_external name sg) targs tres cconv in
      qx = cq vf sg vargs m ->
      rx = cr vres m' ->
      Genv.find_funct ge vf = Some f ->
      eval_funcall m vf vargs m' ((qx, rx) :: nil) vres.

  Scheme exec_stmt_ind2 := Minimality for exec_stmt Sort Prop
    with eval_funcall_ind2 := Minimality for eval_funcall Sort Prop.
  Combined Scheme exec_stmt_funcall_ind from exec_stmt_ind2, eval_funcall_ind2.

  Inductive outcome_state_match
            (e: env) (le: temp_env) (m: mem) (f: function) (k: cont): outcome -> state -> Prop :=
  | osm_normal:
      outcome_state_match e le m f k Out_normal (State f Sskip k e le m)
  | osm_break:
      outcome_state_match e le m f k Out_break (State f Sbreak k e le m)
  | osm_continue:
      outcome_state_match e le m f k Out_continue (State f Scontinue k e le m)
  | osm_return_none: forall k',
      call_cont k' = call_cont k ->
      outcome_state_match e le m f k
                          (Out_return None) (State f (Sreturn None) k' e le m)
  | osm_return_some: forall a v k',
      call_cont k' = call_cont k ->
      eval_expr ge e le m a v ->
      outcome_state_match e le m f k
                          (Out_return (Some (v,typeof a))) (State f (Sreturn (Some a)) k' e le m).

  Inductive bigstep_lmaps : token (!li_c)  -> token li_c -> Prop :=
  | bigstep_lmaps_intro tr q r m m' vf vargs vres targs tres tcc f:
      (* valid query *)
      Genv.is_internal ge (entry q) = true ->
      (* initial state *)
      q = cq vf (signature_of_type targs tres tcc) vargs m ->
      Genv.find_funct ge vf = Some (Internal f) ->
      type_of_function f = Tfunction targs tres tcc ->
      val_casted_list vargs targs ->
      Ple (Genv.genv_next ge) (Mem.nextblock m) ->
      (* eval function body *)
      eval_funcall m vf vargs m' tr vres ->
      (* final state *)
      r = cr vres m' ->
      bigstep_lmaps tr (q, r).
End BIGSTEP.

Section BIGSTEP_TO_TRANSITIONS.
  Hint Resolve app_nil_r app_assoc.
  Section MONOID.
    Class Monoid (A : Type) :=
      {
        empty : A;
        append : A -> A -> A;

        left_neutrality : forall x, append empty x = x;
        right_neutrality : forall x, append x empty = x;
        associativity : forall x y z, append x (append y z) = append (append x y) z
      }.
    Global Program Instance list_monoid {A} : Monoid (list A) :=
      {
        empty := nil;
        append x y := x ++ y
      }.
  End MONOID.
  
  Hint Rewrite app_nil_r app_assoc : list_rewrite.
  Hint Unfold empty append list_monoid.
  Ltac monoid_solve := autounfold; autorewrite with list_rewrite; auto.
  
  Section CLOSURES.
    Variable genv: Type.
    Variable state: Type.
    Context (acc : Type) {H : Monoid acc}.
    Variable step: genv -> state -> acc -> state -> Prop.

    (** Zero, one or several transitions.  Also known as Kleene closure,
    or reflexive transitive closure. *)
    Notation " '[]' " := empty (at level 1).
    Notation " x '~~' y " := (append x y) (at level 1).
    Hint Rewrite left_neutrality right_neutrality.
    Hint Resolve left_neutrality right_neutrality associativity.

    Inductive star (ge: genv): state -> acc -> state -> Prop :=
    | star_refl: forall s,
        star ge s [] s
    | star_step: forall s1 tr1 s2 tr2 s3 tr,
        step ge s1 tr1 s2 -> star ge s2 tr2 s3 -> tr = tr1 ~~ tr2 ->
        star ge s1 tr s3.

    Lemma star_one:
      forall ge s1 tr s2, step ge s1 tr s2 -> star ge s1 tr s2.
    Proof.
      intros. eapply star_step; eauto. apply star_refl.
    Qed.
    Lemma star_trans:
      forall ge s1 tr1 s2, star ge s1 tr1 s2 ->
                           forall tr2 s3 tr, star ge s2 tr2 s3 ->
                                             tr = tr1 ~~ tr2 ->
                                             star ge s1 tr s3.
    Proof.
      induction 1; intros.
      rewrite H1. autorewrite with core. auto.
      eapply star_step; eauto. subst. autorewrite with core. auto.
    Qed.
    Lemma star_left:
      forall ge s1 tr1 s2 tr2 s3 tr,
        step ge s1 tr1 s2 -> star ge s2 tr2 s3 -> tr = tr1 ~~ tr2 ->
        star ge s1 tr s3.
    Proof star_step.
    Lemma star_right:
      forall ge s1 tr1 s2 tr2 s3 tr,
        star ge s1 tr1 s2 -> step ge s2 tr2 s3 -> tr = tr1 ~~ tr2 ->
        star ge s1 tr s3.
    Proof.
      intros. eapply star_trans. eauto. apply star_one. eauto. auto.
    Qed.
  End CLOSURES.

  Section TRANSITION.
    (* A transition system that fits into the star operator, and is sound w.r.t. lts in CompCertSem.v *)
    Context {liA liB S} (L : lts liA liB S).
    Inductive transition_step (ge : genvtype L) : S -> token (!liA) -> S -> Prop :=
    | silent_step s s':
        Step L s E0 s' ->
        transition_step ge s nil s'
    | external_step s s' q r:
        Smallstep.at_external L s q ->
        Smallstep.after_external L s r s' ->
        transition_step ge s ((q, r) :: nil) s'.
    Inductive transition : token (!liA) -> token liB -> Prop :=
    | transition_intro s s' tr q r:
        (* initial state *)
        valid_query L q = true ->
        Smallstep.initial_state L q s ->
        (* transition steps *)
        (star _ _ _ transition_step) (Smallstep.globalenv L) s tr s' ->
        (* final state *)
        Smallstep.final_state L s' r ->
        transition tr (q, r).
    Hint Unfold list_monoid.
    Lemma transition_sound t q r:
      transition t (q, r) -> lts_lmaps L t (q, r).
    Proof.
      inversion 1. subst.
      econstructor; [ auto | eauto | ].
      clear H H2 H3. induction H5.
      - apply lts_trace_final. auto.
      - specialize (IHstar H6).
        inversion H; subst.
        + eapply lts_trace_step; eauto.
        + eapply lts_trace_external; eauto.
    Qed.
  End TRANSITION.
  
  Variable p : program.
  Variable se : Genv.symtbl.
  Let sem : semantics li_c li_c := Clight.semantics1 p.
  Let lts : lts li_c li_c state := sem se.
  Let ge : genv := Smallstep.globalenv lts.
  Let star_transition := (star _ _ _ (transition_step lts)) ge.

  Lemma is_call_cont_call_cont:
    forall k, is_call_cont k -> call_cont k = k.
  Proof.
    destruct k; simpl; intros; contradiction || auto.
  Qed.

  (* exec_stmt and eval_funcall correspond to transition steps *)
  Hint Constructors outcome_state_match.
  Lemma exec_stmt_eval_funcall_steps:
    (forall e le m s le' m' tr out,
        exec_stmt ge e le m s le' m' tr out ->
        forall f k, exists S,
            star_transition (State f s k e le m) tr S /\
            outcome_state_match ge e le' m' f k out S)
    /\
    (forall m vf args m' tr res,
        eval_funcall ge m vf args m' tr res ->
        forall k,
          is_call_cont k ->
          star_transition (Callstate vf args k m) tr (Returnstate res k m')).
  Proof.
    apply exec_stmt_funcall_ind; intros.

    (* skip *)
    - eexists. split. apply star_refl. auto.
    (* assign *)
    - eexists. split. apply star_one. apply silent_step. econstructor; eauto. auto.
    (* set *)
    - eexists. split. apply star_one. apply silent_step. econstructor; eauto. auto.
    (* call *)
    - eexists. split.
      eapply star_left. apply silent_step. econstructor; eauto.
      eapply star_right. apply H5. simpl; auto.
      apply silent_step. econstructor. reflexivity.
      monoid_solve. auto.
    (* builtin *)
    - eexists. split. apply star_one. apply silent_step. econstructor; eauto. auto.
    (* sequence 2 *)
    - destruct (H0 f (Kseq s2 k)) as [S1 [A1 B1]]. inv B1.
      destruct (H2 f k) as [S2 [A2 B2]].
      eexists. split.
      eapply star_left. apply silent_step. econstructor.
      eapply star_trans. eexact A1.
      eapply star_left. apply silent_step. constructor. eexact A2.
      reflexivity. reflexivity. monoid_solve. auto.
    (* sequence 1 *)
    - destruct (H0 f (Kseq s2 k)) as [S1 [A1 B1]].
      set (S2 :=
             match out with
             | Out_break => State f Sbreak k e le1 m1
             | Out_continue => State f Scontinue k e le1 m1
             | _ => S1
             end).
      exists S2. split.
      eapply star_left. apply silent_step. econstructor.
      eapply star_trans. eexact A1.
      unfold S2; inv B1;
        [ congruence |
          apply star_one; apply silent_step; apply step_break_seq |
          apply star_one; apply silent_step; apply step_continue_seq |
          apply star_refl |
          apply star_refl ].
      reflexivity. monoid_solve.
      unfold S2; inv B1; congruence || econstructor; eauto.
    (* ifthenelse *)
    - destruct (H2 f k) as [S1 [A1 B1]].
      exists S1; split.
      eapply star_left. 2: eexact A1.
      apply silent_step.
      eapply step_ifthenelse; eauto. monoid_solve. auto.
    (* return none *)
    - econstructor; split. apply star_refl. constructor. auto.
    (* return some *)
    - econstructor; split. apply star_refl. econstructor; eauto.
    (* break *)
    - econstructor; split. apply star_refl. constructor.
    (* continue *)
    - econstructor; split. apply star_refl. constructor.
    (* loop stop 1 *)
    - destruct (H0 f (Kloop1 s1 s2 k)) as [S1 [A1 B1]].
      set (S2 :=
             match out' with
             | Out_break => State f Sskip k e le' m'
             | _ => S1
             end).
      exists S2; split.
      eapply star_left. apply silent_step. eapply step_loop.
      eapply star_trans. eexact A1.
      unfold S2. inversion H1; subst.
      inv B1. apply star_one. apply silent_step. constructor.
      apply star_refl.
      reflexivity. monoid_solve.
      unfold S2. inversion H1; subst. constructor. inv B1; econstructor; eauto.
    (* loop stop 2 *)
    - destruct (H0 f (Kloop1 s1 s2 k)) as [S1 [A1 B1]].
      destruct (H3 f (Kloop2 s1 s2 k)) as [S2 [A2 B2]].
      set (S3 :=
             match out2 with
             | Out_break => State f Sskip k e le2 m2
             | _ => S2
             end).
      exists S3; split.
      eapply star_left. apply silent_step. eapply step_loop.
      eapply star_trans. eexact A1.
      eapply star_left with (s2 := State f s2 (Kloop2 s1 s2 k) e le1 m1).
      inv H1; inv B1; apply silent_step; constructor; auto. 
      eapply star_trans. eexact A2.
      unfold S3. inversion H4; subst.
      inv B2. apply star_one. apply silent_step. constructor. apply star_refl.
      reflexivity. reflexivity. reflexivity. monoid_solve.
      unfold S3. inversion H4; subst. constructor. inv B2; econstructor; eauto.
    (* loop loop *)
    - destruct (H0 f (Kloop1 s1 s2 k)) as [S1 [A1 B1]].
      destruct (H3 f (Kloop2 s1 s2 k)) as [S2 [A2 B2]].
      destruct (H5 f k) as [S3 [A3 B3]].
      exists S3; split.
      eapply star_left. apply silent_step. eapply step_loop.
      eapply star_trans. eexact A1.
      eapply star_left with (s2 := State f s2 (Kloop2 s1 s2 k) e le1 m1).
      inv H1; inv B1; apply silent_step; constructor; auto.
      eapply star_trans. eexact A2.
      eapply star_left with (s2 := State f (Sloop s1 s2) k e le2 m2).
      inversion H4; subst; inv B2; apply silent_step; constructor; auto.
      eexact A3.
      reflexivity. reflexivity. reflexivity. reflexivity.
      monoid_solve. auto.
    (* switch *)
    - destruct (H2 f (Kswitch k)) as [S1 [A1 B1]].
      set (S2 :=
             match out with
             | Out_normal => State f Sskip k e le1 m1
             | Out_break => State f Sskip k e le1 m1
             | Out_continue => State f Scontinue k e le1 m1
             | _ => S1
             end).
      exists S2; split.
      eapply star_left. apply silent_step. eapply step_switch; eauto.
      eapply star_trans. eexact A1.
      unfold S2; inv B1.
      apply star_one. apply silent_step. constructor. auto.
      apply star_one. apply silent_step. constructor. auto.
      apply star_one. apply silent_step. constructor.
      apply star_refl.
      apply star_refl.
      reflexivity.  monoid_solve.
      unfold S2. inv B1; simpl; econstructor; eauto.
    (* call internal *)
    - destruct (H4 f k) as [S1 [A1 B1]].
      eapply star_left. apply silent_step.
      eapply step_internal_function; eauto. econstructor; eauto.
      eapply star_right. eexact A1.
      {
        inv B1; simpl in H5; try contradiction.
        (* Out_normal *)
        + assert (fn_return f = Tvoid /\ vres = Vundef).
          destruct (fn_return f); auto || contradiction.
          destruct H8. subst vres. apply silent_step. apply step_skip_call; auto.
        (* Out_return None *)
        + assert (fn_return f = Tvoid /\ vres = Vundef).
          destruct (fn_return f); auto || contradiction.
          destruct H9. subst vres.
          rewrite <- (is_call_cont_call_cont k H7). rewrite <- H8.
          apply silent_step. apply step_return_0; auto.
        (* Out_return Some *)
        + destruct H5.
          rewrite <- (is_call_cont_call_cont k H7). rewrite <- H8.
          apply silent_step. eapply step_return_1; eauto.
      }
      reflexivity. monoid_solve.
    (* call external *)
    - apply star_one. apply silent_step. eapply step_external_function; eauto.
    (* query and reply *)
    - apply star_one. apply external_step.
      rewrite H.
      eapply at_external_intro. subst f. apply H1.
      rewrite H0.
      apply after_external_intro.
  Qed.
  Hint Unfold is_call_cont.
  Lemma bigstep_lmaps_soundness tr q r:
    bigstep_lmaps ge tr (q, r) -> lts_lmaps lts tr (q, r).
  Proof.
    intros bigstep.
    apply transition_sound.
    inversion bigstep. subst.
    econstructor;
      [ auto |
        econstructor; eauto |
        eapply (proj2 exec_stmt_eval_funcall_steps); eauto |
        constructor ].
  Qed.
End BIGSTEP_TO_TRANSITIONS.

Section BIGSTEP_COH_SPACE.
  Variable se : Genv.symtbl.
  Variable p : program.
  Let ge := globalenv se p.
  Local Obligation Tactic := idtac.
  Program Definition c_bigstep_lmaps : !li_c --o li_c :=
    {|
      has '(t, u) := bigstep_lmaps ge t u
    |}.
  Next Obligation.
    intros p1 p2.
    destruct p1 as [tr1 [q1 r1]].
    destruct p2 as [tr2 [q2 r2]].
    simpl. intros bigstep1 bigstep2 coh.
    exploit (has_coh _ (clight p se) (tr1, (q1, r1)) (tr2, (q2, r2))).
    - apply bigstep_lmaps_soundness. apply bigstep1.
    - apply bigstep_lmaps_soundness. apply bigstep2.
    - apply coh.
    - auto.
  Qed.
End BIGSTEP_COH_SPACE.

Definition clight_bigstep (p : Clight.program) se : !li_c --o li_c :=
  c_bigstep_lmaps se p.
Theorem bigstep_soundness (p : Clight.program) se:
  forall tr q r,
    has (clight_bigstep p se) (tr, (q, r)) -> has (clight p se) (tr, (q, r)).
Proof.
  apply bigstep_lmaps_soundness.
Qed.
