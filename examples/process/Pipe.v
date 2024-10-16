Require Import Coqlib Integers.

Require Import Events LanguageInterface Smallstep.
Require Import CategoricalComp Lifting Encapsulation.

Require Import Load With InitMem.

Section SEQ.

  Variant seq_state := | seq1 | seq2 | ret (n: int).
  Inductive seq_initial_state: query li_wp -> seq_state -> Prop :=
  | seq_initial_state_intro q: seq_initial_state q seq1.
  Inductive seq_at_external: seq_state -> query (li_wp + li_wp) -> Prop :=
  | seq_at_external1: seq_at_external seq1 (inl tt)
  | seq_at_external2: seq_at_external seq2 (inr tt).
  Inductive seq_after_external: seq_state -> reply (li_wp + li_wp) -> seq_state -> Prop :=
  | seq_after_external1 n: seq_after_external seq1 (inl n) seq2
  | seq_after_external2 n: seq_after_external seq2 (inr n) (ret n).
  Inductive seq_final_state: seq_state -> reply li_wp -> Prop :=
  | seq_final_state_intro n: seq_final_state (ret n) n.

  Definition seq: semantics (li_wp + li_wp) li_wp :=
    {|
      activate se :=
        {|
          Smallstep.step _ _ _ _ := False;
          Smallstep.initial_state := seq_initial_state;
          Smallstep.at_external := seq_at_external;
          Smallstep.after_external := seq_after_external;
          Smallstep.final_state := seq_final_state;
          Smallstep.globalenv := tt;
        |};
      skel := empty_skel;
      footprint i := False;
    |}.

End SEQ.

Definition pipe_state := list byte.
Instance pset_pipe_state : PSet pipe_state :=
  { pset_init _ := nil }.

Section PIPE.

  Definition pipe_in := (((li_sys + li_sys) + (li_sys + li_sys)) @ pipe_state)%li.
  Definition encap_pipe_in := ((li_sys + li_sys) + (li_sys + li_sys))%li.
  Definition pipe_out := (li_sys + li_sys)%li.
  Variant pipe_internal_state :=
    | pipe1_read_query (n: int64) (s: pipe_state)
    | pipe1_read_reply (bytes: list byte) (s: pipe_state)
    | pipe1_write (bytes: list byte) (s: pipe_state)
    | pipe2_read (n: int64) (s: pipe_state)
    | pipe2_write_query (bytes: list byte) (s: pipe_state)
    | pipe2_write_reply (n: int) (s: pipe_state).

  Inductive pipe_initial_state: query pipe_in -> pipe_internal_state -> Prop :=
  | pipe_initial_state1 n s:
    pipe_initial_state (inl (inl (read_query n)), s) (pipe1_read_query n s)
  | pipe_initial_state2 bytes s:
    pipe_initial_state (inl (inr (write_query bytes)), s) (pipe1_write bytes s)
  | pipe_initial_state3 n s:
    pipe_initial_state (inr (inl (read_query n)), s) (pipe2_read n s)
  | pipe_initial_state4 bytes s:
    pipe_initial_state (inr (inr (write_query bytes)), s) (pipe2_write_query bytes s).
  Inductive pipe_at_external: pipe_internal_state -> query pipe_out -> Prop :=
  | pipe_at_external1 n s:
    pipe_at_external (pipe1_read_query n s) (inl (read_query n))
  | pipe_at_external2 bytes s:
    pipe_at_external (pipe2_write_query bytes s) (inr (write_query bytes)).
  Inductive pipe_after_external: pipe_internal_state -> reply pipe_out -> pipe_internal_state -> Prop :=
  | pipe_after_external1 bytes n s:
    pipe_after_external (pipe1_read_query n s) (inl (read_reply bytes)) (pipe1_read_reply bytes s)
  | pipe_after_external2 n bytes s:
    pipe_after_external (pipe2_write_query bytes s) (inr (write_reply n)) (pipe2_write_reply n s).
  Inductive pipe_final_state: pipe_internal_state -> reply pipe_in -> Prop :=
  | pipe_final_state1 bytes s:
    pipe_final_state (pipe1_read_reply bytes s) ((inl (inl (read_reply bytes))), s)
  | pipe_final_state2 n bytes s:
    n = Int.repr (Z.of_nat (length bytes)) ->
    (* The old buffer is replaced. Otherwise, we'd need "open" or "reset"
       operation to set the buffer to initial state *)
    pipe_final_state (pipe1_write bytes s) ((inl (inr (write_reply n)), bytes))
  | pipe_final_state3 n s:
    (* read all the buffer if [n] is greater than or equal to the length of the
       buffer *)
    Int64.unsigned n >= (Z.of_nat (length s)) ->
    pipe_final_state (pipe2_read n s) ((inr (inl (read_reply s)), nil))
  | pipe_final_state3' n s bytes bytes':
    (* read first [n] bytes otherwise *)
    Int64.unsigned n = (Z.of_nat (length bytes)) ->
    s = bytes ++ bytes' ->
    pipe_final_state (pipe2_read n s) ((inr (inl (read_reply bytes)), bytes'))
  | pipe_final_state4 n s:
    pipe_final_state (pipe2_write_reply n s) ((inr (inr (write_reply n)), s)).

  Definition pipe_operator: semantics pipe_out pipe_in :=
    {|
      activate se :=
        {|
          Smallstep.step _ _ _ _ := False;
          Smallstep.initial_state := pipe_initial_state;
          Smallstep.at_external := pipe_at_external;
          Smallstep.after_external := pipe_after_external;
          Smallstep.final_state := pipe_final_state;
          Smallstep.globalenv := tt;
        |};
      skel := empty_skel;
      footprint i := False;
    |}.

  Definition encap_pipe_operator: pipe_out +-> encap_pipe_in :=
    {|
      pstate := pipe_state;
      esem := pipe_operator;
    |}.

End PIPE.

Definition pipe (L1 L2: semantics (li_sys + li_sys) li_wp) sk: (li_sys + li_sys) +-> li_wp :=
  comp_esem'
    (semantics_embed (comp_semantics' seq (with_semantics L1 L2 sk) sk))
    encap_pipe_operator sk.

Section PIPE_FSIM.

  Import Linking.

  Inductive pipe_match_state:
    (unit + unit) * (pipe_state * pipe_state) ->
    pipe_internal_state -> pipe_internal_state -> Prop :=
  | pipe_match_state1 n s:
    pipe_match_state (inl tt, (s, s)) (pipe1_read_query n s) (pipe1_read_query n s)
  | pipe_match_state2 bytes s:
    pipe_match_state (inl tt, (s, s)) (pipe1_read_reply bytes s) (pipe1_read_reply bytes s)
  | pipe_match_state3 bytes s:
    pipe_match_state (inl tt, (s, s)) (pipe1_write bytes s) (pipe1_write bytes s)
  | pipe_match_state4 n s:
    pipe_match_state (inr tt, (s, s)) (pipe2_read n s) (pipe2_read n s)
  | pipe_match_state5 bytes s:
    pipe_match_state (inr tt, (s, s)) (pipe2_write_query bytes s) (pipe2_write_query bytes s)
  | pipe_match_state6 n s:
    pipe_match_state (inr tt, (s, s)) (pipe2_write_reply n s) (pipe2_write_reply n s).

  Hint Constructors pipe_after_external
    pipe_at_external
    pipe_final_state
    pipe_initial_state
    pipe_match_state.

  Lemma pipe_operator_wp_id:
    E.forward_simulation &cc_wp_id &(cc_wp_id + cc_wp_id) encap_pipe_operator encap_pipe_operator.
  Proof.
    apply st_normalize_fsim. constructor. cbn.
    eapply ST.Forward_simulation with
      (ltof _ (fun (_: unit) => 0%nat))
      (fun _ _ wb _ _ _ st1 st2 => pipe_match_state wb st1 st2)
      (fun _ '(_, (s1, s2)) => s1 = s2);
      try easy.
    { intros. cbn in *. eprod_crush. reflexivity. }
    cbn.
    intros. cbn -[pipe_operator] in *. eprod_crush.
    assert (Hse: wp_match_senv se1 se2). destruct s; eauto. clear H.
    constructor; intros; cbn in *; eprod_crush.
    - inv H1; inv H2; inv H6; eprod_crush; subst; repeat econstructor.
      all: match goal with | [H: ccworld cc_wp_id |- _] => destruct H end; eauto.
    - inv H1; inv H.
      + eexists (_, _). split; eauto.
        eexists (_, (_, _)). repeat econstructor.
      + eexists (_, _). split; eauto.
        eexists (_, (_, _)). repeat econstructor.
      + eexists (_, _). split; eauto.
        eexists (_, (_, _)). repeat econstructor.
      + eexists (_, _). split; eauto.
        eexists (_, (_, _)). repeat econstructor.
      + eexists (_, _). split; eauto.
        eexists (_, (_, _)). repeat econstructor.
    - inv H; inv H1.
      + eexists (inl _). split; eauto.
        eexists _, _. repeat (split; eauto).
        inv H2. eexists _. repeat econstructor.
      + eexists (inr _). split; eauto.
        eexists _, _. repeat (split; eauto).
        inv H2. eexists _. repeat econstructor.
    - inv H.
      Unshelve. all: try eauto; easy.
  Qed.

  Lemma seq_id:
    forward_simulation (1 + 1) 1 seq seq.
  Proof.
    constructor. econstructor. reflexivity. reflexivity.
    intros. instantiate (1 := fun _ _ _ => _). cbn beta. inv H.
    eapply forward_simulation_step with (match_states := eq).
    - intros. inv H. inv H1.
      eexists; split; eauto. constructor.
    - intros. inv H1.
      eexists; split; constructor; eauto.
    - intros. inv H1.
      + eexists _, _. repeat apply conj; repeat constructor; eauto.
        intros. inv H. inv H1. inv H3.
        eexists. split; constructor; eauto.
      + eexists _, _. repeat apply conj; repeat constructor; eauto.
        intros. inv H. inv H1. inv H3.
        eexists. split; constructor; eauto.
    - easy.
    - easy.
      Unshelve. apply wB. apply wB.
  Qed.

  Context {S1 S2 T1 T2: semantics (li_sys + li_sys) li_wp}.
  Context (sk: AST.program unit unit)
    (Hsk1: linkorder (skel S1) sk)
    (Hsk2: linkorder (skel S2) sk).
  Context (HS: forward_simulation cc_wp_id 1 S1 T1) (HT: forward_simulation cc_wp_id 1 S2 T2).

  Lemma pipe_fsim: E.forward_simulation &cc_wp_id &1 (pipe S1 S2 sk) (pipe T1 T2 sk).
  Proof.
    unfold pipe. eapply encap_fsim_lcomp_sk.
    - apply encap_fsim_embed.
      eapply categorical_compose_simulation'; eauto.
      + apply seq_id.
      + apply with_fsim; eauto.
      + apply empty_linkorder.
      + apply linkorder_refl.
    - apply pipe_operator_wp_id.
    - apply linkorder_refl.
    - apply empty_linkorder.
  Qed.

End PIPE_FSIM.
