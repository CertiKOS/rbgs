Require Import Coqlib Integers.

Require Import Events LanguageInterface Smallstep Globalenvs Values Memory.
Require Import AST Ctypes Clight.
Require Import CategoricalComp Lifting Encapsulation.

Require Import List Maps.
Import ListNotations.

Require Import Load With InitMem Pipe.

Section NTH.

  Inductive nth {A}: list A -> nat -> A -> Prop :=
  | nth_this a l: nth (a :: l) 0%nat a
  | nth_next a b n l:
    nth l n b -> nth (a :: l) (S n) b.

  Open Scope Z_scope.
  Local Transparent Mem.loadbytes Mem.load Mem.store.

  Lemma getN_nth_exists len memvals bytes start i:
    Mem.getN len start memvals = map Byte bytes ->
    (i < len)%nat ->
    exists byte : byte, nth bytes i byte.
  Proof.
    revert start i len memvals. induction bytes.
    - intros. destruct len.
      + inv H0.
      + inv H.
    - intros. destruct len.
      + inv H0.
      + destruct i.
        * exists a. constructor.
        * cbn in H. inv H.
          exploit IHbytes. eauto.
          instantiate (1 := i). lia.
          intros (b & Hb). exists b. constructor. eauto.
  Qed.

  Lemma loadbytes_nth m b bytes i len:
    Mem.loadbytes m b 0 len = Some (map Byte bytes) ->
    0 <= i < len ->
    exists byte, nth bytes (Z.to_nat i) byte.
  Proof.
    intros H Hi. unfold Mem.loadbytes in H.
    destruct Mem.range_perm_dec eqn: Hp; try congruence. clear Hp.
    inv H.
    exploit getN_nth_exists; eauto.
    lia.
  Qed.

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

  Lemma loadbyte m b bytes i len:
    Mem.loadbytes m b 0 len = Some (map Byte bytes) ->
    0 <= i < len ->
    exists byte,
      nth bytes (Z.to_nat i) byte /\
        Mem.load Mint8unsigned m b i = Some (Vint (Int.repr (Byte.unsigned byte))).
  Proof.
    intros. exploit loadbytes_nth; eauto.
    intros (byte & Hbyte). exists byte. split; eauto.
    eapply loadbyte'; eauto.
  Qed.

  Inductive nth_update {A}: list A -> nat -> (A -> A) -> list A -> Prop :=
  | nth_update_this a f l: nth_update (a :: l) 0%nat f (f a :: l)
  | nth_update_next a n f l l':
    nth_update l n f l' -> nth_update (a :: l) (S n) f (a :: l').

  Local Transparent Archi.big_endian.

  Lemma getN_set_outside len start x v memvals:
    (x < start \/ start + Z.of_nat len <= x)%Z ->
    Mem.getN len start (ZMap.set x v memvals) = Mem.getN len start memvals.
  Proof.
    revert start x v memvals. induction len.
    - intros. cbn. reflexivity.
    - intros. cbn. f_equal.
      + rewrite ZMap.gso; eauto. lia.
      + eapply IHlen. lia.
  Qed.

  Lemma nth_update_getN i len start memvals f byte bytes bytes':
    (i < len)%nat ->
    nth bytes i byte ->
    nth_update bytes i f bytes' ->
    Mem.getN len start memvals = map Byte bytes ->
    Mem.getN len start (ZMap.set (start + Z.of_nat i) (Byte (f byte)) memvals) = map Byte bytes'.
  Proof.
    revert start i len memvals byte bytes'. induction bytes.
    - intros. inv H0.
    - intros. inv H0; inv H1.
      + cbn. destruct len. lia. cbn in H2. inv H2. rewrite Z.add_0_r.
        cbn. f_equal.
        * rewrite ZMap.gss. reflexivity.
        * apply getN_set_outside. lia.
      + cbn. destruct len. lia. cbn in H2. inv H2.
        assert (Z.pos (Pos.of_succ_nat n) = 1 + Z.of_nat n) as Hn. lia.
        cbn. f_equal.
        * rewrite ZMap.gso; try lia. reflexivity.
        * rewrite Hn. rewrite Z.add_assoc. eapply IHbytes; eauto. lia.
  Qed.

  Lemma storebyte m b bytes i len byte m' bytes' f:
    Mem.loadbytes m b 0 len = Some (map Byte bytes) ->
    0 <= i < len -> nth bytes (Z.to_nat i) byte ->
    Mem.store Mint8unsigned m b i (Vint (Int.repr (Byte.unsigned (f byte)))) = Some m' ->
    nth_update bytes (Z.to_nat i) f bytes' ->
    Mem.loadbytes m' b 0 len = Some (map Byte bytes').
  Proof.
    intros.
    unfold Mem.loadbytes in *.
    destruct Mem.range_perm_dec; try congruence. inv H.
    cbn. destruct Mem.range_perm_dec.
    2: { exfalso. apply n. intros p Hp. eauto with mem. }
    unfold Mem.store in H2.
    destruct Mem.valid_access_dec; try congruence. inv H2.
    clear r0. cbn. f_equal.
    rewrite Int.unsigned_repr.
    2: { pose proof (Byte.unsigned_range_2 (f byte)) as Hx; cbn in *; lia. }
    rewrite Byte.repr_unsigned.
    rewrite PMap.gss.
    exploit (nth_update_getN (Z.to_nat i) (Z.to_nat len) 0); eauto. lia.
    cbn.
    rewrite Z_to_nat_max. rewrite Z.max_l. 2: lia. eauto.
  Qed.

  Lemma nth_update_length {A} (l: list A) n f l':
    nth_update l n f l' -> length l = length l'.
  Proof. intros H. induction H; cbn; lia. Qed.

End NTH.

Notation hello_bytes := [ Byte.repr 104; Byte.repr 101; Byte.repr 108; Byte.repr 108; Byte.repr 111 ].
Notation uryyb_bytes := [ Byte.repr 117; Byte.repr 114; Byte.repr 121; Byte.repr 121; Byte.repr 98].
Definition rot13_byte (b: byte) : byte :=
  Byte.add (Byte.modu (Byte.sub b (Byte.repr 84)) (Byte.repr 26)) (Byte.repr 97).
Definition rot13_bytes : list byte -> list byte := map rot13_byte.
Lemma rot13_bytes_hello: rot13_bytes hello_bytes = uryyb_bytes.
Proof. cbn. repeat f_equal. Qed.
Lemma rot13_bytes_urbby: rot13_bytes uryyb_bytes = hello_bytes.
Proof. cbn. repeat f_equal. Qed.

Notation tvoid := (Tvoid).
Notation tchar := (Tint I8 Unsigned noattr).
Notation tint := (Tint I32 Unsigned noattr).
Notation tlong := (Tlong Unsigned noattr).
Notation tarray := (fun ty size => Tarray ty size noattr).
Notation tptr := (fun ty => Tpointer ty noattr).

Definition rw_parameters := Tcons tint (Tcons (tptr tchar) (Tcons tlong Tnil)).
Definition rw_type :=
  Tfunction rw_parameters tint cc_default.
Definition rw_sig : signature :=
  signature_of_type rw_parameters tvoid cc_default.
Definition write : fundef :=
  External (EF_external "write" rw_sig) rw_parameters tint cc_default.
Definition read : fundef :=
  External (EF_external "read" rw_sig) rw_parameters tint cc_default.

Definition secret_main_id: positive := 1.
Definition secret_write_id: positive := 2.
Definition secret_msg_id: positive := 3.

Definition msg_il : list init_data :=
  [ Init_int8 (Int.repr 117); (* u *)
    Init_int8 (Int.repr 114); (* r *)
    Init_int8 (Int.repr 121); (* y *)
    Init_int8 (Int.repr 121); (* y *)
    Init_int8 (Int.repr 98) ]. (* b *)

Definition msg_globvar : globvar type :=
  {|
    gvar_info := tarray tchar 6%Z;
    gvar_init := msg_il;
    gvar_readonly := false;
    gvar_volatile := false;
  |}.

Definition secret_main_body : statement :=
  Ssequence
    (* write(1, msg, sizeof msg - 1) *)
    (Scall None (Evar secret_write_id rw_type)
       [ Econst_int (Int.repr 1) tint;
         Eaddrof (Evar secret_msg_id (tptr tchar)) (tptr tchar);
         Econst_long (Int64.repr 5) tlong ]) (* sizeof msg - 1 *)
    (Sreturn (Some (Econst_int (Int.repr 0) tint))).

Definition secret_main : function :=
  {|
    fn_return := tint;
    fn_callconv := cc_default;
    fn_params := [];
    fn_temps := [];
    fn_vars := [];
    fn_body := secret_main_body;
  |}.

Program Definition secret_program : Clight.program :=
  {|
    prog_defs := [ (secret_main_id, Gfun (Internal secret_main));
                   (secret_write_id, Gfun write);
                   (secret_msg_id, Gvar msg_globvar)
    ];
    prog_public := [ secret_main_id ];
    prog_main := Some secret_main_id;
    prog_types := [];
    prog_comp_env := (PTree.empty _);
  |}.
Next Obligation. reflexivity. Qed.

Definition secret_c : Smallstep.semantics (li_sys + li_sys) li_wp := load_c secret_program.

Section SECRET_SPEC.

  Variant secret_state :=
    | secret1 | secret2 | secret3 | secret4.

  Inductive secret_spec_initial_state: query li_wp -> secret_state -> Prop :=
  | secret_spec_initial_state_intro q: secret_spec_initial_state q secret1.
  Inductive secret_spec_at_external: secret_state -> query (li_sys + li_sys) -> Prop :=
  | secret_spec_at_external_intro bytes:
    bytes = uryyb_bytes ->
    secret_spec_at_external secret2 (inr (write_query bytes)).
  Inductive secret_spec_after_external: secret_state -> reply (li_sys + li_sys) -> secret_state -> Prop :=
  | secret_spec_after_external_intro n:
    secret_spec_after_external secret2 (inr (write_reply n)) secret3.
  Inductive secret_spec_final_state: secret_state -> reply li_wp -> Prop :=
  | secret_spec_final_state_intro: secret_spec_final_state secret4 Int.zero.
  Inductive secret_step : secret_state -> trace -> secret_state -> Prop :=
  | secret_step1: secret_step secret1 E0 secret2
  | secret_step2: secret_step secret3 E0 secret4.

  Definition secret_spec: Smallstep.semantics (li_sys + li_sys) li_wp :=
    {|
      activate se :=
        {|
          Smallstep.step _ := secret_step;
          Smallstep.initial_state := secret_spec_initial_state;
          Smallstep.at_external := secret_spec_at_external;
          Smallstep.after_external := secret_spec_after_external;
          Smallstep.final_state := secret_spec_final_state;
          Smallstep.globalenv := tt;

        |};
      skel := AST.erase_program secret_program;
      footprint := AST.footprint_of_program secret_program;
    |}.

End SECRET_SPEC.

Ltac one_step := eapply star_left with (t1 := E0) (t2 := E0); [ | | reflexivity ].

Require Import Lia.

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
Ltac destruct_or H :=
  match type of H with
  | _ \/ _ => destruct H as [H|H]; [ |destruct_or H]
  | _ => idtac
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

Ltac one_trivial_step :=
  one_step; [ eapply step2; eapply step1; crush_step; crush_expr; try solve [ constructor | easy ] | ].

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

Hint Constructors Cop.val_casted.

Section SECRET_FSIM.

  Notation L1 := (comp_semantics' (semantics1 secret_program) (sys_c secret_program) (erase_program secret_program)).
  Opaque semantics1.

  Inductive secret_match_state (se: Genv.symtbl): secret_state -> Smallstep.state secret_c -> Prop :=
  | secret_match_state1:
    secret_match_state se secret1 (st1 (init_c secret_program) L1 None)
  | secret_match_state2 vf m args:
    secret_match_state se secret2
      (st2 (init_c secret_program) L1 None
         (st2 (semantics1 secret_program) (sys_c secret_program)
         (Callstate vf args (Kcall None secret_main empty_env (PTree.empty val) (Kseq (Sreturn (Some (Econst_int (Int.repr 0) tint))) Kstop)) m)
         (sys_write_query uryyb_bytes m)))
  | secret_match_state3 vf n m args:
    secret_match_state se secret3
      (st2 (init_c secret_program) L1 None
         (st2 (semantics1 secret_program) (sys_c secret_program)
         (Callstate vf args (Kcall None secret_main empty_env (PTree.empty val) (Kseq (Sreturn (Some (Econst_int (Int.repr 0) tint))) Kstop)) m)
         (sys_write_reply n m)))
  | secret_match_state4:
    secret_match_state se secret4 (st1 (init_c secret_program) L1 (Some Int.zero)).

  Lemma secret_prog_defmap_main:
    (prog_defmap secret_program) ! secret_main_id = Some (Gfun (Internal secret_main)).
  Proof. reflexivity. Qed.

  Lemma secret_prog_defmap_write:
    (prog_defmap secret_program) ! secret_write_id = Some (Gfun write).
  Proof. reflexivity. Qed.

  Lemma secret_prog_defmap_msg:
    (prog_defmap secret_program) ! secret_msg_id = Some (Gvar msg_globvar).
  Proof. reflexivity. Qed.

  Lemma secret_init_mem se:
    Genv.valid_for (erase_program secret_program) se ->
    exists m, init_mem se (erase_program secret_program) = Some m /\
           (forall b, Genv.find_symbol se secret_msg_id = Some b ->
                 Mem.loadbytes m b (Ptrofs.unsigned Ptrofs.zero) 5 = Some (map Byte uryyb_bytes)).
  Proof.
    intros Hvalid.
    edestruct init_mem_exists with
      (p := (erase_program secret_program)) as [m Hm]; eauto.
    - split.
      + cbn in H. destruct_or H; inv H. cbn.
        repeat apply conj; solve [ easy | apply Z.divide_1_l ].
      + cbn in H. destruct_or H; inv H. cbn. intros.
        destruct_or H; inv H.
    - exists m. split; eauto. intros b Hb.
      unfold init_mem in Hm.
      Opaque Genv.store_init_data_list.
      cbn in Hm.
      Ltac destruct_match :=
        match goal with
        | [ H: context [ match ?x with | Some _ => _ | None => _ end ] |- _ ] =>
            let H' := fresh "H" in destruct x eqn:H'; [ | inv H ]
        end.
      repeat (destruct_match; eprod_crush).
      inv Hb. inv Hm.
      eapply (@Genv.store_init_data_list_loadbytes se b msg_il) in H5.
      + erewrite Mem.loadbytes_drop; eauto.
        right. right. right. constructor.
      + eapply Genv.store_zeros_loadbytes. eauto.
  Qed.

  Lemma main_block se:
    Genv.valid_for (AST.erase_program secret_program) se ->
    exists b, Genv.find_symbol (globalenv se secret_program) secret_main_id = Some b /\
           Genv.find_funct (globalenv se secret_program) (Vptr b Ptrofs.zero) = Some (Internal secret_main).
  Proof.
    intros Hse.
    exploit @Genv.find_def_symbol; eauto.
    intros [H _]. specialize (H secret_prog_defmap_main).
    destruct H as (b & Hb1 & Hb2); eauto.
    exists b. split; eauto. eapply genv_funct_symbol; eauto.
  Qed.

  Lemma write_block se:
    Genv.valid_for (AST.erase_program secret_program) se ->
    exists b, Genv.find_symbol (globalenv se secret_program) secret_write_id = Some b /\
           Genv.find_funct (globalenv se secret_program) (Vptr b Ptrofs.zero) = Some write.
  Proof.
    intros Hse.
    exploit @Genv.find_def_symbol; eauto.
    intros [H _]. specialize (H secret_prog_defmap_write).
    destruct H as (b & Hb1 & Hb2); eauto.
    exists b. split; eauto. eapply genv_funct_symbol; eauto.
  Qed.

  Lemma msg_block se:
    Genv.valid_for (AST.erase_program secret_program) se ->
    exists b, Genv.find_symbol (globalenv se secret_program) secret_msg_id = Some b.
  Proof.
    intros Hse.
    exploit @Genv.find_def_symbol; eauto.
    intros [H _]. specialize (H secret_prog_defmap_msg).
    destruct H as (b & Hb1 & Hb2); eauto.
  Qed.

  Lemma secret_fsim: forward_simulation 1 1 secret_spec secret_c.
  Proof.
    constructor. econstructor. reflexivity. cbn.
    { intros; split; intros.
      - right. left. apply H.
      - destruct_or H; easy. }
    intros. instantiate (1 := fun _ _ _ => _). cbn beta.
    destruct H.
    eapply forward_simulation_plus with
      (match_states := fun s1 s2 => secret_match_state se1 s1 s2).
    - intros. inv H1. inv H.
      exists (st1 (init_c secret_program) L1 None).
      split; repeat constructor.
    - intros. inv H1. inv H. cbn in *. exists Int.zero.
      split; repeat constructor.
    - intros. inv H1. inv H. exists tt, (inr (write_query uryyb_bytes)).
      repeat apply conj; try repeat constructor.
      intros. inv H. inv H1.
      eexists. split. 2: constructor.
      repeat constructor.
    - intros. inv H; inv H1.
      + edestruct secret_init_mem as [m [Hm1 Hm2]]; eauto.
        edestruct main_block as [b [Hb1 Hb2]]; eauto.
        edestruct write_block as [b1 [Hb3 Hb4]]; eauto.
        edestruct msg_block as [b2 Hb5]; eauto.
        eexists. split. 2: constructor.
        eapply plus_left. (* init calls secret.c *)
        { eapply step_push.
          - econstructor; try reflexivity; eauto.
            apply Genv.find_invert_symbol; eauto.
          - constructor. econstructor; eauto.
            + constructor.
            + cbn. apply init_mem_nextblock in Hm1.
              rewrite Hm1. reflexivity. }
        2: { instantiate (1 := E0). reflexivity. }
        one_trivial_step. (* internal step of secret.c *)
        { eapply init_mem_alloc_flag. apply Hm1. }
        one_trivial_step. (* internal step of secret.c *)
        one_trivial_step. (* internal step of secret.c *)
        { unfold rw_type. crush_deref. }
        one_step. (* secret.c calls sys *)
        { eapply step2. eapply step_push.
          - econstructor. eauto.
          - eapply sys_c_initial_state_write; eauto. }
        eapply star_refl.
      + eexists. split. 2: constructor.
        eapply plus_left. (* sys returns to secret.c *)
        { eapply step2. eapply step_pop; econstructor. }
        2: { instantiate (1 := E0). reflexivity. }
        one_trivial_step. (* internal step of secret.c *)
        one_trivial_step. (* internal step of secret.c *)
        one_trivial_step. (* internal step of secret.c *)
        one_step. (* secret.c returns to init *)
        { eapply step_pop; repeat constructor. }
        eapply star_refl.
    - easy.
  Qed.

End SECRET_FSIM.

Definition rot13_rot13_id: positive := 1.
Definition rot13_main_id: positive := 2.
Definition rot13_read_id: positive := 3.
Definition rot13_write_id: positive := 4.
Definition rot13_rot13_c_id: positive := 5.
Definition rot13_main_buf_id: positive := 6.
Definition rot13_main_n_id: positive := 7.
Definition rot13_main_i_id: positive := 8.
Definition rot13_main_t_id: positive := 9.

Require Import Cop.

Definition rot13_rot13_body : statement :=
  let c := Evar rot13_rot13_c_id tchar in
  let i97 := Econst_int (Int.repr 97) tint in
  let i84 := Econst_int (Int.repr 84) tint in
  let i26 := Econst_int (Int.repr 26) tint in
  let c1 := Ebinop Osub c i84 tint in
  let c2 := Ebinop Omod c1 i26 tint in
  let c3 := Ebinop Oadd c2 i97 tint in
  Sreturn (Some c3).

Definition rot13_rot13 : function :=
  {|
    fn_return := tchar;
    fn_callconv := cc_default;
    fn_params := [ (rot13_rot13_c_id, tchar) ];
    fn_temps := [];
    fn_vars := [];
    fn_body := rot13_rot13_body;
  |}.

Definition rot13_type := Tfunction (Tcons tchar Tnil) tchar cc_default.

Program Definition rot13_main_body : statement :=
  let zero := Econst_int (Int.repr 0) tint in
  let one := Econst_int (Int.repr 1) tint in
  let n := Etempvar rot13_main_n_id tint in
  let i := Etempvar rot13_main_i_id tint in
  let t := Etempvar rot13_main_t_id tint in
  let buf := Evar rot13_main_buf_id (tarray tchar 100) in
  let buf_i := Ederef (Ebinop Oadd buf i tchar) tchar in
  let for_loop :=
    (* for i = 0; i < n; i++ *)
    Sfor (Sset rot13_main_i_id zero) (Ebinop Olt i n tint)
      (Ssequence
         (* t = rot13(buf[i]) *)
         (Scall (Some rot13_main_t_id) (Evar rot13_rot13_id rot13_type) [ buf_i ])
         (* buf[i] = t *)
         (Sassign buf_i t))
      (* i++ *)
      (Sset rot13_main_i_id (Ebinop Oadd i one tint))
  in
  let read_buf :=
    (* n = read(0, buf, sizeof buf) *)
    Scall (Some rot13_main_n_id) (Evar rot13_read_id rw_type) [ zero; buf; Esizeof (tarray tchar 100) tlong ]
  in
  let write_buf :=
    (* write(1, buf, n) *)
    Scall None (Evar rot13_write_id rw_type) [ one; buf; n ]
  in
  Ssequence read_buf (Ssequence for_loop (Ssequence write_buf (Sreturn (Some zero)))).

Definition rot13_main : function :=
  {|
    fn_return := tint;
    fn_callconv := cc_default;
    fn_params := [];
    fn_temps := [ (rot13_main_n_id, tint); (rot13_main_i_id, tint); (rot13_main_t_id, tint) ];
    fn_vars := [ (rot13_main_buf_id, tarray tchar 100) ];
    fn_body := rot13_main_body;
  |}.

Program Definition rot13_program : Clight.program :=
  {|
    prog_defs := [(rot13_rot13_id, Gfun (Internal rot13_rot13));
                  (rot13_main_id, Gfun (Internal rot13_main));
                  (rot13_read_id, Gfun read);
                  (rot13_write_id, Gfun write)];
    prog_public := [ rot13_main_id ];
    prog_main := Some rot13_main_id;
    prog_types := [];
    prog_comp_env := (PTree.empty _);
  |}.
Next Obligation. reflexivity. Qed.

Definition rot13_c : semantics (li_sys + li_sys) li_wp := load_c rot13_program.

Section ROT13_SPEC.

  Variant rot13_state :=
    | rot13_read0 | rot13_write0 (bytes: list byte) | rot13_ret0
    | rot13_read | rot13_write (bytes: list byte) | rot13_ret
    (* The first i bytes have been decoded. These intermediate steps correspond
       to internal steps in the loop of rot13.c, so that we don't have to do
       induction proof on the Clight loops *)
    | rot13_writei (bytes: list byte) (i: Z).

  Inductive rot13_spec_initial_state: query li_wp -> rot13_state -> Prop :=
  | rot13_spec_initial_state_intro q: rot13_spec_initial_state q rot13_read0.
  Inductive rot13_spec_at_external: rot13_state -> query (li_sys + li_sys) -> Prop :=
  | rot13_spec_at_external_read:
    rot13_spec_at_external rot13_read (inl (read_query (Int64.repr 100)))
  | rot13_spec_at_external_write bytes:
    rot13_spec_at_external (rot13_write bytes) (inr (write_query bytes)).
  Inductive rot13_spec_after_external: rot13_state -> reply (li_sys + li_sys) -> rot13_state -> Prop :=
  | rot13_spec_after_external_read bytes:
    Z.of_nat (length bytes) <= 100 ->
    rot13_spec_after_external rot13_read (inl (read_reply bytes)) (rot13_write0 bytes)
  | rot13_spec_after_external_write bytes n:
    rot13_spec_after_external (rot13_write bytes) (inr (write_reply n)) rot13_ret0.
  Inductive rot13_spec_final_state: rot13_state -> reply li_wp -> Prop :=
  | rot13_spec_final_state_intro: rot13_spec_final_state rot13_ret Int.zero.
  Inductive rot13_spec_step: rot13_state -> trace -> rot13_state -> Prop :=
  | rot13_spec_step1: rot13_spec_step rot13_read0 E0 rot13_read
  | rot13_spec_step2 bytes:
    rot13_spec_step (rot13_write0 bytes) E0 (rot13_writei bytes 0)
  | rot13_spec_stepi bytes bytes' i
      (HB: forall b, nth bytes (Z.to_nat i) b -> Byte.unsigned b >= 97):
    0 <= i < Z.of_nat (length bytes) ->
    nth_update bytes (Z.to_nat i) rot13_byte bytes' ->
    rot13_spec_step (rot13_writei bytes i) E0 (rot13_writei bytes' (i + 1))
  | rot13_spec_step3 bytes i:
    i = Z.of_nat (length bytes) ->
    rot13_spec_step (rot13_writei bytes i) E0 (rot13_write bytes)
  | rot13_spec_step4: rot13_spec_step rot13_ret0 E0 rot13_ret.

  Definition rot13_spec: semantics (li_sys + li_sys) li_wp :=
    {|
      activate se :=
        {|
          Smallstep.step _ := rot13_spec_step;
          Smallstep.initial_state := rot13_spec_initial_state;
          Smallstep.at_external := rot13_spec_at_external;
          Smallstep.after_external := rot13_spec_after_external;
          Smallstep.final_state := rot13_spec_final_state;
          Smallstep.globalenv := tt;
        |};
      skel := AST.erase_program rot13_program;
      footprint := AST.footprint_of_program rot13_program;
    |}.

End ROT13_SPEC.

Section ROT13_FSIM.

  Notation L1 := (comp_semantics' (semantics1 rot13_program) (sys_c rot13_program) (erase_program rot13_program)).
  Opaque semantics1.

  Lemma rot13_prog_defmap_main:
    (prog_defmap rot13_program) ! rot13_main_id =
      Some (Gfun (Internal rot13_main)).
  Proof. reflexivity. Qed.

  Lemma rot13_prog_defmap_read:
    (prog_defmap rot13_program) ! rot13_read_id = Some (Gfun read).
  Proof. reflexivity. Qed.

  Lemma rot13_prog_defmap_write:
    (prog_defmap rot13_program) ! rot13_write_id = Some (Gfun write).
  Proof. reflexivity. Qed.

  Lemma rot13_prog_defmap_rot13:
    (prog_defmap rot13_program) ! rot13_rot13_id = Some (Gfun (Internal rot13_rot13)).
  Proof. reflexivity. Qed.

  Lemma rot13_main_block se:
    Genv.valid_for (AST.erase_program rot13_program) se ->
    exists b, Genv.find_symbol (globalenv se rot13_program) rot13_main_id = Some b /\
           Genv.find_funct (globalenv se rot13_program) (Vptr b Ptrofs.zero) = Some (Internal rot13_main).
  Proof.
    intros Hse.
    exploit @Genv.find_def_symbol; eauto.
    intros [H _]. specialize (H rot13_prog_defmap_main).
    destruct H as (b & Hb1 & Hb2); eauto.
    exists b. split; eauto. eapply genv_funct_symbol; eauto.
  Qed.

  Lemma rot13_read_block se:
    Genv.valid_for (AST.erase_program rot13_program) se ->
    exists b, Genv.find_symbol (globalenv se rot13_program) rot13_read_id = Some b /\
           Genv.find_funct (globalenv se rot13_program) (Vptr b Ptrofs.zero) = Some read.
  Proof.
    intros Hse.
    exploit @Genv.find_def_symbol; eauto.
    intros [H _]. specialize (H rot13_prog_defmap_read).
    destruct H as (b & Hb1 & Hb2); eauto.
    exists b. split; eauto. eapply genv_funct_symbol; eauto.
  Qed.

  Lemma rot13_write_block se:
    Genv.valid_for (AST.erase_program rot13_program) se ->
    exists b, Genv.find_symbol (globalenv se rot13_program) rot13_write_id = Some b /\
           Genv.find_funct (globalenv se rot13_program) (Vptr b Ptrofs.zero) = Some write.
  Proof.
    intros Hse.
    exploit @Genv.find_def_symbol; eauto.
    intros [H _]. specialize (H rot13_prog_defmap_write).
    destruct H as (b & Hb1 & Hb2); eauto.
    exists b. split; eauto. eapply genv_funct_symbol; eauto.
  Qed.

  Lemma rot13_rot13_block se:
    Genv.valid_for (AST.erase_program rot13_program) se ->
    exists b, Genv.find_symbol (globalenv se rot13_program) rot13_rot13_id = Some b /\
           Genv.find_funct (globalenv se rot13_program) (Vptr b Ptrofs.zero) = Some (Internal rot13_rot13).
  Proof.
    intros Hse.
    exploit @Genv.find_def_symbol; eauto.
    intros [H _]. specialize (H rot13_prog_defmap_rot13).
    destruct H as (b & Hb1 & Hb2); eauto.
    exists b. split; eauto. eapply genv_funct_symbol; eauto.
  Qed.

  Lemma rot13_init_mem se:
    Genv.valid_for (erase_program rot13_program) se ->
    exists m, init_mem se (erase_program rot13_program) = Some m.
  Proof.
    intros Hvalid. eapply init_mem_exists; eauto.
    split; cbn in H; destruct_or H; inv H.
  Qed.

  Definition kont1 buf_block :=
    (Kcall (Some rot13_main_n_id) rot13_main (PTree.set rot13_main_buf_id (buf_block, Tarray tchar 100 noattr) empty_env)
       (PTree.set rot13_main_n_id Vundef
          (PTree.set rot13_main_i_id Vundef (PTree.set rot13_main_t_id Vundef (PTree.empty val))))
       (Kseq
          (Ssequence
             (Sfor (Sset rot13_main_i_id (Econst_int (Int.repr 0) tint))
                (Ebinop Olt (Etempvar rot13_main_i_id tint) (Etempvar rot13_main_n_id tint) tint)
                (Ssequence
                   (Scall (Some rot13_main_t_id) (Evar rot13_rot13_id rot13_type)
                      [Ederef
                         (Ebinop Oadd (Evar rot13_main_buf_id (Tarray tchar 100 noattr)) (Etempvar rot13_main_i_id tint)
                            tchar) tchar])
                   (Sassign
                      (Ederef
                         (Ebinop Oadd (Evar rot13_main_buf_id (Tarray tchar 100 noattr)) (Etempvar rot13_main_i_id tint)
                            tchar) tchar) (Etempvar rot13_main_t_id tint)))
                (Sset rot13_main_i_id (Ebinop Oadd (Etempvar rot13_main_i_id tint) (Econst_int (Int.repr 1) tint) tint)))
             (Ssequence
                (Scall None (Evar rot13_write_id rw_type)
                   [Econst_int (Int.repr 1) tint; Evar rot13_main_buf_id (Tarray tchar 100 noattr);
                    Etempvar rot13_main_n_id tint]) (Sreturn (Some (Econst_int (Int.repr 0) tint))))) Kstop)).

  Definition kont2 buf_block le :=
    (Kcall None rot13_main (PTree.set rot13_main_buf_id (buf_block, Tarray tchar 100 noattr) empty_env) le
                (Kseq (Sreturn (Some (Econst_int (Int.repr 0) tint))) Kstop)).

  Definition state_i buf_block le m :=
    State rot13_main
      (Sloop
         (Ssequence
            (Sifthenelse (Ebinop Olt (Etempvar rot13_main_i_id tint) (Etempvar rot13_main_n_id tint) tint) Sskip Sbreak)
            (Ssequence
               (Scall (Some rot13_main_t_id) (Evar rot13_rot13_id rot13_type)
                  [Ederef (Ebinop Oadd (Evar rot13_main_buf_id (Tarray tchar 100 noattr)) (Etempvar rot13_main_i_id tint) tchar)
                     tchar])
               (Sassign
                  (Ederef (Ebinop Oadd (Evar rot13_main_buf_id (Tarray tchar 100 noattr)) (Etempvar rot13_main_i_id tint) tchar)
                     tchar) (Etempvar rot13_main_t_id tint)))
         )
         (Sset rot13_main_i_id (Ebinop Oadd (Etempvar rot13_main_i_id tint) (Econst_int (Int.repr 1) tint) tint))
      )
      (Kseq
         (Ssequence
            (Scall None (Evar rot13_write_id rw_type)
               [Econst_int (Int.repr 1) tint; Evar rot13_main_buf_id (Tarray tchar 100 noattr); Etempvar rot13_main_n_id tint])
            (Sreturn (Some (Econst_int (Int.repr 0) tint)))) Kstop)
      (PTree.set rot13_main_buf_id (buf_block, Tarray tchar 100 noattr) empty_env)
      le m.

  Definition sys_st s1 s2 :=
    st2 (init_c rot13_program) L1 None
         (st2 (semantics1 rot13_program) (sys_c rot13_program) s1 s2).

  Definition c_st s :=
    st2 (init_c rot13_program) L1 None
         (st1 (semantics1 rot13_program) (sys_c rot13_program) s).

  Inductive rot13_match_state (se: Genv.symtbl): rot13_state -> Smallstep.state rot13_c -> Prop :=
  | rot13_match_state1:
    rot13_match_state se rot13_read0 (st1 (init_c rot13_program) L1 None)
  | rot13_match_state2 vf m args kont buf_block
    (HKONT: kont = kont1 buf_block)
    (HALLOC: Mem.alloc_flag m = true)
    (HPERM: Mem.range_perm m buf_block 0 100 Cur Freeable)
    (HVALID: Mem.valid_block m buf_block):
    rot13_match_state se rot13_read
      (sys_st (Callstate vf args kont m) (sys_read_query (Int64.repr 100) buf_block Ptrofs.zero m))
  | rot13_match_state3 vf m args kont bytes buf_block
    (HKONT: kont = kont1 buf_block)
    (HALLOC: Mem.alloc_flag m = true)
    (HPERM: Mem.range_perm m buf_block 0 100 Cur Freeable)
    (HVALID: Mem.valid_block m buf_block)
    (HLEN: Z.of_nat (length bytes) <= 100):
    rot13_match_state se (rot13_write0 bytes)
      (sys_st (Callstate vf args kont m) (sys_read_reply bytes buf_block Ptrofs.zero m))
  | rot13_match_state_i m bytes i buf_block len le
    (HLENEQ: len = Z.of_nat (length bytes)) (HI: i <= len) (HLEN: len <= 100)
    (HLB: Mem.loadbytes m buf_block 0 len = Some (map Byte bytes))
    (HALLOC: Mem.alloc_flag m = true)
    (HPERM: Mem.range_perm m buf_block 0 100 Cur Freeable)
    (HVALID: Mem.valid_block m buf_block)
    (HIEQ: le!rot13_main_i_id = Some (Vint (Int.repr i)))
    (HNEQ: le!rot13_main_n_id = Some (Vint (Int.repr len))):
    rot13_match_state se (rot13_writei bytes i)
      (c_st (state_i buf_block le m))
  | rot13_match_state4 vf m args kont bytes buf_block le
    (HPERM: Mem.range_perm m buf_block 0 100 Cur Freeable)
    (HKONT: kont = kont2 buf_block le):
    rot13_match_state se (rot13_write bytes)
      (sys_st (Callstate vf args kont m) (sys_write_query bytes m))
  | rot13_match_state5 vf m args kont n buf_block le
    (HPERM: Mem.range_perm m buf_block 0 100 Cur Freeable)
    (HKONT: kont = kont2 buf_block le):
    rot13_match_state se rot13_ret0
      (sys_st (Callstate vf args kont m) (sys_write_reply n m))
  | rot13_match_state6:
    rot13_match_state se rot13_ret (st1 (init_c rot13_program) L1 (Some Int.zero)).

  Lemma byte_val_casted byte:
    val_casted (Vint (Int.repr (Byte.unsigned byte))) tchar.
  Proof.
    constructor. cbn.
    unfold Int.zero_ext.
    rewrite Zbits.Zzero_ext_mod. 2: lia.
    pose proof (Byte.unsigned_range_2 byte) as Hx; cbn in Hx.
    rewrite Int.unsigned_repr.
    2: { unfold decode_int, rev_if_be. destruct Archi.big_endian; cbn; lia. }
    change (two_p 8) with 256.
    f_equal. rewrite Z.mod_small; lia.
  Qed.

  Lemma ptrofs_lemma1 i:
    0 <= i <= 100 ->
    Ptrofs.unsigned (Ptrofs.add Ptrofs.zero (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_intu (Int.repr i)))) = i.
  Proof.
    intros. rewrite Ptrofs.add_zero_l, Ptrofs.mul_commut, Ptrofs.mul_one.
    unfold Ptrofs.of_intu. unfold Ptrofs.of_int.
    rewrite Int.unsigned_repr. 2: cbn; lia.
    rewrite Ptrofs.unsigned_repr. reflexivity.
    unfold Ptrofs.max_unsigned. unfold Ptrofs.modulus.
    unfold Ptrofs.wordsize. unfold Wordsize_Ptrofs.wordsize.
    destruct Archi.ptr64; cbn; lia.
  Qed.

  Lemma byte_correct byte:
    Byte.ltu (Byte.repr 96) byte = true ->
    (Int.repr (Byte.unsigned (rot13_byte byte))) =
      (Int.zero_ext 8
          (Int.zero_ext 8
             (Int.add (Int.modu (Int.sub (Int.zero_ext 8 (Int.repr (Byte.unsigned byte))) (Int.repr 84)) (Int.repr 26))
                (Int.repr 97)))).
  Proof.
    intros H. unfold rot13_byte.
    rewrite Int.zero_ext_idem by lia.
    unfold Int.zero_ext. rewrite !Zbits.Zzero_ext_mod by lia.
    pose proof (Byte.unsigned_range_2 byte) as Hx; cbn in Hx.
    rewrite Int.unsigned_repr by (cbn; lia).
    repeat rewrite !Z.mod_small. all: change (two_p 8) with 256.
    2, 4: lia.
    2: {
      unfold Int.sub. rewrite !Int.unsigned_repr by (cbn; lia).
      assert (0 <= Byte.unsigned byte - 84 < 256).
      { unfold Byte.ltu in H. destruct zlt; inv H.
        rewrite Byte.unsigned_repr in l by (cbn; lia). lia. }
      unfold Int.modu. rewrite !Int.unsigned_repr by (cbn; lia).
      assert (0 <= (Byte.unsigned byte - 84) mod 26 < 256).
      { exploit (Z.mod_pos_bound (Byte.unsigned byte - 84) 26). lia. lia. }
      unfold Int.add. rewrite !Int.unsigned_repr. all: try (cbn; lia).
      2: { rewrite !Int.unsigned_repr by (cbn; lia). cbn. lia. }
    exploit (Z.mod_pos_bound (Byte.unsigned byte - 84) 26). lia. lia.
    }
    f_equal.
    unfold Int.sub. rewrite !Int.unsigned_repr by (cbn; lia).
    unfold Byte.sub. rewrite Byte.unsigned_repr by (cbn; lia).
    assert (0 <= Byte.unsigned byte - 84 < 256).
    { unfold Byte.ltu in H. destruct zlt; inv H.
      rewrite Byte.unsigned_repr in l by (cbn; lia). lia. }
    unfold Int.modu. rewrite !Int.unsigned_repr by (cbn; lia).
    unfold Byte.modu. rewrite !Byte.unsigned_repr by (cbn; lia).
    assert (0 <= (Byte.unsigned byte - 84) mod 26 < 256).
    { exploit (Z.mod_pos_bound (Byte.unsigned byte - 84) 26). lia. lia. }
    unfold Int.add. rewrite !Int.unsigned_repr. all: try (cbn; lia).
    2: { rewrite !Int.unsigned_repr by (cbn; lia). cbn. lia. }
    unfold Byte.add. rewrite !Byte.unsigned_repr. all: try (cbn; lia).
    rewrite !Byte.unsigned_repr by (cbn; lia). cbn. split; try lia.
    exploit (Z.mod_pos_bound (Byte.unsigned byte - 84) 26). lia. lia.
  Qed.

  Lemma rot13_fsim: forward_simulation 1 1 rot13_spec rot13_c.
  Proof.
    constructor. econstructor. reflexivity. cbn.
    { intros; split; intros.
      - right. left. apply H.
      - destruct_or H; easy. }
    intros. instantiate (1 := fun _ _ _ => _). cbn beta.
    destruct H.
    eapply forward_simulation_plus with
      (match_states := fun s1 s2 => rot13_match_state se1 s1 s2).
    - intros. inv H1. inv H.
      exists (st1 (init_c rot13_program) L1 None).
      split; repeat constructor.
    - intros. inv H1. inv H. cbn in *. exists Int.zero.
      split; repeat constructor.
    - intros. inv H; inv H1.
      + exists tt, (inl (read_query (Int64.repr 100))).
        repeat apply conj; try repeat constructor.
        intros. inv H. inv H1.
        eexists. split. 2: econstructor; eauto. repeat constructor; eauto.
      + exists tt, (inr (write_query bytes)).
        repeat apply conj; try repeat constructor.
        intros. inv H. inv H1.
        eexists. split. 2: econstructor; eauto. repeat constructor.
    - intros. inv H; inv H1.
      (* transition to the call to read *)
      + edestruct rot13_init_mem as [m Hm]; eauto.
        edestruct rot13_main_block as [b [Hb1 Hb2]]; eauto.
        edestruct rot13_read_block as [b1 [Hb3 Hb4]]; eauto.
        exploit init_mem_alloc_flag; eauto. intros Hflag.
        edestruct (@Mem.alloc_succeed m 0 100); eauto. destruct x as (m1 & b2).
        eexists. split.
        2: { econstructor. eauto.
             (* alloc_flag *)
             - eapply Mem.alloc_flag_alloc2; eauto.
             (* range_perm *)
             - intros p Hperm. eapply Mem.perm_alloc_2 in e; eauto.
             (* valid_block *)
             - eapply Mem.valid_new_block; eauto. }
        eapply plus_left. (* init calls rot13.c *)
        { eapply step_push.
          - econstructor; try reflexivity; eauto.
            eapply Genv.find_invert_symbol. eauto.
          - constructor. econstructor; eauto.
            + constructor.
            + cbn. apply init_mem_nextblock in Hm.
              rewrite Hm. reflexivity. }
        2: { instantiate (1 := E0). reflexivity. }
        one_step. (* internal step of rot13.c: Callstate *)
        { eapply step2. eapply step1; crush_step; try solve [ constructor | easy ].
          - solve_list_norepet.
          - repeat econstructor. eauto. }
        one_trivial_step. (* internal step of rot13.c: Ssequence *)
        one_trivial_step. (* internal step of rot13.c: Scall *)
        { unfold rw_type. crush_deref. }
        one_step. (* rot13.c calls read to sys *)
        { eapply step2. eapply step_push; repeat econstructor; eauto. }
        eapply star_refl.
      (* enter the loop *)
      + edestruct (Mem.range_perm_storebytes m buf_block 0 (map Byte bytes)) as (m1 & Hm1).
        { (* range_perm *)
          intros p Hperm. eapply Mem.perm_implies. apply HPERM.
          rewrite map_length in Hperm. lia. auto with mem. }
        eexists. split.
        eapply plus_left. (* sys returns to rot13.c, and storebytes "uryyb" *)
        { eapply step2. eapply step_pop; econstructor; eauto. }
        2: { instantiate (1 := E0). reflexivity. }
        one_trivial_step. (* internal step of rot13.c: Returnstate *)
        one_trivial_step. (* internal step of rot13.c: Sskip *)
        one_trivial_step. (* internal step of rot13.c: Ssequence *)
        one_step. (* internal step of rot13.c: Sfor *)
        { eapply step2. eapply step1. unfold Sfor. crush_step. }
        one_trivial_step. (* internal step of rot13.c: Sset *)
        one_trivial_step. (* internal step of rot13.c: Sskip *)
        rewrite PTree.set2. eapply star_refl.
        { econstructor; eauto; try lia.
          (* loadbytes *)
          - apply Mem.loadbytes_storebytes_same in Hm1.
            rewrite map_length in Hm1. apply Hm1.
          - erewrite Mem.storebytes_alloc_flag; eauto.
          - intros p Hp. eauto with mem.
          - eauto with mem. }
      (* looping *)
      + edestruct rot13_rot13_block as [b [Hb1 Hb2]]; eauto.
        edestruct loadbyte as (byte & Hbyte & Hload); eauto.
        edestruct (Mem.alloc_succeed m 0 1) as ((m1 & b1) & Hmb); eauto.
        assert (exists m2, Mem.store Mint8unsigned m1 b1 0 (Vint (Int.repr (Byte.unsigned byte))) = Some m2)
                 as (m2 & Hm2).
        { edestruct Mem.valid_access_store as (m2 & Hm2); eauto. split; cbn.
          - intros p Hp. eapply Mem.perm_alloc_2 in Hmb.
            eapply Mem.perm_implies; eauto. auto with mem. lia.
          - apply Z.divide_1_l. }
        assert (exists m3,   Mem.free_list m2 [(b1, 0, 1)] = Some m3) as (m3 & Hm3).
        { edestruct Mem.range_perm_free as (m3 & Hm3).
          2: cbn; eexists; rewrite Hm3; eauto.
          intros p Hp. eauto with mem. }
        assert (exists m4, Mem.store Mint8unsigned m3 buf_block i (Vint (Int.repr (Byte.unsigned (rot13_byte byte)))) = Some m4)
                 as (m4 & Hm4).
        { edestruct Mem.valid_access_store as (m4 & Hm4); eauto. split; cbn.
          - intros p Hp. cbn in Hm3. destruct Mem.free eqn: Hfree; inv Hm3.
            eapply Mem.perm_free_1; eauto. left.
            intros Hb. subst. eapply Mem.fresh_block_alloc; eauto.
            eapply Mem.perm_store_1; eauto.
            eapply Mem.perm_alloc_1; eauto.
            eapply Mem.perm_implies; eauto. apply HPERM. lia. auto with mem.
          - apply Z.divide_1_l. }
        eexists. split.
        eapply plus_left. (* internal step of rot13.c: Sloop *)
        { eapply step2. eapply step1. unfold state_i. crush_step. }
        2: { instantiate (1 := E0). reflexivity. }
        one_trivial_step. (* internal step of rot13.c: Ssequence *)
        one_trivial_step. (* internal step of rot13.c: Sifthenelse *)
        { instantiate (1 := true). destruct Int.ltu eqn: Hltu.
          - reflexivity.
          - exfalso. unfold Int.ltu in Hltu. destruct zlt; try easy.
            rewrite !Int.unsigned_repr in g; cbn; lia. }
        one_trivial_step. (* internal step of rot13.c: Sskip *)
        one_trivial_step. (* internal step of rot13.c: Ssequence *)
        one_step. (* internal step of rot13.c: Scall *)
        { eapply step2. eapply step1; crush_step; crush_expr.
          - apply deref_loc_reference. reflexivity.
          - rewrite ptrofs_lemma1 by lia. apply Hload.
          - apply byte_val_casted. }
        one_step. (* internal step of rot13.c: call rot13 *)
        { eapply step2. eapply step1; crush_step; crush_expr.
          - solve_list_norepet.
          - econstructor. apply Hmb. constructor.
          - econstructor.
            + reflexivity.
            + eapply assign_loc_value. reflexivity. cbn. apply Hm2.
            + constructor. }
        one_step. (* internal step of rot13: rot13 returns *)
        { eapply step2. eapply step1; crush_step; crush_expr.
          - eapply Mem.load_store_same; eauto.
          - crush_expr.
          - crush_expr.
          - crush_expr.
          - cbn. reflexivity. }
        one_trivial_step. (* internal step of rot13.c: Returnstate *)
        one_trivial_step. (* internal step of rot13.c: Sskip *)
        one_step.
        { eapply step2. eapply step1. crush_step; crush_expr.
          rewrite ptrofs_lemma1 by lia.
          rewrite <- byte_correct.
          2: { specialize (HB _ Hbyte).
               unfold Byte.ltu. destruct zlt; try easy.
               rewrite Byte.unsigned_repr in g; try (cbn; lia). }
          apply Hm4. }
        one_trivial_step. (* internal step of rot13.c: Sskip *)
        one_trivial_step. (* internal step of rot13.c: Sset *)
        one_trivial_step. (* internal step of rot13.c: Sskip *)
        apply star_refl.
        { econstructor; eauto with mem.
          - erewrite <- nth_update_length; eauto. lia.
          - erewrite <- nth_update_length; eauto.
          - eapply storebyte; eauto. all: erewrite <- nth_update_length; eauto.
            cbn in Hm3. destruct Mem.free eqn: Hfree; inv Hm3.
            assert (buf_block <> b1).
            { intros Hb. subst. eapply Mem.fresh_block_alloc; eauto. }
            erewrite Mem.loadbytes_free. 2-3: eauto.
            erewrite Mem.loadbytes_store_other. 2-3: eauto.
            erewrite Mem.loadbytes_alloc_unchanged; eauto.
          - erewrite Mem.store_alloc_flag. 2: eauto.
            cbn in Hm3. destruct Mem.free eqn: Hfree; inv Hm3.
            erewrite Mem.free_alloc_flag. 2: eauto.
            erewrite Mem.store_alloc_flag. 2: eauto.
            eapply Mem.alloc_flag_alloc2; eauto.
          - intros p Hp.
            eapply Mem.perm_store_1; eauto.
            cbn in Hm3. destruct Mem.free eqn: Hfree; inv Hm3.
            eapply Mem.perm_free_1; eauto. left.
            intros Hb. subst. eapply Mem.fresh_block_alloc; eauto.
            eapply Mem.perm_store_1; eauto.
            eapply Mem.perm_alloc_1; eauto.
          - rewrite PTree.gss. f_equal. f_equal.
            unfold Int.add. f_equal.
            rewrite !Int.unsigned_repr; cbn; lia.
          - do 2 rewrite PTree.gso by easy. rewrite HNEQ.
            do 4 f_equal. eapply nth_update_length; eauto. }
      (* exiting the loop and proceed to call write *)
      + edestruct rot13_write_block as [b1 [Hb3 Hb4]]; eauto.
        eexists. split.
        eapply plus_left. (* internal step of rot13.c: Sloop *)
        { eapply step2. eapply step1. unfold state_i. crush_step. }
        2: { instantiate (1 := E0). reflexivity. }
        one_trivial_step. (* internal step of rot13.c: Ssequence *)
        one_trivial_step. (* internal step of rot13.c: Sifthenelse *)
        { instantiate (1 := false). destruct Int.ltu eqn: Hltu.
          - exfalso. unfold Int.ltu in Hltu.
            destruct zlt; try solve [easy | lia].
          - cbn. reflexivity. }
        one_trivial_step. (* internal step of rot13.c: Sbreak *)
        one_trivial_step. (* internal step of rot13.c: Sbreak *)
        one_trivial_step. (* internal step of rot13.c: Sskip *)
        one_trivial_step. (* internal step of rot13.c: Ssequence *)
        one_trivial_step. (* internal step of rot13.c: Scall *)
        { unfold rw_type. crush_deref. }
        one_step. (* rot13.c call sys *)
        { rewrite Int.unsigned_repr by (cbn; lia).
          eapply step2. eapply step_push.
          - econstructor. eauto.
          - eapply sys_c_initial_state_write; eauto. }
        eapply star_refl.
        { econstructor; eauto. reflexivity. }
      (* return from sys *)
      + assert (exists m1, Mem.free_list m [(buf_block, 0, 100%Z)] = Some m1) as (m1 & Hm1).
        { edestruct Mem.range_perm_free as (m1 & Hm1).
          2: cbn; eexists; rewrite Hm1; eauto.
          intros p Hp. eauto with mem. }
        eexists. split. 2: constructor.
        eapply plus_left. (* sys returns to rot13.c *)
        { eapply step2. eapply step_pop; constructor. }
        2: { instantiate (1 := E0). reflexivity. }
        one_trivial_step. (* internal step of rot13.c: Returnstate *)
        one_trivial_step. (* internal step of rot13.c: Sskip *)
        one_trivial_step. (* internal step of rot13.c: Sreturn *)
        one_step. (* rot13 returns to init *)
        { eapply step_pop; repeat econstructor. }
        eapply star_refl.
    - easy.
  Qed.

End ROT13_FSIM.

Section HELLO_SPEC.

  (* The redundant internal step makes the simulation easier. *)
  Variant hello_state :=
    | hello1 | hello2 | hello3 | hello4.
  Inductive hello_spec_initial_state: query li_wp -> hello_state -> Prop :=
  | hello_spec_initial_state_intro q: hello_spec_initial_state q hello1.
  Inductive hello_spec_at_external: hello_state -> query (li_sys + li_sys) -> Prop :=
  | hello_spec_at_external_intro bytes:
    bytes = hello_bytes ->
    hello_spec_at_external hello2 (inr (write_query bytes)).
  Inductive hello_spec_after_external: hello_state -> reply (li_sys + li_sys) -> hello_state -> Prop :=
  | hello_spec_after_external_intro n:
    hello_spec_after_external hello2 (inr (write_reply n)) hello3.
  Inductive hello_spec_final_state: hello_state -> reply li_wp -> Prop :=
  | hello_spec_final_state_intro: hello_spec_final_state hello4 Int.zero.
  Inductive hello_spec_step: hello_state -> trace -> hello_state -> Prop :=
  | hello_spec_step1: hello_spec_step hello1 E0 hello2
  | hello_spec_step2: hello_spec_step hello3 E0 hello4.

  Context (hello_skel: AST.program unit unit).
  Definition hello_spec: semantics (li_sys + li_sys) li_wp :=
    {|
      activate se :=
        {|
          Smallstep.step _ := hello_spec_step;
          Smallstep.initial_state := hello_spec_initial_state;
          Smallstep.at_external := hello_spec_at_external;
          Smallstep.after_external := hello_spec_after_external;
          Smallstep.final_state := hello_spec_final_state;
          Smallstep.globalenv := tt;
        |};
      skel := hello_skel;
      footprint i := footprint_of_program secret_program i \/ footprint_of_program rot13_program i;
    |}.
  Definition encap_hello_spec: li_sys + li_sys +-> li_wp := semantics_embed hello_spec.

End HELLO_SPEC.

Section PIPE_CORRECT.

  Context (hello_skel: AST.program unit unit).

  Notation L1 :=
        (TensorComp.semantics_map (comp_semantics' seq (with_semantics secret_spec rot13_spec hello_skel) hello_skel)
           TensorComp.lf (TensorComp.li_iso_inv TensorComp.li_iso_unit) @ pipe_state)%lts.

  Inductive pipe_match_state: hello_state -> Smallstep.state (pipe secret_spec rot13_spec hello_skel) -> Prop :=
  | pipe_match_state1 buf:
    pipe_match_state hello1
      (st1 L1 pipe_operator (st1 seq (with_semantics secret_spec rot13_spec hello_skel) seq1, buf))
  | pipe_match_state2 buf:
    pipe_match_state hello2
      (st2 L1 pipe_operator
         (st2 seq (with_semantics secret_spec rot13_spec hello_skel) seq2 (inr (rot13_write hello_bytes)), buf)
         (pipe2_write_query hello_bytes []))
  | pipe_match_state3 buf n:
    pipe_match_state hello3
      (st2 L1 pipe_operator
         (st2 seq (with_semantics secret_spec rot13_spec hello_skel) seq2 (inr (rot13_write hello_bytes)), buf)
         (pipe2_write_reply n []))
  | pipe_match_state4:
    pipe_match_state hello4
      (st1 L1 pipe_operator (st1 seq (with_semantics secret_spec rot13_spec hello_skel) (ret Int.zero), [])).

  Local Opaque app.

  Lemma pipe_spec_correct: E.forward_simulation
                           &1 &1 (encap_hello_spec hello_skel) (pipe secret_spec rot13_spec hello_skel).
  Proof.
    apply st_normalize_fsim. constructor.
    eapply ST.Forward_simulation with
          (ltof _ (fun (_: unit) => 0%nat))
          (fun _se1 _se2 _wb _sa _sb _i s1 s2 => pipe_match_state s1 s2)
          (fun _ _ => True);
          try easy. intros; cbn. firstorder.
    intros. constructor.
    - intros. cbn in *. eprod_crush. inv H4.
      eexists tt, (st1 L1 _ (_, _)). split. repeat constructor; eauto.
      eexists tt, (tt, (tt, (tt, p0))). split; repeat constructor; eauto.
    - intros. cbn in *. eprod_crush. inv H3. inv H2.
      exists (Int.zero, (tt, [])). split.
      * exists (Int.zero, tt, []). split; repeat constructor; eauto.
        cbn. exists Int.zero. split; repeat constructor.
      * exists (tt, (tt, (tt, []))). split; repeat constructor; eauto.
    - intros. cbn in *. eprod_crush. inv H3. unfold id in H5. subst. inv H2.
      exists (inr (write_query hello_bytes)). split.
      * repeat constructor.
      * exists tt, tt. repeat split; eauto.
        destruct H3 as (r' & Hr1 & Hr2). unfold id in Hr1. subst. inv Hr2.
        exists (st2 L1 pipe_operator
             (st2 seq (with_semantics secret_spec rot13_spec hello_skel) seq2 (inr (rot13_write hello_bytes)), buf)
             (pipe2_write_reply n [])). split.
        -- exists (inr (write_reply n)). split; eauto. repeat constructor.
        -- exists tt, (tt, (tt, (tt, buf))). split; repeat constructor.
    - intros. cbn in *. eprod_crush. exists tt. inv H2; inv H3.
      * eexists (st2 L1 pipe_operator
                   (st2 seq (with_semantics secret_spec rot13_spec hello_skel) seq2 (inr (rot13_write hello_bytes)), [])
                   (pipe2_write_query hello_bytes [])).
        split.
        -- left. eapply plus_left. (* seq calls secret *)
           { repeat econstructor. instantiate (1 := (_, _)). split; eauto.
             eapply step_push; repeat constructor. }
           2: { instantiate (1 := E0). reflexivity. }
           one_step. (* secret internal step *)
           { eapply step1. instantiate (1 := (_, _)). split; eauto.
             apply step2. repeat constructor. }
           one_step. (* secret calls write to pipe *)
           { eapply step_push.
             instantiate (1 := (_, _)). repeat constructor. constructor. }
           one_step. (* pipe returns to secret *)
           { eapply step_pop. repeat constructor.
             instantiate (1 := (_, _)). repeat constructor; cbn.
             eexists. split; eauto. reflexivity.
             repeat constructor. }
           one_step. (* secret internal step *)
           { eapply step1. instantiate (1 := (_, _)). split; eauto.
             apply step2. repeat constructor. }
           one_step. (* secret returns to seq *)
           { repeat econstructor. instantiate (1 := (_, _)). split; eauto.
             eapply step_pop; repeat constructor. }
           one_step. (* seq calls rot13 *)
           { repeat econstructor. instantiate (1 := (_, _)). split; eauto.
             eapply step_push; repeat constructor. }
           one_step. (* rot13 internal step *)
           { eapply step1. instantiate (1 := (_, _)). split; eauto.
             apply step2. repeat constructor. }
           one_step. (* rot13 calls read to pipe *)
           { eapply step_push.
             instantiate (1 := (_, _)). repeat constructor. constructor. }
           one_step. (* pipe returns to rot13 *)
           { eapply step_pop. repeat constructor.
             cbn. rewrite Int64.unsigned_repr; cbn; try lia.
             instantiate (1 := (_, _)). repeat constructor; cbn.
             eexists. split; eauto. reflexivity.
             repeat constructor. cbn. lia. }
           (* entering the loop *)
           one_step.
           { eapply step1. instantiate (1 := (_, _)). split; eauto.
             apply step2. repeat constructor. }
           (* loop 5 times to decode the buffer *)
           one_step.
           { eapply step1. instantiate (1 := (_, _)). split; eauto.
             apply step2. repeat constructor.
             intros b Hb. inv Hb.
             rewrite Byte.unsigned_repr by (cbn; lia). all: lia. }
           one_step.
           { eapply step1. instantiate (1 := (_, _)). split; eauto.
             apply step2. repeat constructor.
             intros b Hb. inv Hb. inv H5.
             rewrite Byte.unsigned_repr by (cbn; lia). all: lia. }
           one_step.
           { eapply step1. instantiate (1 := (_, _)). split; eauto.
             apply step2. repeat constructor.
             intros b Hb. inv Hb. inv H5. inv H6.
             rewrite Byte.unsigned_repr by (cbn; lia). all: lia. }
           one_step.
           { eapply step1. instantiate (1 := (_, _)). split; eauto.
             apply step2. repeat constructor.
             intros b Hb. inv Hb. inv H5. inv H6. inv H5.
             rewrite Byte.unsigned_repr by (cbn; lia). all: lia. }
           one_step.
           { eapply step1. instantiate (1 := (_, _)). split; eauto.
             apply step2. repeat constructor.
             intros b Hb. inv Hb. inv H5. inv H6. inv H5. inv H6.
             rewrite Byte.unsigned_repr by (cbn; lia). all: lia. }
           (* exit loop *)
           one_step.
           { eapply step1. instantiate (1 := (_, _)). split; eauto.
             apply step2. constructor. apply rot13_spec_step3.
             reflexivity. }
           one_step. (* rot13 calls write to pipe *)
           { eapply step_push.
             instantiate (1 := (_, _)). repeat constructor. constructor. }
           apply star_refl.
        -- exists tt, (tt, (tt, (tt, buf))). split; repeat constructor.
      * exists (st1 L1 pipe_operator (st1 seq (with_semantics secret_spec rot13_spec hello_skel) (ret Int.zero), [])).
        split.
        -- left. eapply plus_left. (* pipe returns to rot13 *)
           { eapply step_pop. repeat constructor.
             instantiate (1 := (_, _)). repeat constructor; cbn.
             eexists. split; eauto. reflexivity.
             repeat constructor. }
           2: { instantiate (1 := E0). reflexivity. }
           one_step. (* rot13 internal step *)
           { eapply step1. instantiate (1 := (_, _)). split; eauto.
             apply step2. repeat constructor. }
           one_step. (* rot13 returns to seq *)
           { repeat econstructor. instantiate (1 := (_, _)). split; eauto.
             eapply step_pop; repeat constructor. }
           apply star_refl.
        -- exists tt, (tt, (tt, (tt, buf))). split; repeat constructor.
  Qed.

End PIPE_CORRECT.

Require Import Compiler.
Require Import CallconvAlgebra.

Lemma wp_match_senv_refl: forall se, wp_match_senv se se.
Proof.
  intros. red.
  split. intros; reflexivity.
  split. intros; reflexivity.
  intros; reflexivity.
Qed.

Lemma cc_wp_id_ref: @CallconvAlgebra.ccref (with_ li_sys li_sys) _ 1 cc_wp_id.
Proof.
  red. intros * Hse Hq. inv Hse. inv Hq.
  exists tt. split. apply wp_match_senv_refl.
  repeat apply conj; eauto.
  all: destruct q2; destruct q; eauto.
Qed.

(* TODO: move this lemma to Encapsulation.v *)
Instance st_cc_compose_ref li1 li2 li3:
  Proper (st_ccref ++> st_ccref ++> st_ccref) (@ST.cc_compose li1 li2 li3).
Proof.
    intros cc12 cc12' H12 cc23 cc23' H23. unfold st_ccref.
    exploit @st_fsim_vcomp. apply H12. apply H23. intros HX. apply HX.
Qed.

Section CCREF.

  Lemma cc_wp_id_ref_idemp:
    st_ccref (ST.cc_compose & (cc_wp_id) & (cc_wp_id))
      &(@cc_wp_id (with_ li_sys li_sys)).
  Proof.
    unfold st_ccref. apply st_normalize_fsim. constructor.
    eapply ST.Forward_simulation with
      (ltof _ (fun (_: unit) => 0%nat))
      (fun se1 se2 w0 _ w2 _ => eq)
      (fun _ _ => True); try easy.
    intros. cbn in *. eprod_crush.
    constructor; cbn; intros; eprod_crush; try easy.
    - inv H5. eexists tt, _. split. constructor.
      eexists tt, (tt, tt). repeat split; eauto.
    - inv H4. exists r1. split. econstructor.
      exists (tt, tt). repeat split; eauto.
    - inv H4. exists q1. split. econstructor.
      exists tt, tt. split; eauto. split; eauto. split.
      destruct q1; eauto.
      split.
      { destruct H as [A [B C]].
        destruct H2 as [A' [B' C']].
        repeat apply conj.
        - intros. congruence.
        - intros. rewrite B. easy.
        - intros. rewrite C. easy. }
      intros. inv H5. eexists tt, _.
      split. constructor.
      exists tt, (tt, tt). repeat split; eauto.
  Qed.

End CCREF.

Section HELLO.
  Context (hello_skel: AST.program unit unit).
  Hypothesis (Hskel1: Linking.linkorder (AST.erase_program secret_program) hello_skel).
  Hypothesis (Hskel2: Linking.linkorder (AST.erase_program rot13_program) hello_skel).

  Lemma Hskel1': Linking.linkorder (skel (load_c secret_program)) hello_skel.
  Proof. apply Hskel1. Qed.
  Lemma Hskel2': Linking.linkorder (skel (load_c rot13_program)) hello_skel.
  Proof. apply Hskel2. Qed.
  Lemma Hskel1'': Linking.linkorder (skel secret_spec) hello_skel.
  Proof. apply Hskel1. Qed.
  Lemma Hskel2'': Linking.linkorder (skel rot13_spec) hello_skel.
  Proof. apply Hskel2. Qed.

  Hypothesis (Hwin64: Archi.win64 = false).

  Lemma secret_fsim': forward_simulation cc_wp_id 1 secret_spec secret_c.
  Proof.
    eapply open_fsim_ccref. apply cc_wp_id_ref. reflexivity.
    apply secret_fsim.
  Qed.
  Lemma rot13_fsim': forward_simulation cc_wp_id 1 rot13_spec rot13_c.
  Proof.
    eapply open_fsim_ccref. apply cc_wp_id_ref. reflexivity.
    apply rot13_fsim.
  Qed.

  Hypothesis
    (Hromatch1: forall (se : Genv.symtbl) (m : mem),
        init_mem se (erase_program secret_program) = Some m ->
        ValueAnalysis.romatch_all se (VAInject.bc_of_symtbl se) m).
  Hypothesis
    (Hromatch2: forall (se : Genv.symtbl) (m : mem),
        init_mem se (erase_program rot13_program) = Some m ->
        ValueAnalysis.romatch_all se (VAInject.bc_of_symtbl se) m).

  Lemma hello_correct secret_asm rot13_asm:
    transf_clight_program secret_program = Errors.OK secret_asm ->
    transf_clight_program rot13_program = Errors.OK rot13_asm ->
    E.forward_simulation
    &cc_wp_id &1 (encap_hello_spec hello_skel)
          (pipe (load_asm secret_asm) (load_asm rot13_asm) hello_skel).
  Proof.
    intros A B.
    apply load_c_asm in A; auto. apply load_c_asm in B; eauto.
    exploit @pipe_fsim. apply Hskel1'. apply Hskel2'.
    apply A. apply B. intros X.
    pose proof pipe_spec_correct as Y.
    pose proof secret_fsim' as A1.
    pose proof rot13_fsim' as B1.
    exploit @pipe_fsim. apply Hskel1''. apply Hskel2''.
    apply A1. apply B1. intros Z.
    exploit @encap_fsim_vcomp. apply Y. apply Z. intros YZ.
    exploit @encap_fsim_vcomp. apply YZ. apply X. intros XYZ.
    do 2 rewrite <- ccref_right_unit1 in XYZ.
    rewrite ccref_left_unit2 in XYZ.
    rewrite cc_wp_id_ref_idemp in XYZ. apply XYZ.
  Qed.

End HELLO.
