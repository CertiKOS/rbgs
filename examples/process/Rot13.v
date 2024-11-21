Require Import Classical.
Require Import Program.Equality.
Require Import LogicalRelations.
Require Import Poset.
Require Import Lattice.
Require Import Downset.
Require Import IntStrat.
Require Import Classical_Prop.
Require Import Coqlib.
Require Import Determ.

From compcert.common Require Import Smallstep Globalenvs.
Require LanguageInterface.
Import -(notations) LanguageInterface.
Require Import Asm.
Import Memory Values Integers ListNotations.
Require Import CompCertStrat Load.
Import Load.STRAT.
Close Scope list.
Close Scope Z_scope.

Obligation Tactic := idtac.

(** * §6.3 Modeling loading and the execution environments *)

(** This file contains the verification of the secret and rot13 example using
    the strategy framework presented in the paper.

    We made one simplification to the example presented in the paper: we used
    the shorted string "hello" instead of "hello, world!" so that we don't have
    to deal with rot13 encoding on non-ascii characters. This simplified things
    because proving numeric calculations in CompCert is thorny due to the
    convertion among various representations of integers/bytes/nats.

*)

Axiom (Hwin: Archi.win64 = false).
Notation hello_bytes := [ Byte.repr 104; Byte.repr 101; Byte.repr 108; Byte.repr 108; Byte.repr 111 ]%list.
Notation uryyb_bytes := [ Byte.repr 117; Byte.repr 114; Byte.repr 121; Byte.repr 121; Byte.repr 98]%list.

(** ** Strategy-level definitions *)

Arguments compose_when {E F G}%esig_scope {i j k} p (σ τ)%strat_scope.

(** The strategy level specification of the overall execution Γ_(1), the secret
    module Γ_secret, and the Γ_decode. *)

Section STRATEGY.
  Obligation Tactic := cbn.
  Context (sk_secret sk_decode: AST.program unit unit).

  (** *** Example 2.4 (Command Specifications) *)
  Definition Γ_play se : @play S P ready :=
    @oq S P se ::
      @pq S P se (inr (F_write hello_bytes)) ::
      @oa S P se (inr (F_write hello_bytes)) (Int.repr 5) ::
      @pa S P se (Int.repr 0) :: pnil_ready.
  Definition Γ : S ->> P := sup { se | Genv.valid_for sk_secret se /\ Genv.valid_for sk_decode se }, down (Γ_play se).
  Definition Γ_secret_play se : @play S P ready :=
    @oq S P se ::
      @pq S P se (inr (F_write uryyb_bytes)) ::
      @oa S P se (inr (F_write uryyb_bytes)) (Int.repr 5) ::
      @pa S P se (Int.repr 0) :: pnil_ready.
  Definition Γ_secret : S ->> P := sup { se | Genv.valid_for sk_secret se }, down (Γ_secret_play se).
  Definition Γ_decode_play se : @play S P ready :=
    @oq S P se ::
      @pq S P se (inl (F_read (Int.repr 100))) ::
      @oa S P se (inl (F_read (Int.repr 100))) uryyb_bytes ::
      @pq S P se (inr (F_write hello_bytes)) ::
      @oa S P se (inr (F_write hello_bytes)) (Int.repr 5) ::
      @pa S P se (Int.repr 0) :: pnil_ready.
  Definition Γ_decode : S ->> P := sup { se | Genv.valid_for sk_decode se }, down (Γ_decode_play se).

  (** *** Example 2.11 (Composing processes) *)
  Definition seq_play se n1 n2: @play (P + P) P ready :=
    @oq (P+P) P se ::
      @pq (P+P) P se (inl se) ::
      @oa (P+P) P se (inl se) n1 ::
      @pq (P+P) P se (inr se) ::
      @oa (P+P) P se (inr se) n2 ::
      @pa (P+P) P se n2 :: pnil_ready.
  Definition seq : P + P ->> P := sup se, sup n1, sup n2, down (seq_play se n1 n2).

  Inductive fifo_play: list byte -> forall i, @play 0 F i -> Prop :=
  | fifo_nil d : fifo_play d ready pnil_ready
  | fifo_read n d1 d2 d s
      (Hd: d = app d1 d2) (Hn: Int.unsigned n = Z.of_nat (length d1)) (Hs: fifo_play d2 ready s):
    fifo_play d ready (@oq 0 F (F_read n) :: @pa 0 F (F_read n) d1 :: s)
  | fifo_read_all n d s (Hn: (Int.unsigned n > Z.of_nat (length d))%Z) (Hs: fifo_play nil ready s):
    fifo_play d ready (@oq 0 F (F_read n) :: @pa 0 F (F_read n) d :: s)
  | fifo_write n d1 d2 d s
      (Hd: d2 = app d d1) (Hn: Int.unsigned n = Z.of_nat (length d1)) (Hs: fifo_play d2 ready s):
    fifo_play d ready (@oq 0 F (F_write d1) :: @pa 0 F (F_write d1) n :: s).
  Program Definition fifo : 0 ->> F :=
    {|
      Downset.has s := fifo_play nil ready s;
    |}.
  Next Obligation.
    cbn.
    generalize (@ready 0 F).
    generalize (nil: list byte).
    intros l p x y Hxy Hy. revert x Hxy.
    dependent induction Hy; intros x Hxy;
      dependent destruction Hxy; try constructor.
    - dependent destruction Hxy; econstructor; eauto.
    - dependent destruction Hxy. eapply fifo_read_all; eauto.
    - dependent destruction Hxy. eapply fifo_write; eauto.
  Qed.

  Definition pipe (p1 p2: S ->> P) : S ->> P :=
    seq ⊙
    (p1 + p2) ⊙
    fassoc ⊙
    (fassocr + id F) ⊙
    (id F + (fdup ⊙ fifo) + id F) ⊙
    (frur + id F).

  Hint Constructors comp_has : core.

  (** *** Property ϕ_(1) in Example 2.11 *)
  Lemma ϕ_1 : Γ [= pipe Γ_secret Γ_decode.
  Proof.
    intros p Hp. cbn in Hp. destruct Hp as ((se & Hse1 & Hse2) & Hp). cbn in Hp.
    eapply Downset.closed in Hp; eauto. clear Hp. unfold pipe.
    unfold compose at 1. cbn - [compose].
    eexists _, _. repeat apply conj.
    { exists se, (Int.repr 0), (Int.repr 0). reflexivity. }
    2: { unfold Γ_play, seq_play.
         apply comp_oq. apply comp_lq. apply comp_ra.
         repeat constructor. }
    Unshelve. 2: refine pnil_ready.
    unfold compose at 1. cbn - [compose].
    eexists _, _. repeat apply conj.
    { eexists _, _. repeat apply conj.
      - exists (exist _ se Hse1). reflexivity.
      - exists (exist _ se Hse2). reflexivity.
      - apply fcomp_oq_l. repeat constructor. }
    2:{ apply comp_oq.  apply comp_lq.  apply comp_ra.  apply comp_la.
        apply comp_oq.  apply comp_lq.  apply comp_ra.
        repeat constructor. }

    unfold compose at 1. cbn - [compose].
    Unshelve. 2: refine pnil_ready.
    eexists _, _. repeat apply conj.

    (* (* (F+F) + (F+F) ---> ((F+F)+F) + F *) *)

    apply emor_question. apply emor_answer.
    apply emor_question. apply emor_answer.
    apply emor_question. apply emor_answer.
    apply emor_ready.
    2: { apply comp_oq. apply comp_lq. apply comp_ra. apply comp_la.
         apply comp_oq. apply comp_lq. apply comp_ra.
         repeat constructor. }
    cbn [operator fassoc].
    Unshelve. 2: refine pnil_ready.
    eexists _, _. repeat apply conj.

    (* (* ((F+F)+F) + F ---> F + (F+F) + F *) *)

    eexists _, _. repeat apply conj.
    (* fassocr *)
    apply emor_question. apply emor_answer.
    apply emor_question. apply emor_answer.
    apply emor_ready.
    (* id *)
    apply emor_question. apply emor_answer. apply emor_ready.

    (* fcomp execute left component by default. so this is what we want *)
    repeat constructor.
    2: { repeat constructor. }
    cbn [operator fassoc].
    Unshelve. 2: refine pnil_ready.
    eexists _, _. repeat apply conj.

    (* (* F + (F+F) + F ---> F + 0 + F *) *)
    eexists _, _. repeat apply conj.
    2: { apply emor_question. apply emor_answer. apply emor_ready. }
    eexists _, _. repeat apply conj. apply emor_ready.

    eexists _, _. repeat apply conj.
    (* delta *)
    eapply emor_question with (q := inl _). apply emor_answer.
    eapply emor_question with (q := inr _). apply emor_answer.
    apply emor_ready.
    (* fifo *)
    eapply fifo_write with (d1 := uryyb_bytes).
    rewrite app_nil_l. reflexivity. cbn.
    instantiate (1 := (Int.repr 5)). reflexivity.
    eapply fifo_read_all with (n := (Int.repr 100)). cbn.
    rewrite Int.unsigned_repr. lia. cbn. lia. apply fifo_nil.

    repeat constructor.
    repeat constructor.
    repeat constructor.
    2: repeat constructor.

    (* F + 0 + F ---> F + F *)

    Unshelve. 2: refine pnil_ready.
    eexists _, _. repeat apply conj.
    cbn. apply emor_ready.
    cbn. apply emor_question with (q := F_write hello_bytes).
    apply emor_answer with (r := (Int.repr 5)). apply emor_ready.

    eapply fcomp_oq_r.
    eapply (fcomp_pq_r (E1 := F) (E2 := F)).
    eapply (fcomp_oa_r (E1 := F) (E2 := F)).
    eapply (fcomp_pa_r (E1 := F) (E2 := F)).
    constructor.
  Qed.

End STRATEGY.

(** ** Code Proof for the Clight programs *)

(** *** Clight Program rot13.c *)

Require Import AST Clight Ctypes Cop Maps.

Definition secret_c_main_id: positive := 1.
Definition secret_c_rot13_id: positive := 2.
Definition secret_c_write_id: positive := 3.
Definition secret_c_msg_id: positive := 4.

Definition rot13_buf_id: positive := 5.
Definition rot13_len_id: positive := 6.
Definition rot13_i_id: positive := 7.

(** Definition of rot13 function. For simplicity, we assume that the input
    buffer only contains lowercase alphabets *)
Program Definition rot13_body : statement :=
  let zero := Econst_int (Int.repr 0) tint in
  let one := Econst_int (Int.repr 1) tint in
  let len := Etempvar rot13_len_id tint in
  let i := Etempvar rot13_i_id tint in
  let buf := Etempvar rot13_buf_id (tptr tchar) in
  let buf_i := Ederef (Ebinop Oadd buf i tchar) tchar in
  let i97 := Econst_int (Int.repr 97) tint in
  let i84 := Econst_int (Int.repr 84) tint in
  let i26 := Econst_int (Int.repr 26) tint in
  (* we simplified `buf[i] - 'a' + 13` to `buf[i] - 84` *)
  let c1 := Ebinop Osub buf_i i84 tint in
  let c2 := Ebinop Omod c1 i26 tint in
  let c3 := Ebinop Oadd c2 i97 tint in
  let for_loop :=
    (* for i = 0; i < n; i++ *)
    Sfor(Sset rot13_i_id zero) (Ebinop Olt i len tint)
      (* buf[i] = (buf[i] - 'a' + 13) % 26 + 'a' *)
      (Sassign buf_i c3)
      (Sset rot13_i_id (Ebinop Oadd i one tint))
  in
  Ssequence for_loop (Sreturn None).

Program Definition rot13_function : function :=
  {|
    fn_return := tvoid;
    fn_callconv := cc_default;
    fn_params := [ (rot13_buf_id, tptr tchar); (rot13_len_id, tint) ];
    fn_temps := [ (rot13_i_id, tint) ];
    fn_vars := [];
    fn_body := rot13_body;
  |}.

Program Definition rot13_clight : Clight.program :=
  {|
    prog_defs := [(secret_c_rot13_id, Gfun (Internal rot13_function))];
    prog_public := [ secret_c_rot13_id ];
    prog_main := None;
    prog_types := [];
    prog_comp_env := (PTree.empty _);
  |}.
Next Obligation. reflexivity. Qed.

(** Clight-level program skeletons. Because the `secret` program is written
    directly in Assembly, we have to provide a corresponding Clight skeletons to
    invoke the loader, etc. *)

(** The imaginary Clight-level main function that correspond to the main
    function in the Assembly program secret.s. This function will not be
    executed, and its semantics will not be used *)
Context (secret_c_main_function : function).

Definition msg_il : list init_data :=
  [ Init_int8 (Int.repr 104); (* h *)
    Init_int8 (Int.repr 101); (* e *)
    Init_int8 (Int.repr 108); (* l *)
    Init_int8 (Int.repr 108); (* l *)
    Init_int8 (Int.repr 111) ]. (* o *)

Definition msg_globvar : globvar type :=
  {|
    gvar_info := tarray tchar 6%Z;
    gvar_init := msg_il;
    gvar_readonly := false;
    gvar_volatile := false;
  |}.

(** The imaginary Clight program that corresponds to the module obtained by
    composing the secret program and the rot13 program *)
Program Definition sr_clight: Clight.program :=
  {|
    prog_defs := [
      (secret_c_main_id, Gfun (Internal secret_c_main_function));
      (secret_c_rot13_id, Gfun (Internal rot13_function));
      (secret_c_write_id, Gfun write);
      (secret_c_msg_id, Gvar msg_globvar)];
    prog_public := nil;
    prog_main := Some secret_c_main_id;
    prog_types := [];
    prog_comp_env := (PTree.empty _);
  |}.
Next Obligation. reflexivity. Qed.

Require SecretAsm.
Require Import InitMem Util.

(** *** Correctness proof of the secret program *)

(** The proof corresponds to the ϕ_secret and π_secret combined in the Example 6.4 *)

Section SECRET.

  Definition sr_sk := AST.erase_program sr_clight.

  Lemma secret_init_mem se:
    Genv.valid_for sr_sk se ->
    exists m, init_mem se sr_sk = Some m /\
           (forall b, Genv.find_symbol se secret_c_msg_id = Some b ->
                 Mem.loadbytes m b 0 5 = Some (map Byte hello_bytes)
                 /\ forall ofs, (0 <= ofs < 5)%Z -> Mem.valid_access m Mint8unsigned b ofs Writable).
  Proof.
    intros Hvalid.
    edestruct init_mem_exists with (p := sr_sk) as [m Hm]; eauto.
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
      exploit (@Genv.store_init_data_list_loadbytes se b msg_il). apply H6.
      eapply Genv.store_zeros_loadbytes. eauto.
      intros Hx.
      split.
      + erewrite Mem.loadbytes_drop; eauto.
        right. right. right. constructor.
      + intros ofs Hofs.
        eapply Mem.valid_access_drop_1; eauto.
        right. right. right. constructor.
        unfold Mem.valid_access. split.
        intros r Hr.
        erewrite <- Genv.store_init_data_list_perm; eauto.
        erewrite <- Genv.store_zeros_perm; eauto.
        eapply init_perm_1 in H4. eauto with mem.
        cbn in *. lia. cbn. apply Z.divide_1_l.
  Qed.

  Lemma main_block se:
    Genv.valid_for sr_sk se ->
    exists b, Genv.find_symbol (globalenv se sr_clight) secret_c_main_id = Some b /\
           Genv.find_funct (globalenv se sr_clight) (Vptr b Ptrofs.zero) = Some (Internal secret_c_main_function).
  Proof.
    intros Hse. exploit @Genv.find_def_symbol; eauto.
    intros [H _]. edestruct H as (b & Hb1 & Hb2); eauto.
    2: { exists b. split; eauto. eapply genv_funct_symbol; eauto. }
    reflexivity.
  Qed.
  Lemma rot13_block se:
    Genv.valid_for sr_sk se ->
    exists b, Genv.find_symbol (globalenv se sr_clight) secret_c_rot13_id = Some b /\
           Genv.find_funct (globalenv se sr_clight) (Vptr b Ptrofs.zero) = Some (Internal rot13_function).
  Proof.
    intros Hse. exploit @Genv.find_def_symbol; eauto.
    intros [H _]. edestruct H as (b & Hb1 & Hb2); eauto.
    2: { exists b. split; eauto. eapply genv_funct_symbol; eauto. }
    reflexivity.
  Qed.
  Lemma write_block se:
    Genv.valid_for sr_sk se ->
    exists b, Genv.find_symbol (globalenv se sr_clight) secret_c_write_id = Some b /\
           Genv.find_funct (globalenv se sr_clight) (Vptr b Ptrofs.zero) = Some write.
  Proof.
    intros Hse. exploit @Genv.find_def_symbol; eauto.
    intros [H _]. edestruct H as (b & Hb1 & Hb2); eauto.
    2: { exists b. split; eauto. eapply genv_funct_symbol; eauto. }
    reflexivity.
  Qed.
  Lemma msg_block se:
    Genv.valid_for sr_sk se ->
    exists b, Genv.find_symbol (globalenv se sr_clight) secret_c_msg_id = Some b.
  Proof.
    intros Hse. exploit @Genv.find_def_symbol; eauto.
    intros [H _]. edestruct H as (b & Hb1 & Hb2); eauto.
    reflexivity.
  Qed.
  Lemma Hrot13_sig:
    SecretAsm.rot13_sig = signature_of_type (Tcons (tptr tchar) (Tcons tint Tnil)) tvoid cc_default.
  Proof. reflexivity. Qed.

  Definition L_secret := SecretAsm.secret_spec.
  Definition L_compose := fun (i: bool) => if i then L_secret else Clight.semantics2 rot13_clight.
  Local Opaque semantics2.

  Lemma ϕ_secret :
    Γ_secret sr_sk [= load_c_sem sr_clight (SmallstepLinking.semantics L_compose sr_sk).
  Proof.
    intros p Hp. cbn in Hp. destruct Hp as ((se & Hse) & Hp).
    eapply Downset.closed in Hp; eauto. clear Hp.
    edestruct secret_init_mem as (m & Hm1 & Hm2). apply Hse.
    edestruct main_block as (b & Hb1 & Hb2). apply Hse.
    edestruct rot13_block as (b1 & Hb3 & Hb4). apply Hse.
    edestruct write_block as (b2 & Hb5 & Hb6). apply Hse.
    edestruct msg_block as (b3 & Hb7). apply Hse.
    assert (Hflag: Mem.alloc_flag m = true).
    { eapply init_mem_alloc_flag; eauto. }
    specialize (Hm2 _ Hb7) as (Hm2 & Hm2').
    assert (Hm0: Mem.load Mint8unsigned m b3 0 = Some (Vint (Int.repr 104))).
    { eapply loadbyte' with (i := 0%Z) in Hm2. 2: lia. 2: constructor.
      rewrite Hm2. repeat f_equal. }
    assert (exists m', Mem.store Mint8unsigned m b3 0 (Vint (Int.repr 117)) = Some m') as (m3 & Hm0').
    { edestruct Mem.valid_access_store as (mx & Hmx). 2: eexists; eauto.
      apply Hm2'. lia. }
    assert (Hm4: Mem.load Mint8unsigned m3 b3 1 = Some (Vint (Int.repr 101))).
    { eapply loadbyte' with (i := 1%Z) in Hm2. 2: lia. 2: repeat constructor.
      erewrite Mem.load_store_other; eauto. do 2 right. cbn. lia. }
    assert (exists m', Mem.store Mint8unsigned m3 b3 1 (Vint (Int.repr 114)) = Some m') as (m4 & Hm4').
    { edestruct Mem.valid_access_store as (mx & Hmx). 2: eexists; eauto.
      eapply Mem.store_valid_access_1; eauto. apply Hm2'. lia. }
    assert (Hm5: Mem.load Mint8unsigned m4 b3 2 = Some (Vint (Int.repr 108))).
    { eapply loadbyte' with (i := 2%Z) in Hm2. 2: lia. 2: repeat constructor.
      erewrite Mem.load_store_other; [ | eauto | ].
      erewrite Mem.load_store_other; eauto. all : do 2 right; cbn; lia. }
    assert (exists m', Mem.store Mint8unsigned m4 b3 2 (Vint (Int.repr 121)) = Some m') as (m5 & Hm5').
    { edestruct Mem.valid_access_store as (mx & Hmx). 2: eexists; eauto.
      eapply Mem.store_valid_access_1; eauto.
      eapply Mem.store_valid_access_1; eauto.  apply Hm2'. lia. }
    assert (Hm6: Mem.load Mint8unsigned m5 b3 3 = Some (Vint (Int.repr 108))).
    { eapply loadbyte' with (i := 3%Z) in Hm2. 2: lia. 2: repeat constructor.
      erewrite Mem.load_store_other; [ | eauto | ].
      erewrite Mem.load_store_other; [ | eauto | ].
      erewrite Mem.load_store_other; eauto. all : do 2 right; cbn; lia. }
    assert (exists m', Mem.store Mint8unsigned m5 b3 3 (Vint (Int.repr 121)) = Some m') as (m6 & Hm6').
    { edestruct Mem.valid_access_store as (mx & Hmx). 2: eexists; eauto.
      eapply Mem.store_valid_access_1; eauto.
      eapply Mem.store_valid_access_1; eauto.
      eapply Mem.store_valid_access_1; eauto.  apply Hm2'. lia. }
    assert (Hm7: Mem.load Mint8unsigned m6 b3 4 = Some (Vint (Int.repr 111))).
    { eapply loadbyte' with (i := 4%Z) in Hm2. 2: lia. 2: repeat constructor.
      erewrite Mem.load_store_other; [ | eauto | ].
      erewrite Mem.load_store_other; [ | eauto | ].
      erewrite Mem.load_store_other; [ | eauto | ].
      erewrite Mem.load_store_other; eauto. all : do 2 right; cbn; lia. }
    assert (exists m', Mem.store Mint8unsigned m6 b3 4 (Vint (Int.repr 98)) = Some m') as (m7 & Hm7').
    { edestruct Mem.valid_access_store as (mx & Hmx). 2: eexists ; eauto.
      eapply Mem.store_valid_access_1; eauto.
      eapply Mem.store_valid_access_1; eauto.
      eapply Mem.store_valid_access_1; eauto.
      eapply Mem.store_valid_access_1; eauto. apply Hm2'. lia. }
    assert (Mem.loadbytes m7 b3 0 5 = Some (map Byte uryyb_bytes)) as Hmx.
    { Transparent Mem.loadbytes Mem.store.
      unfold Mem.loadbytes. cbn.
      destruct (Mem.range_perm_dec m7 b3 0 5 Cur Readable) eqn: Hx.
      2: {
        exfalso. apply n. intros f Hf.
        clear - Hm0' Hm4' Hm5' Hm6' Hm7' Hm2' Hf.
        do 5 (eapply Mem.perm_store_1; [ eauto | ]).
        specialize (Hm2' _ Hf). destruct Hm2'. cbn in *.
        specialize (H f). exploit H. lia. eauto with mem.
      }
      clear - Hm0' Hm4' Hm5' Hm6' Hm7'.
      unfold Mem.store in *.
      repeat destruct Mem.valid_access_dec; try congruence.
      cbn in *.
      clear - Hm0' Hm4' Hm5' Hm6' Hm7'.
      inv Hm7'. cbn. inv Hm6'. cbn. inv Hm5'. cbn. inv Hm4'. cbn. inv Hm0'. cbn.
      f_equal.
      rewrite !PMap.gss.
      rewrite !Int.unsigned_repr by (cbn; lia). 
      replace (Pos.to_nat 5) with 5 by reflexivity. cbn.
      assert (forall x, encode_int 1 x = [ Byte.repr x ]%list) by reflexivity.
      rewrite !H. cbn. repeat f_equal.
      - do 4 rewrite ZMap.gso by lia. now rewrite ZMap.gss.
      - do 3 rewrite ZMap.gso by lia. now rewrite ZMap.gss.
      - do 2 rewrite ZMap.gso by lia. now rewrite ZMap.gss.
      - do 1 rewrite ZMap.gso by lia. now rewrite ZMap.gss.
      - now rewrite ZMap.gss. }
    eexists _, _. repeat apply conj.
    3: { unfold entry_c_play. unfold Γ_secret_play.
         apply comp_oq. apply comp_lq. apply comp_rq. apply comp_oa.
         apply comp_ra. apply comp_la. instantiate (1 := pnil_ready). apply comp_ready. }
    { cbn. eexists se, _, _, Int.zero. eexists.
      econstructor. 1,5,6: eauto. apply Hb1. reflexivity. reflexivity.
      unfold entry_c_play. reflexivity. }
    eexists _, _. repeat apply conj.
    3: { apply comp_oq. apply comp_lq. apply comp_rq. apply comp_oa.
         apply comp_ra. apply comp_la. instantiate (1 := pnil_ready). apply comp_ready. }
    2: { eapply closure_has_cons. 2: apply closure_has_nil.
         2: apply seq_comp_has_nil2; reflexivity.
         exists false. cbn. eexists se, _, uryyb_bytes, _, _. exists.
         econstructor; eauto.
         replace 0%Z with (Ptrofs.unsigned Ptrofs.zero) in Hmx by reflexivity. apply Hmx.
         cbn. lia.
         unfold write_c_play. reflexivity. }
    cbn. eapply closure_has_cons.
    2: apply closure_has_nil.
    2: apply seq_comp_has_nil2; eauto.
    cbn. econstructor; eauto. (* initial step *)
    { econstructor.
      - instantiate (1 := true).
        cbn. unfold valid_query. split; cbn; try congruence.
        exists secret_c_main_id. split; eauto.
        + unfold footprint_of_program. cbn.
          rewrite PTree.gso. rewrite PTree.gso. rewrite PTree.gso.
          rewrite PTree.gss. reflexivity.
          all: intros HH; inv HH.
        + unfold Genv.symbol_address.
          cbn in Hb1. rewrite Hb1. reflexivity.
      - econstructor; eauto. }
    econstructor 4. (* L_secret internal step *)
    { apply star_one. econstructor 1. econstructor 1; eauto. }
    econstructor 4. (* L_secret calls rot13 *)
    { apply star_one. econstructor 2.
      - constructor; eauto. 
      - instantiate (1 := false).
        unfold valid_query. split; cbn; try congruence.
        exists secret_c_rot13_id. split.
        + Local Transparent semantics2. cbn.
          unfold footprint_of_program. cbn.
          rewrite PTree.gss. reflexivity.
          Local Opaque semantics2.
        + unfold Genv.symbol_address. cbn in Hb3.
          rewrite Hb3. reflexivity.
      - rewrite Hrot13_sig. econstructor; eauto.
        + rewrite <- Hb4.
          setoid_rewrite SecretAsm.find_funct_spec; eauto.
          cbn. rewrite PTree.gss.
          rewrite PTree.gso. rewrite PTree.gso. rewrite PTree.gss.
          reflexivity.
          all: intros HH; inv HH.
        + reflexivity.
        + repeat constructor.
        + cbn. erewrite init_mem_nextblock; eauto. reflexivity. }
    econstructor 4. (* Callstate -> State *)
    { apply star_one. econstructor 1.
      eapply step_internal_function.
      - rewrite <- Hb4.
        setoid_rewrite SecretAsm.find_funct_spec; eauto.
        cbn. rewrite PTree.gss.
        rewrite PTree.gso. rewrite PTree.gso. rewrite PTree.gss.
        reflexivity.
        all: intros HH; inv HH.
      - econstructor; cbn; eauto.
        + solve_list_norepet.
        + solve_list_norepet.
        + solve_list_disjoint.
        + apply alloc_variables_nil. }
    (* loop 5 times *)
    cbn. unfold rot13_body.
    Ltac one_trivial_step := econstructor 4; [ apply star_one; econstructor 1; crush_step; crush_expr | ].
    one_trivial_step.
    econstructor 4. (* unfold Sfor *)
    { apply star_one. econstructor 1. unfold Sfor. crush_step. }
    do 5 one_trivial_step.
    replace (negb (Int.eq Int.one Int.zero)) with true by reflexivity.
    one_trivial_step.
    Ltac sub_modu_add_zero_ext :=
      unfold Int.sub; rewrite !Int.unsigned_repr by (cbn; lia); cbn;
      unfold Int.modu; rewrite !Int.unsigned_repr by (cbn; lia); cbn;
      unfold Int.add; rewrite !Int.unsigned_repr by (cbn; lia); cbn;
      unfold Int.zero_ext; rewrite !Int.unsigned_repr by (cbn; lia); cbn.
    econstructor 4. (* Sassign buf[i] = .. *)
    { apply star_one. econstructor 1. crush_step; crush_expr. }
    do 6 one_trivial_step.
    replace (negb (Int.eq Int.one Int.zero)) with true by reflexivity.
    one_trivial_step.
    econstructor 4. (* Sassign buf[i] = .. *)
    { apply star_one. econstructor 1. crush_step; crush_expr. }
    do 6 one_trivial_step.
    replace (negb (Int.eq Int.one Int.zero)) with true by reflexivity.
    one_trivial_step.
    econstructor 4. (* Sassign buf[i] = .. *)
    { apply star_one. econstructor 1. crush_step; crush_expr. }
    do 6 one_trivial_step.
    replace (negb (Int.eq Int.one Int.zero)) with true by reflexivity.
    one_trivial_step.
    econstructor 4. (* Sassign buf[i] = .. *)
    { apply star_one. econstructor 1. crush_step; crush_expr. }
    do 6 one_trivial_step.
    replace (negb (Int.eq Int.one Int.zero)) with true by reflexivity.
    one_trivial_step.
    econstructor 4. (* Sassign buf[i] = .. *)
    { apply star_one. econstructor 1. crush_step; crush_expr. }
    do 6 one_trivial_step.
    replace (negb (Int.eq Int.zero Int.zero)) with false by reflexivity.
    do 4 one_trivial_step. 
    econstructor 4. (* rot13 returns to L_secret *)
    { apply star_one. econstructor 3.
      - constructor.
      - econstructor. apply Hb7. }
    econstructor 4. (* L_secret internal step *)
    { apply star_one. econstructor 1. econstructor 2. }
    econstructor 2.
    { econstructor.
      - econstructor; eauto.
      - intros [|] Hj.
        + unfold valid_query in Hj. cbn in Hj.
          destruct Hj as (Hj1 & (i & Hj2 & Hj3)).
          unfold Genv.symbol_address in Hj3.
          unfold footprint_of_program in Hj2.
          destruct (Genv.find_symbol se i) eqn: Hj4; try congruence.
          inv Hj3.
          exploit Genv.find_symbol_injective. apply Hj4. apply Hb5.
          intros ->. cbn in Hj2.
          rewrite PTree.gso in Hj2. rewrite PTree.gss in Hj2.
          inv Hj2. intros HH. inv HH.
        + unfold valid_query in Hj. cbn in Hj.
          destruct Hj as (Hj1 & (i & Hj2 & Hj3)).
          unfold Genv.symbol_address in Hj3.
          Local Transparent semantics2. cbn in Hj2. Local Opaque semantics2.
          unfold footprint_of_program in Hj2.
          destruct (Genv.find_symbol se i) eqn: Hj4; try congruence.
          inv Hj3.
          exploit Genv.find_symbol_injective. apply Hj4. apply Hb5.
          intros ->. cbn in Hj2.
          rewrite PTree.gso in Hj2. rewrite PTree.gempty in Hj2. inv Hj2.
          intros HH. inv HH. }
    { repeat econstructor. }
    econstructor 4. (* L_secret internal step *)
    { apply star_one. econstructor 1. econstructor 3. }
    econstructor 3.
    { econstructor. econstructor. }
  Qed.

End SECRET.

(** ** Code Proof for the Clight programs *)

(** *** Clight Program decode.c *)

Definition decode_main_id: positive := 1.
Definition decode_rot13_id: positive := 2.
Definition decode_read_id: positive := 3.
Definition decode_write_id: positive := 4.

Definition decode_buf_id: positive := 5.
Definition decode_n_id: positive := 6.

Definition rot13_type := Tfunction (Tcons (tptr tchar) (Tcons tint Tnil)) tvoid cc_default.

Definition decode_body : statement :=
  let zero := Econst_int (Int.repr 0) tint in
  let one := Econst_int (Int.repr 1) tint in
  let n := Etempvar decode_n_id tint in
  let buf := Evar decode_buf_id (tarray tchar 100%Z) in
  let read_buf :=
    (* n = read(0, buf, sizeof buf) *)
    Scall (Some decode_n_id) (Evar decode_read_id rw_type) [ zero; buf; Ecast (Esizeof (tarray tchar 100%Z) tlong) tint ]
  in
  let rot_buf :=
    (* rot13(buf, n) *)
    Scall None (Evar decode_rot13_id rot13_type) [ buf; n ]
  in
  let write_buf :=
    (* write(1, buf, n) *)
    Scall None (Evar decode_write_id rw_type) [ one; buf; n ]
  in
  Ssequence read_buf
    (Ssequence rot_buf
       (Ssequence write_buf (Sreturn (Some zero)))).

Definition decode_main : function :=
  {|
    fn_return := tint;
    fn_callconv := cc_default;
    fn_params := [ ];
    fn_temps := [ (decode_n_id, tint) ];
    fn_vars := [ (decode_buf_id, tarray tchar 100%Z) ];
    fn_body := decode_body;
  |}.

Definition rot13_ext_fun : Clight.fundef :=
  External (EF_external "rot13" SecretAsm.rot13_sig)
    (Tcons (tptr tchar) (Tcons tint Tnil))
    tvoid cc_default.
Program Definition decode_clight : Clight.program :=
  {|
    prog_defs := [(decode_main_id, Gfun (Internal decode_main));
                  (decode_rot13_id, Gfun rot13_ext_fun);
                  (decode_read_id, Gfun read);
                  (decode_write_id, Gfun write)];
    prog_public := [ decode_main_id; decode_rot13_id ];
    prog_main := Some decode_main_id;
    prog_types := [];
    prog_comp_env := (PTree.empty _);
  |}.
Next Obligation. reflexivity. Qed.

Program Definition dr_clight : Clight.program :=
  {|
    prog_defs := [(decode_write_id, Gfun write);
                  (decode_rot13_id, Gfun (Internal rot13_function));
                  (decode_main_id, Gfun (Internal decode_main));
                  (decode_read_id, Gfun read)];
    prog_public := [ decode_main_id; decode_rot13_id; secret_c_rot13_id ];
    prog_main := Some decode_main_id;
    prog_types := [];
    prog_comp_env := (PTree.empty _);
  |}.
Next Obligation. reflexivity. Qed.

Lemma mk_program_ext {F: Type} def1 def2 pub1 pub2 main1 main2 typ1 typ2 cenv1 cenv2 cenv_eq1 cenv_eq2:
  def1 = def2 -> pub1 = pub2 -> main1 = main2 -> typ1 = typ2 -> cenv1 = cenv2 -> 
  @Build_program F def1 pub1 main1 typ1 cenv1 cenv_eq1 = @Build_program F def2 pub2 main2 typ2 cenv2 cenv_eq2.
Proof. intros. subst. f_equal. apply Axioms.proof_irr. Qed.

Lemma Hdr_program : Linking.link decode_clight rot13_clight = Some dr_clight.
  Transparent Linker_program Linking.Linker_prog.
  unfold Linking.link. cbn.
  unfold link_program. cbn.
  unfold Linking.link_prog. cbn.
  assert (PTree_Properties.for_all
        (PTree.set decode_write_id (Gfun write)
           (PTree.set decode_read_id (Gfun read)
              (PTree.set decode_rot13_id (Gfun rot13_ext_fun)
                 (PTree.set decode_main_id (Gfun (Internal decode_main))
                    (PTree.empty (globdef (fundef function) type))))))
        (Linking.link_prog_check decode_clight rot13_clight) = true) as H.
  {
    apply PTree_Properties.for_all_correct. intros x a Hx.
    unfold Linking.link_prog_check.
    simpl.
    destruct (peq x decode_write_id); subst. reflexivity.
    destruct (peq x decode_read_id); subst. reflexivity.
    destruct (peq x decode_rot13_id); subst. simpl.
    {
      do 2 (rewrite PTree.gso in Hx; [ | eauto ]).
      rewrite PTree.gss in Hx. inv Hx.
      Transparent Linking.Linker_def Linker_fundef. simpl.
      destruct peq. inv e.
      destruct peq. reflexivity.
      exfalso. apply n2. reflexivity.
    }
    destruct (peq x decode_main_id); subst. reflexivity.
    do 4 (rewrite PTree.gso in Hx; [ | eauto ]).
    rewrite PTree.gempty in Hx. inv Hx.
  }
  setoid_rewrite H. cbn.
  destruct link_build_composite_env.
  destruct a. unfold dr_clight. f_equal.
  apply mk_program_ext; eauto.
  cbn in e. inv e. reflexivity.
Qed.

(** *** Correctness proof of the decode program *)

(** The proof corresponds to the ϕ_decode and π_decode combined in the Example 6.4 *)

Section DECODE.

  Definition dr_sk := AST.erase_program dr_clight.

  Definition L_compose1 := fun (i: bool) => if i then Clight.semantics2 decode_clight else Clight.semantics2 rot13_clight.
  Local Opaque semantics2.

  Lemma decode_init_mem se:
    Genv.valid_for dr_sk se -> exists m, init_mem se dr_sk = Some m.
  Proof.
    intros Hvalid. eapply init_mem_exists; eauto.
    split; cbn in H; destruct_or H; inv H.
  Qed.
  Lemma decode_main_block se:
    Genv.valid_for dr_sk se ->
    exists b, Genv.find_symbol (globalenv se dr_clight) decode_main_id = Some b /\
           Genv.find_funct (globalenv se dr_clight) (Vptr b Ptrofs.zero) = Some (Internal decode_main).
  Proof.
    intros Hse. exploit @Genv.find_def_symbol; eauto.
    intros [H _]. edestruct H as (b & Hb1 & Hb2); eauto.
    2: { exists b. split; eauto. eapply genv_funct_symbol; eauto. }
    reflexivity.
  Qed.
  Lemma decode_rot13_block se:
    Genv.valid_for dr_sk se ->
    exists b, Genv.find_symbol (globalenv se dr_clight) decode_rot13_id = Some b /\
           Genv.find_funct (globalenv se dr_clight) (Vptr b Ptrofs.zero) = Some (Internal rot13_function).
  Proof.
    intros Hse. exploit @Genv.find_def_symbol; eauto.
    intros [H _]. edestruct H as (b & Hb1 & Hb2); eauto.
    2: { exists b. split; eauto. eapply genv_funct_symbol; eauto. }
    reflexivity.
  Qed.
  Lemma decode_write_block se:
    Genv.valid_for dr_sk se ->
    exists b, Genv.find_symbol (globalenv se dr_clight) decode_write_id = Some b /\
           Genv.find_funct (globalenv se dr_clight) (Vptr b Ptrofs.zero) = Some write.
  Proof.
    intros Hse. exploit @Genv.find_def_symbol; eauto.
    intros [H _]. edestruct H as (b & Hb1 & Hb2); eauto.
    2: { exists b. split; eauto. eapply genv_funct_symbol; eauto. }
    reflexivity.
  Qed.
  Lemma decode_read_block se:
    Genv.valid_for dr_sk se ->
    exists b, Genv.find_symbol (globalenv se dr_clight) decode_read_id = Some b /\
           Genv.find_funct (globalenv se dr_clight) (Vptr b Ptrofs.zero) = Some read.
  Proof.
    intros Hse. exploit @Genv.find_def_symbol; eauto.
    intros [H _]. edestruct H as (b & Hb1 & Hb2); eauto.
    2: { exists b. split; eauto. eapply genv_funct_symbol; eauto. }
    reflexivity.
  Qed.

  Lemma ϕ_decode :
    Γ_decode dr_sk [= load_c_sem dr_clight (SmallstepLinking.semantics L_compose1 dr_sk).
  Proof.
    intros p Hp. cbn in Hp. destruct Hp as ((se & Hse) & Hp).
    eapply Downset.closed in Hp; eauto. clear Hp.
    edestruct decode_main_block as (b & Hb1 & Hb2). apply Hse.
    edestruct decode_rot13_block as (b1 & Hb3 & Hb4). apply Hse.
    edestruct decode_write_block as (b2 & Hb5 & Hb6). apply Hse.
    edestruct decode_read_block as (b3 & Hb7 & Hb8). apply Hse.
    edestruct decode_init_mem as (m & Hm0). apply Hse.
    assert (Hflag: Mem.alloc_flag m = true).
    { eapply init_mem_alloc_flag; eauto. }
    edestruct (@Mem.alloc_succeed m 0 100); eauto. destruct x as (m1 & bb1).
    assert (exists m2, Mem.storebytes m1 bb1 0 (map Byte uryyb_bytes) = Some m2) as (m2 & Hm2).
    { edestruct Mem.range_perm_storebytes. 2: eexists; eauto.
      intros f Hf. cbn in Hf.
      eapply Mem.perm_alloc_2 in e. eauto with mem. lia. }
    assert (Hm2': Mem.loadbytes m2 bb1 0 5 = Some (map Byte uryyb_bytes)).
    { erewrite <- Mem.loadbytes_storebytes_same; eauto. }
    assert (Hm2'' : forall ofs, (0 <= ofs < 5)%Z -> Mem.valid_access m2 Mint8unsigned bb1 ofs Writable).
    { intros ofs Hofs.
      unfold Mem.valid_access. cbn. split. 2: apply Z.divide_1_l. intros f Hf.
      eapply Mem.perm_storebytes_1; eauto.
      eapply Mem.perm_alloc_2 in e. eauto with mem. lia. }
    assert (Hm3: Mem.load Mint8unsigned m2 bb1 0 = Some (Vint (Int.repr 117))).
    { eapply loadbyte' with (i := 0%Z) in Hm2'. 2: lia. 2: constructor.
      rewrite Hm2'. repeat f_equal. }
    assert (exists m', Mem.store Mint8unsigned m2 bb1 0 (Vint (Int.repr 104)) = Some m') as (m3 & Hm3'). 
    { edestruct Mem.valid_access_store as (mx & Hmx). 2: eexists; eauto.
      apply Hm2''. lia. }
    assert (Hm4: Mem.load Mint8unsigned m3 bb1 1 = Some (Vint (Int.repr 114))).
    { eapply loadbyte' with (i := 1%Z) in Hm2'. 2: lia. 2: repeat constructor.
      erewrite Mem.load_store_other; eauto. do 2 right. cbn. lia. }
    assert (exists m', Mem.store Mint8unsigned m3 bb1 1 (Vint (Int.repr 101)) = Some m') as (m4 & Hm4'). 
    { edestruct Mem.valid_access_store as (mx & Hmx). 2: eexists; eauto.
      eapply Mem.store_valid_access_1; eauto. apply Hm2''. lia. }
    assert (Hm5: Mem.load Mint8unsigned m4 bb1 2 = Some (Vint (Int.repr 121))). 
    { eapply loadbyte' with (i := 2%Z) in Hm2'. 2: lia. 2: repeat constructor.
      erewrite Mem.load_store_other; [ | eauto | ].
      erewrite Mem.load_store_other; eauto. all : do 2 right; cbn; lia. }
    assert (exists m', Mem.store Mint8unsigned m4 bb1 2 (Vint (Int.repr 108)) = Some m') as (m5 & Hm5'). 
    { edestruct Mem.valid_access_store as (mx & Hmx). 2: eexists; eauto.
      eapply Mem.store_valid_access_1; eauto.
      eapply Mem.store_valid_access_1; eauto.  apply Hm2''. lia. }
    assert (Hm6: Mem.load Mint8unsigned m5 bb1 3 = Some (Vint (Int.repr 121))). 
    { eapply loadbyte' with (i := 3%Z) in Hm2'. 2: lia. 2: repeat constructor.
      erewrite Mem.load_store_other; [ | eauto | ].
      erewrite Mem.load_store_other; [ | eauto | ].
      erewrite Mem.load_store_other; eauto. all : do 2 right; cbn; lia. }
    assert (exists m', Mem.store Mint8unsigned m5 bb1 3 (Vint (Int.repr 108)) = Some m') as (m6 & Hm6'). 
    { edestruct Mem.valid_access_store as (mx & Hmx). 2: eexists; eauto.
      eapply Mem.store_valid_access_1; eauto.
      eapply Mem.store_valid_access_1; eauto.
      eapply Mem.store_valid_access_1; eauto.  apply Hm2''. lia. }
    assert (Hm7: Mem.load Mint8unsigned m6 bb1 4 = Some (Vint (Int.repr 98))).
    { eapply loadbyte' with (i := 4%Z) in Hm2'. 2: lia. 2: repeat constructor.
      erewrite Mem.load_store_other; [ | eauto | ].
      erewrite Mem.load_store_other; [ | eauto | ].
      erewrite Mem.load_store_other; [ | eauto | ].
      erewrite Mem.load_store_other; eauto. all : do 2 right; cbn; lia. }
    assert (exists m', Mem.store Mint8unsigned m6 bb1 4 (Vint (Int.repr 111)) = Some m') as (m7 & Hm7').
    { edestruct Mem.valid_access_store as (mx & Hmx). 2: eexists ; eauto.
      eapply Mem.store_valid_access_1; eauto.
      eapply Mem.store_valid_access_1; eauto.
      eapply Mem.store_valid_access_1; eauto.
      eapply Mem.store_valid_access_1; eauto. apply Hm2''. lia. }
    assert (Mem.loadbytes m7 bb1 0 5 = Some (map Byte hello_bytes)) as Hmx. 
    { Transparent Mem.loadbytes Mem.store.
      unfold Mem.loadbytes. cbn.
      destruct (Mem.range_perm_dec m7 bb1 0 5 Cur Readable) eqn: Hx.
      2: {
        exfalso. apply n. intros f Hf.
        clear - Hm2'' Hm3' Hm4' Hm5' Hm6' Hm7' Hm2' Hf.
        do 5 (eapply Mem.perm_store_1; [ eauto | ]).
        specialize (Hm2'' _ Hf). destruct Hm2''. cbn in *.
        specialize (H f). exploit H. lia. eauto with mem.
      }
      clear - Hm3' Hm4' Hm5' Hm6' Hm7'.
      unfold Mem.store in *.
      repeat destruct Mem.valid_access_dec; try congruence.
      cbn in *.
      clear - Hm3' Hm4' Hm5' Hm6' Hm7'.
      inv Hm7'. cbn. inv Hm6'. cbn. inv Hm5'. cbn. inv Hm4'. cbn. inv Hm3'. cbn.
      f_equal.
      rewrite !PMap.gss.
      rewrite !Int.unsigned_repr by (cbn; lia).
      replace (Pos.to_nat 5) with 5 by reflexivity. cbn.
      assert (forall x, encode_int 1 x = [ Byte.repr x ]%list) by reflexivity.
      rewrite !H. cbn. repeat f_equal.
      - do 4 rewrite ZMap.gso by lia. now rewrite ZMap.gss.
      - do 3 rewrite ZMap.gso by lia. now rewrite ZMap.gss.
      - do 2 rewrite ZMap.gso by lia. now rewrite ZMap.gss.
      - do 1 rewrite ZMap.gso by lia. now rewrite ZMap.gss.
      - now rewrite ZMap.gss. }
    assert (exists m8, Mem.free_list m7 [(bb1, 0%Z, 100%Z)] = Some m8) as (m8 & Hm8).
    { edestruct Mem.range_perm_free as (mm & Hmm).
      2: { eexists; cbn. rewrite Hmm. reflexivity. }
      intros f Hf.
      do 5 (eapply Mem.perm_store_1; eauto).
      eapply Mem.perm_storebytes_1; eauto.
      eauto with mem. }
    assert (Hb2' : Genv.find_funct (globalenv se decode_clight) (Vptr b Ptrofs.zero) = Some (Internal decode_main)).
    { setoid_rewrite SecretAsm.find_funct_spec; eauto. cbn.
      rewrite PTree.gso. rewrite PTree.gso. rewrite PTree.gso. rewrite PTree.gss.
      reflexivity. 1-3: intros HH; inv HH. }
    assert (Hb4' : Genv.find_funct (globalenv se decode_clight) (Vptr b1 Ptrofs.zero) = Some rot13_ext_fun).
    { setoid_rewrite SecretAsm.find_funct_spec; eauto. cbn.
      rewrite PTree.gso. rewrite PTree.gso. rewrite PTree.gss.
      reflexivity. 1-2: intros HH; inv HH. }
    assert (Hb6' : Genv.find_funct (globalenv se decode_clight) (Vptr b2 Ptrofs.zero) = Some write).
    { setoid_rewrite SecretAsm.find_funct_spec; eauto. cbn.
      rewrite PTree.gss. reflexivity. }
    assert (Hb8' : Genv.find_funct (globalenv se decode_clight) (Vptr b3 Ptrofs.zero) = Some read).
    { setoid_rewrite SecretAsm.find_funct_spec; eauto. cbn.
      rewrite PTree.gso. rewrite PTree.gss. reflexivity. intros HH; inv HH. }
    eexists _, _. repeat apply conj.
    3: { unfold Γ_decode_play.
         apply comp_oq. apply comp_lq. apply comp_rq. apply comp_oa.
         apply comp_rq. apply comp_oa.
         apply comp_ra. apply comp_la. instantiate (1 := pnil_ready). apply comp_ready. }
    { cbn. eexists se, _, _, Int.zero. exists.
      econstructor. 1,5,6: eauto. apply Hb1. reflexivity. reflexivity.
      unfold entry_c_play. reflexivity. }
    eexists _, _. repeat apply conj.
    3: { apply comp_oq.
         apply comp_lq. apply comp_rq. apply comp_oa. apply comp_ra.
         apply comp_lq. apply comp_rq. apply comp_oa. apply comp_ra.
         apply comp_la. instantiate (1 := pnil_ready). apply comp_ready. }
    2: { eapply closure_has_cons. 2: eapply closure_has_cons. 3: apply closure_has_nil.
         3: apply seq_comp_has_nil2; reflexivity.
         - exists true. cbn. eexists se, _, _, uryyb_bytes, _. exists. 2: reflexivity.
           econstructor; eauto.
           + replace 0%Z with (Ptrofs.unsigned Ptrofs.zero) in Hm2 by reflexivity. apply Hm2.
           + instantiate (1 := Int.repr 100%Z). cbn.
             rewrite Int.unsigned_repr by (cbn; lia). lia.
         - exists false. cbn. eexists se, _, hello_bytes, _, _. exists. 2: reflexivity.
           econstructor; eauto.
           replace 0%Z with (Ptrofs.unsigned Ptrofs.zero) in Hmx by reflexivity. apply Hmx.
           cbn. lia.
         - cbn. unfold read_c_play, write_c_play. repeat constructor. }
    cbn. eapply closure_has_cons.
    2: apply closure_has_nil. 2: apply seq_comp_has_nil2; eauto.
    cbn. econstructor; eauto. (* initial step *)
    { econstructor.
      - instantiate (1 := true).
        cbn. unfold valid_query. split; cbn; try congruence.
        exists decode_main_id. split; eauto.
        + Transparent semantics2. cbn.
          unfold footprint_of_program. cbn.
          Opaque semantics2.
          rewrite PTree.gso. rewrite PTree.gso. rewrite PTree.gso.
          rewrite PTree.gss. reflexivity.
          all: intros HH; inv HH.
        + unfold Genv.symbol_address.
          cbn in Hb1. rewrite Hb1. reflexivity.
      - econstructor; eauto.
        + constructor.
        + cbn. erewrite init_mem_nextblock; eauto. reflexivity. }
    econstructor 4. (* decode.c internal step: Callstate -> State *)
    { apply star_one. econstructor 1. constructor; eauto.
      constructor; cbn; eauto; try solve [ solve_list_norepet | solve_list_disjoint ].
      econstructor. 2: constructor. eauto. }
    econstructor 4. (* decode.c internal step *)
    { apply star_one. econstructor 1. crush_step. }
    econstructor 4. (* decode.c internal step *)
    { apply star_one. econstructor 1. unfold rw_type. crush_step; eauto; try reflexivity.
      - crush_expr.
      - crush_expr.
        constructor. reflexivity.
        eapply eval_Ecast. crush_expr. reflexivity.
        constructor. reflexivity. }
    econstructor 2. (* decode.c calls read *)
    { repeat econstructor. apply Hb8'. intros [|] Hj.
      - unfold valid_query in Hj. cbn in Hj.
        destruct Hj as (Hj1 & (i & Hj2 & Hj3)).
        unfold Genv.symbol_address in Hj3.
        Transparent semantics2.
        cbn in Hj2. unfold footprint_of_program in Hj2.
        Opaque semantics2.
        destruct (Genv.find_symbol se i) eqn: Hj4; try congruence.
        inv Hj3.
        exploit Genv.find_symbol_injective. apply Hj4. apply Hb7.
        intros ->. cbn in Hj2.
        rewrite PTree.gso in Hj2. rewrite PTree.gss in Hj2.
        inv Hj2. intros HH; inv HH.
      - unfold valid_query in Hj. cbn in Hj.
        destruct Hj as (Hj1 & (i & Hj2 & Hj3)).
        unfold Genv.symbol_address in Hj3.
        Transparent semantics2.
        cbn in Hj2. unfold footprint_of_program in Hj2.
        Opaque semantics2.
        destruct (Genv.find_symbol se i) eqn: Hj4; try congruence.
        inv Hj3.
        exploit Genv.find_symbol_injective. apply Hj4. apply Hb7.
        intros ->. cbn in Hj2.
        rewrite PTree.gso in Hj2. rewrite PTree.gempty in Hj2.
        inv Hj2. intros HH; inv HH. }
    { repeat econstructor. }
    econstructor 4. (* decode.c internal step *)
    { apply star_one. econstructor 1. crush_step. }
    econstructor 4. (* decode.c internal step *)
    { apply star_one. econstructor 1. crush_step. }
    econstructor 4. (* decode.c internal step *)
    { apply star_one. econstructor 1. crush_step. }
    econstructor 4. (* decode.c internal step *)
    { apply star_one. econstructor 1. crush_step. 4: apply Hb4'. 1,4: reflexivity.
      - crush_expr. constructor. reflexivity.
      - crush_expr. constructor. reflexivity. }
    econstructor 4. (* decode.c calls rot13.c *)
    { apply star_one. econstructor 2.
      - econstructor; eauto.
      - instantiate (1 := false). unfold valid_query. split; cbn; try easy.
        exists decode_rot13_id. split.
        Transparent semantics2.
        cbn. unfold footprint_of_program.
        Opaque semantics2.
        reflexivity. unfold Genv.symbol_address.
        cbn in Hb3. rewrite Hb3. reflexivity.
      - rewrite Hrot13_sig. econstructor; eauto.
        + setoid_rewrite SecretAsm.find_funct_spec; eauto.
          cbn. rewrite PTree.gss. reflexivity.
        + reflexivity.
        + repeat constructor.
        + cbn. apply init_mem_nextblock in Hm0. rewrite <- Hm0.
          eapply Mem.nextblock_storebytes in Hm2.
          apply Mem.nextblock_alloc in e. rewrite Hm2. rewrite e.
          unfold Ple. lia. }
    econstructor 4. (* Callstate -> State *)
    { apply star_one. econstructor 1.
      eapply step_internal_function.
      - setoid_rewrite SecretAsm.find_funct_spec; eauto.
        cbn. rewrite PTree.gss. reflexivity.
      - econstructor; cbn; eauto; try solve [ solve_list_disjoint | solve_list_norepet ].
        + apply alloc_variables_nil.
        + erewrite Mem.storebytes_alloc_flag.
          eapply Mem.alloc_flag_alloc2; eauto. eauto. }
    (* loop 5 times *)
    cbn. unfold rot13_body.
    Ltac one_trivial_step := econstructor 4; [ apply star_one; econstructor 1; crush_step; crush_expr | ].
    one_trivial_step.
    econstructor 4. (* unfold Sfor *)
    { apply star_one. econstructor 1. unfold Sfor. crush_step. }
    do 5 one_trivial_step.
    replace (negb (Int.eq Int.one Int.zero)) with true by reflexivity.
    one_trivial_step.
    Ltac sub_modu_add_zero_ext :=
      unfold Int.sub; rewrite !Int.unsigned_repr by (cbn; lia); cbn;
      unfold Int.modu; rewrite !Int.unsigned_repr by (cbn; lia); cbn;
      unfold Int.add; rewrite !Int.unsigned_repr by (cbn; lia); cbn;
      unfold Int.zero_ext; rewrite !Int.unsigned_repr by (cbn; lia); cbn.
    econstructor 4. (* Sassign buf[i] = .. *)
    { apply star_one. econstructor 1. crush_step; crush_expr. }
    do 6 one_trivial_step.
    replace (negb (Int.eq Int.one Int.zero)) with true by reflexivity.
    one_trivial_step.
    econstructor 4. (* Sassign buf[i] = .. *)
    { apply star_one. econstructor 1. crush_step; crush_expr. }
    do 6 one_trivial_step.
    replace (negb (Int.eq Int.one Int.zero)) with true by reflexivity.
    one_trivial_step.
    econstructor 4. (* Sassign buf[i] = .. *)
    { apply star_one. econstructor 1. crush_step; crush_expr. }
    do 6 one_trivial_step.
    replace (negb (Int.eq Int.one Int.zero)) with true by reflexivity.
    one_trivial_step.
    econstructor 4. (* Sassign buf[i] = .. *)
    { apply star_one. econstructor 1. crush_step; crush_expr. }
    do 6 one_trivial_step.
    replace (negb (Int.eq Int.one Int.zero)) with true by reflexivity.
    one_trivial_step.
    econstructor 4. (* Sassign buf[i] = .. *)
    { apply star_one. econstructor 1. crush_step; crush_expr. }
    do 6 one_trivial_step.
    replace (negb (Int.eq Int.zero Int.zero)) with false by reflexivity.
    do 4 one_trivial_step.
    econstructor 4. (* rot13.c returns to decode.c *)
    { apply star_one. econstructor 3; constructor. }
    do 3 one_trivial_step.
    econstructor 4. (* decode.c calls write *)
    { apply star_one. econstructor 1. crush_step; crush_expr.
      constructor. reflexivity.
      constructor. reflexivity. }
    econstructor 2. (* decode.c calls write *)
    { repeat econstructor. apply Hb6'.
      intros [|] Hj.
      - unfold valid_query in Hj. cbn in Hj.
        destruct Hj as (Hj1 & (i & Hj2 & Hj3)).
        unfold Genv.symbol_address in Hj3.
        Transparent semantics2.
        cbn in Hj2. unfold footprint_of_program in Hj2.
        Opaque semantics2.
        destruct (Genv.find_symbol se i) eqn: Hj4; try congruence.
        inv Hj3.
        exploit Genv.find_symbol_injective. apply Hj4. apply Hb5.
        intros ->. cbn in Hj2.
        rewrite PTree.gss in Hj2. inv Hj2.
      - unfold valid_query in Hj. cbn in Hj.
        destruct Hj as (Hj1 & (i & Hj2 & Hj3)).
        unfold Genv.symbol_address in Hj3.
        Transparent semantics2.
        cbn in Hj2. unfold footprint_of_program in Hj2.
        Opaque semantics2.
        destruct (Genv.find_symbol se i) eqn: Hj4; try congruence.
        inv Hj3.
        exploit Genv.find_symbol_injective. apply Hj4. apply Hb5.
        intros ->. cbn in Hj2.
        rewrite PTree.gso in Hj2. rewrite PTree.gempty in Hj2.
        inv Hj2. intros HH; inv HH. }
    { repeat econstructor. }
    econstructor 4. (* decode.c internal step *)
    { apply star_one. econstructor 1. crush_step. }
    econstructor 4. (* decode.c internal step *)
    { apply star_one. econstructor 1. crush_step. }
    econstructor 4. (* decode.c internal step *)
    { apply star_one. econstructor 1. crush_step; crush_expr.
      constructor. reflexivity. }
    econstructor 3.
    { repeat econstructor. }
  Qed.

End DECODE.

(** ** Putting together *)

(** The overall proof corresponds the property (1) in Section 1.1 *)

Section PROOF.
  Import Errors Linking.
  Import -(notations) CallconvAlgebra.
  Opaque linkorder.
  Definition secret_asm := SecretAsm.secret_asm_program.
  Context rot13_asm (Hrot13: match_prog rot13_clight rot13_asm).
  Context sr_asm (Hsr: match_prog sr_clight sr_asm)
    (Hlink_sr: link secret_asm rot13_asm = Some sr_asm).

  Lemma ϕ_secret_cc :
    Γ_secret sr_sk [= load_asm_prog sr_asm.
  Proof.
    etransitivity. apply ϕ_secret.
    rewrite load_sem_correct; eauto.
    unfold load_asm_sem. unfold load_asm_prog. reflexivity.
    apply Asm.semantics_determinate.
    eapply open_fsim_ccref. apply cc_compose_id_right. apply cc_compose_id_right.
    eapply compose_forward_simulations.
    2: { eapply AsmLinking.asm_linking; eauto. }
    assert (sr_sk = erase_program sr_asm).
    { unfold sr_sk. apply Hsk. eauto. }
    rewrite H.
    apply SmallstepLinking.semantics_simulation'; intros [|].
    - cbn. apply SecretAsm.secret_correct. apply Hwin.
    - apply clight2_semantic_preservation; eauto.
    - cbn. apply linkorder_erase_asm.
      apply link_linkorder in Hlink_sr. apply Hlink_sr.
    - cbn. erewrite Hsk; eauto.
      apply linkorder_erase_asm.
      apply link_linkorder in Hlink_sr. apply Hlink_sr.
  Qed.

  Context decode_asm (Hdecode: match_prog decode_clight decode_asm).
  Context dr_asm (Hdr: match_prog dr_clight dr_asm)
    (Hlink_dr: link decode_asm rot13_asm = Some dr_asm).

  Lemma ϕ_decode_cc :
    Γ_decode dr_sk [= load_asm_prog dr_asm.
  Proof.
    etransitivity. apply ϕ_decode.
    rewrite load_sem_correct; eauto.
    unfold load_asm_sem. unfold load_asm_prog. reflexivity.
    apply Asm.semantics_determinate.
    eapply open_fsim_ccref. apply cc_compose_id_right. apply cc_compose_id_right.
    eapply compose_forward_simulations.
    2: { eapply AsmLinking.asm_linking; eauto. }
    assert (dr_sk = erase_program dr_asm).
    { unfold dr_sk. apply Hsk. eauto. }
    rewrite H.
    apply SmallstepLinking.semantics_simulation'; intros [|].
    - apply clight2_semantic_preservation; eauto.
    - apply clight2_semantic_preservation; eauto.
    - cbn. erewrite Hsk; eauto. apply linkorder_erase_asm.
      apply link_linkorder in Hlink_dr. apply Hlink_dr.
    - cbn. erewrite Hsk; eauto. apply linkorder_erase_asm.
      apply link_linkorder in Hlink_dr. apply Hlink_dr.
  Qed.

  Lemma ϕ_1' :
    Γ sr_sk dr_sk [= pipe (load_asm_prog sr_asm) (load_asm_prog dr_asm).
  Proof.
    etransitivity. apply ϕ_1.
    unfold pipe.
    rewrite ϕ_decode_cc.
    rewrite ϕ_secret_cc. reflexivity.
  Qed.
End PROOF.
