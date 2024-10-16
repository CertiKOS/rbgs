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
Require Import Process.
Require Import Asm.
Import Memory Values Integers ListNotations.
Require Import CompCertStrat.
Close Scope list.
Close Scope Z_scope.

(** * §6.3 Modeling loading and the execution environments *)

(** This file contains the verification of the secret and rot13 example using
    the strategy framework presented in the paper. There is also a legacy
    version of this example which can be found in `examples/process/*.v` is
    proved purely using CompCertO structures. The legacy version is not
    presented in the paper but provides some useful infrastructures.

    Particularly, this file depends on:

    - models/IntStrat.v: the stratgy model used as the verification framework;

    - examples/SecretAsm.v: manual verification of assembly program secret.s,
      which corresponds to

        π'_secret : L_secret ≤ Asm(secret.s)

      in the paper;

    - examples/Util.v: various utilities about the CompCertO correctness theorem

 *)

Axiom (Hwin: Archi.win64 = false).

(** * Strategy-level definitions and proof *)

Definition P : esig := {| op := Genv.symtbl; ar _ := Integers.int |}.
Inductive F_op : Type := F_read : int -> F_op | F_write : list byte -> F_op.
Definition F : esig :=
  {|
    op := F_op;
    ar m := match m with F_read _ => list byte | F_write _ => Integers.int end;
  |}.
Definition S : esig := F + F.

Arguments compose_when {E F G}%esig_scope {i j k} p (σ τ)%strat_scope.

Section STRATEGY.

  Context (sk_secret sk_decode: AST.program unit unit).

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

(** * Code Proof *)

Require Import CAsm InitMem Maps AST.
Require Import Conventions Mach Asm.
Require Import Ctypes.
Require Import Util.

Lemma rw_sig_size_arguments: size_arguments rw_sig = 0%Z.
Proof. Transparent Archi.ptr64. cbn. destruct Archi.win64; cbn; lia. Qed.

Section C_LOADER.
  Import Ctypes Clight.
  Context (prog: Clight.program).
  Let sk := AST.erase_program prog.

  Definition entry_c_play (se: Genv.symtbl) q r i : @play li_c P ready :=
    @oq li_c P se ::
    @pq li_c P se (se, q)%embed ::
    @oa li_c P se (se, q)%embed r ::
    @pa li_c P se i :: pnil_ready.
  Inductive valid_entry_c: Genv.symtbl -> c_query -> c_reply -> int -> Prop :=
  | valid_entry_c_intro se b m main f q r i m'
    (HM: init_mem se sk = Some m)
    (HB: Genv.find_symbol se main = Some b)
    (HMAIN: prog_main prog = Some main)
    (HF: (prog_defmap prog) ! main = Some (Gfun f))
    (HQ: q = cq (Vptr b Ptrofs.zero) main_sig []%list m)
    (HR: r = cr (Vint i) m') :
    valid_entry_c se q r i.
  Definition entry_c : li_c ->> P :=
    sup se, sup q, sup r, sup i, sup (_: valid_entry_c se q r i), down (entry_c_play se q r i).

  Definition read_c_play se q n bytes r : @play S li_c ready :=
    @oq S li_c (se, q)%embed ::
    @pq S li_c (se, q)%embed (inl (F_read n)) ::
    @oa S li_c (se, q)%embed (inl (F_read n)) bytes ::
    @pa S li_c (se, q)%embed r :: pnil_ready.
  Inductive valid_read_c: Genv.symtbl -> c_query -> int -> list byte -> c_reply -> Prop :=
  | valid_read_c_intro se q r vf b ofs n m bytes m'
    (HVF: Genv.find_funct (Clight.globalenv se prog) vf = Some read)
    (HREAD: Mem.storebytes m b (Ptrofs.unsigned ofs) (map Byte bytes) = Some m')
    (HLEN: (Z.of_nat (length bytes) <= Int.unsigned n)%Z)
    (HQ: q = cq vf rw_sig [Vint (Int.repr 0); Vptr b ofs; Vint n]%list m)
    (HR: r = cr (Vint (Int.repr (Z.of_nat (length bytes)))) m') :
    valid_read_c se q n bytes r.
  Definition read_c : S ->> li_c :=
    sup se, sup q, sup n, sup bytes, sup r, sup (_: valid_read_c se q n bytes r), down (read_c_play se q n bytes r).
  Definition write_c_play se q bytes n r : @play S li_c ready :=
    @oq S li_c (se, q)%embed ::
    @pq S li_c (se, q)%embed (inr (F_write bytes)) ::
    @oa S li_c (se, q)%embed (inr (F_write bytes)) n ::
    @pa S li_c (se, q)%embed r :: pnil_ready.
  Inductive valid_write_c: Genv.symtbl -> c_query -> list byte -> Int.int -> c_reply -> Prop :=
  | valid_write_c_intro se q r vf b ofs len n m bytes 
    (HVF: Genv.find_funct (Clight.globalenv se prog) vf = Some write)
    (HWRITE: Mem.loadbytes m b (Ptrofs.unsigned ofs) len = Some (map Byte bytes))
    (HI: (0 <= len < Int.modulus - 1)%Z)
    (HQ: q = cq vf rw_sig [Vint (Int.repr 1); Vptr b ofs; Vint (Int.repr len)]%list m)
    (HR: r = cr (Vint n) m) :
    valid_write_c se q bytes n r.
  Definition write_c : S ->> li_c :=
    sup se, sup q, sup bytes, sup n, sup r, sup (_: valid_write_c se q bytes n r), down (write_c_play se q bytes n r).
  Definition runtime_c : S ->> li_c := join read_c write_c.
  Definition load_c_prog : S ->> P :=
    entry_c ⊙ (lts_strat (Clight.semantics1 prog)) ⊙ closure runtime_c.
  Definition load_c_sem (L: Smallstep.semantics li_c li_c) : S ->> P :=
    entry_c ⊙ (lts_strat L) ⊙ closure runtime_c.

End C_LOADER.

Section ASM_LOADER.
  Import Asm.
  Context (prog: Asm.program).
  Let sk := erase_program prog.

  Definition entry_asm_play (se: Genv.symtbl) q r rv : @play li_asm P ready :=
    @oq li_asm P se ::
    @pq li_asm P se (se, q)%embed ::
    @oa li_asm P se (se, q)%embed r ::
    @pa li_asm P se rv :: pnil_ready.
  Inductive valid_entry_asm: Genv.symtbl -> (regset * Mem.mem) -> (regset * Mem.mem) -> int -> Prop :=
  | valid_entry_asm_intro se rs m rs' m' i vf b f main
    (HM: init_mem se sk = Some m)
    (HMAIN: AST.prog_main prog = Some main)
    (HF: (prog_defmap prog) ! main = Some (Gfun f))
    (HB: Genv.find_symbol se main = Some b)
    (HVF: vf = Vptr b Ptrofs.zero)
    (HRS: rs = (((Pregmap.init Vundef) # PC <- vf) # RSP <- vf) # RA <- Vnullptr)
    (HRS': rs'#(IR RAX) = Vint i) :
    valid_entry_asm se (rs, m) (rs', m') i.
  Definition entry_asm : li_asm ->> P :=
    sup se, sup q, sup r, sup i, sup (_: valid_entry_asm se q r i), down (entry_asm_play se q r i).
  Definition read_asm_play se q n bytes r : @play S li_asm ready :=
    @oq S li_asm (se, q)%embed ::
    @pq S li_asm (se, q)%embed (inl (F_read n)) ::
    @oa S li_asm (se, q)%embed (inl (F_read n)) bytes ::
    @pa S li_asm (se, q)%embed r :: pnil_ready.
  Inductive valid_read_asm: Genv.symtbl -> (regset * Mem.mem) -> Int.int -> list byte -> (regset * Mem.mem) -> Prop :=
  | valid_read_asm_intro se (rs: regset) m n bytes rs' m' b ofs
      (HVF: Genv.find_funct (Genv.globalenv se prog) rs#PC = Some read_asm)
      (HDI: rs#RDI = Vint (Int.repr 0))
      (HSI: rs#RSI = Vptr b ofs)
      (HDX: rs#RDX = Vint n)
      (HN: (Z.of_nat (length bytes) <= Int.unsigned n)%Z)
      (HM: Mem.storebytes m b (Ptrofs.unsigned ofs) (map Byte bytes) = Some m')
      (HAX: rs' = (rs#RAX <- (Vint (Int.repr (Z.of_nat (length bytes)))))#PC <- (rs#RA)) :
    valid_read_asm se (rs, m) n bytes (rs', m').
  Definition read_asm : S ->> li_asm :=
    sup se, sup q, sup n, sup bytes, sup r, sup (_: valid_read_asm se q n bytes r), down (read_asm_play se q n bytes r).
  Definition write_asm_play se q bytes n r : @play S li_asm ready :=
    @oq S li_asm (se, q)%embed ::
    @pq S li_asm (se, q)%embed (inr (F_write bytes)) ::
    @oa S li_asm (se, q)%embed (inr (F_write bytes)) n ::
    @pa S li_asm (se, q)%embed r :: pnil_ready.
  Inductive valid_write_asm: Genv.symtbl -> (regset * Mem.mem) -> list byte -> Int.int -> (regset * Mem.mem) -> Prop :=
  | valid_write_asm_intro se (rs: regset) m bytes n rs' b ofs r
      (HVF: Genv.find_funct (Genv.globalenv se prog) rs#PC = Some write_asm)
      (HDI: rs#RDI = Vint (Int.repr 1))
      (HSI: rs#RSI = Vptr b ofs)
      (HDX: rs#RDX = Vint (Int.repr n))
      (* HI is for determinism *)
      (HI: (0 <= n < Int.modulus - 1)%Z)
      (HM: Mem.loadbytes m b (Ptrofs.unsigned ofs) n = Some (map Byte bytes))
      (HAX: rs' = (rs#RAX <- (Vint r))#PC <- (rs#RA)) :
    valid_write_asm se (rs, m) bytes r (rs', m).
  Definition write_asm : S ->> li_asm :=
    sup se, sup q, sup bytes, sup n, sup r, sup (_: valid_write_asm se q bytes n r), down (write_asm_play se q bytes n r).
  Definition runtime_asm : S ->> li_asm := join read_asm write_asm.
  Definition load_asm_prog : S ->> P :=
    entry_asm ⊙ (lts_strat (Asm.semantics prog)) ⊙ closure runtime_asm.
  Definition load_asm_sem (L: Smallstep.semantics li_asm li_asm) : S ->> P :=
    entry_asm ⊙ (lts_strat L) ⊙ closure runtime_asm.

End ASM_LOADER.

Local Hint Constructors pcoh : core.

Instance runtime_asm_determ tp: Deterministic (runtime_asm tp).
Proof.
  Ltac dd := dependent destruction Hs; dependent destruction Ht; eauto.
  Ltac om := match goal with
    | [ |- pcoh (oq ?x :: _) (oq ?y :: _) ] =>
        let H := fresh "H" in
        destruct (classic (x = y)); [ inv H | ]; eauto
    | [ |- pcoh (oa ?x :: _) (oa ?y :: _) ] =>
        let H := fresh "H" in
        destruct (classic (x = y)); [ inv H | ]; eauto
    end.
  split. intros s t Hs Ht.
  unfold runtime_asm in *.
  destruct Hs as [[|] (?&?&?&?&?&Hs1&Hs)];
    destruct Ht as [[|] (?&?&?&?&?&Ht1&Ht)]; cbn in *; dd.
  - om. constructor. dd.
    assert (x1 = x6) as ->.
    { inv Hs1. inv Ht1. congruence. }
    constructor. dd.
    om. constructor. dd.
    inv Hs1. inv Ht1.
    rewrite HSI in HSI0. inv HSI0.
    rewrite HM in HM0. inv HM0. repeat constructor. dd.
  - inv Ht1. inv Hs1. eapply pcons_pcoh_oq; eauto.
    intros A. inv A. rewrite HDI in HDI0. inv HDI0.
  - inv Ht1. inv Hs1. eapply pcons_pcoh_oq; eauto.
    intros A. inv A. rewrite HDI in HDI0. inv HDI0.
  - om. constructor. dd.
    assert (x1 = x6) as <-.
    { inv Hs1. inv Ht1. rewrite HSI in HSI0. inv HSI0.
      rewrite HDX in HDX0.
      exploit int_repr_inj. apply HI. apply HI0. congruence.
      intros <-. rewrite HM in HM0.
      inv HM0. eapply map_inj; eauto.
      intros. inv H. easy. }
    constructor. dd.
    om. constructor. dd. dd.
    inv Hs1. inv Ht1. repeat constructor.
Qed.

Section LOADER_CORRECT.
  Context p tp (Hp: match_prog p tp).

  Lemma Hsk: erase_program p = erase_program tp.
  Proof.
    apply clight2_semantic_preservation in Hp.
    destruct Hp. destruct X. apply fsim_skel.
  Qed.

  Transparent Archi.ptr64.
  Opaque match_prog.

  Lemma entry_correct: rsq CAsm.cc_compcert vid (entry_c p) (entry_asm tp).
  Proof.
    intros x (se & q & r & i & H & Hx). inv H. cbn in Hx. rewrite Hx. clear Hx.
    assert (Hmain: (prog_defmap (erase_program p)) ! main = Some (Gfun tt)).
    { rewrite erase_program_defmap. unfold option_map. setoid_rewrite HF. reflexivity. }
    assert (exists tf, (prog_defmap tp) ! main = Some (Gfun tf)) as (tf & Htf).
    { rewrite Hsk in Hmain. rewrite erase_program_defmap in Hmain.
      unfold option_map in Hmain.
      destruct (prog_defmap tp) ! main as [[tf|]|] eqn: Htf; inv Hmain.
      exists tf. split; eauto. }
    assert (Htpmain: AST.prog_main tp = Some main).
    { replace (AST.prog_main tp) with (AST.prog_main (erase_program tp)) by reflexivity.
      rewrite <- Hsk. apply HMAIN. }
    unfold entry_c_play. apply rsp_oq. {
      cbn. eexists se, (_, m), ((Pregmap.init Vundef)#RAX <- (Vint i), m'), i.
      eexists. econstructor; eauto.
      - rewrite <- Hsk. eauto.
      - constructor. }
    intros q Hq. cbn in Hq. subst q.
    set (rs :=  (((Pregmap.init Vundef) # PC <- (Vptr b Ptrofs.zero)) # RSP <- (Vptr b Ptrofs.zero)) # RA <- Vnullptr).
    eapply rsp_pq with (m2 := (se, Datatypes.pair rs m)%embed).

    assert (exists w, LanguageInterface.match_query cc_compcert w
      {| cq_vf := Vptr b Ptrofs.zero; cq_sg := main_sig; cq_args := []; cq_mem := m |} (rs, m) /\ match_senv cc_compcert w se se).
    {
      eexists. split.
      - unfold cc_compcert.
        (* cklr *)
        cbn. instantiate (1 := (se, existT _ 0%nat _, _)).
        exists (cq (Vptr b Ptrofs.zero) main_sig [] m). split.
        { reflexivity. }
        (* inv wt_c *)
        instantiate (1 := (se, (se, main_sig), _)).
        exists (cq (Vptr b Ptrofs.zero) main_sig [] m). split.
        { repeat constructor. }
        (* lessdef_c *)
        instantiate (1 := (se, tt, _)).
        exists (cq (Vptr b Ptrofs.zero) main_sig [] m). split.
        { repeat constructor. }
        (* cc_c_asm *)
        instantiate (1 := (se, caw main_sig
                    (((Pregmap.init Vundef) # PC
                      <- (Vptr b Ptrofs.zero)# RSP
                      <- (Vptr b Ptrofs.zero))# RA
                     <- Vnullptr) m, _)).
        eexists ((((Pregmap.init Vundef) # PC
                   <- (Vptr b Ptrofs.zero)) # RSP
                  <- (Vptr b Ptrofs.zero)) # RA
                 <- Vnullptr, m). split.
        { econstructor; cbn; try constructor; eauto.
          - destruct Archi.win64; cbn; try easy.
          - repeat constructor. red. unfold size_arguments.
            cbn. destruct Archi.win64; reflexivity.
          - erewrite init_mem_nextblock; eauto.
            exploit @Genv.genv_symb_range; eauto.
          - easy.
          - easy. }
        (* cc_asm vainj *)
        instantiate (1 := (se, Inject.injw (Mem.flat_inj (Mem.nextblock m)) (Mem.nextblock m) (Mem.nextblock m))).
        repeat apply conj; cbn; eauto; try easy.
        + intros.
          assert (Val.inject (Mem.flat_inj (Mem.nextblock m)) (Vptr b Ptrofs.zero) (Vptr b Ptrofs.zero)).
          { eapply Val.inject_ptr. unfold Mem.flat_inj.
             destruct plt. reflexivity.
             exfalso. apply n. erewrite init_mem_nextblock; eauto.
             eapply Genv.genv_symb_range; eauto.
             reflexivity. }
          destruct r; eauto; cbn; try constructor; eauto.
          destruct i0; eauto; cbn.
        + constructor; cbn.
          * erewrite init_mem_nextblock; eauto. reflexivity.
          * eapply InitMem.init_mem_romatch. eauto.
          * constructor. eapply initmem_inject; eauto.
      - cbn. repeat apply conj; eauto. constructor. eauto.
        constructor; cbn; erewrite init_mem_nextblock; eauto; try easy.
        apply Load.match_stbls_flat_inj.
    }

    destruct H as (w & Hq & Hse).  econstructor; eauto.
    eapply rsp_oa. {
      cbn. eexists se, (_, m), ((Pregmap.init Vundef)#RAX <- (Vint i), m'), i.
      eexists. econstructor; eauto.
      - rewrite <- Hsk. eauto.
      - repeat constructor. }
    intros [rs1 m1] Hr. eapply rcp_forbid_mr in Hr; eauto.
    3: {
      unfold cc_compcert.
      (* cklr *)
      cbn. instantiate (1 := (se, existT _ 0%nat _, _)).
      exists (cq (Vptr b Ptrofs.zero) main_sig [] m). split.
      { reflexivity. }
      (* inv wt_c *)
      instantiate (1 := (se, (se, main_sig), _)).
      exists (cq (Vptr b Ptrofs.zero) main_sig [] m). split.
      { repeat constructor. }
      (* lessdef_c *)
      instantiate (1 := (se, tt, _)).
      exists (cq (Vptr b Ptrofs.zero) main_sig [] m). split.
      { repeat constructor. }
      (* cc_c_asm *)
      instantiate (1 := (se, caw main_sig
                               (((Pregmap.init Vundef) # PC
                                 <- (Vptr b Ptrofs.zero)# RSP
                                 <- (Vptr b Ptrofs.zero))# RA
                                <- Vnullptr) m, _)).
      eexists ((((Pregmap.init Vundef) # PC
                 <- (Vptr b Ptrofs.zero)) # RSP
                <- (Vptr b Ptrofs.zero)) # RA
               <- Vnullptr, m). split.
      { econstructor; cbn; try constructor; eauto.
        - destruct Archi.win64; cbn; try easy.
        - repeat constructor. red. unfold size_arguments.
          cbn. destruct Archi.win64; reflexivity.
        - erewrite init_mem_nextblock; eauto.
          exploit @Genv.genv_symb_range; eauto.
        - easy.
        - easy. }
      (* cc_asm vainj *)
      instantiate (1 := (se, Inject.injw (Mem.flat_inj (Mem.nextblock m)) (Mem.nextblock m) (Mem.nextblock m))).
      repeat apply conj; cbn; eauto; try easy.
      + intros.
        assert (Val.inject (Mem.flat_inj (Mem.nextblock m)) (Vptr b Ptrofs.zero) (Vptr b Ptrofs.zero)).
        { eapply Val.inject_ptr. unfold Mem.flat_inj.
          destruct plt. reflexivity.
          exfalso. apply n. erewrite init_mem_nextblock; eauto.
          eapply Genv.genv_symb_range; eauto.
          reflexivity. }
        destruct r; eauto; cbn; try constructor; eauto.
        destruct i0; eauto; cbn.
      + constructor; cbn.
        * erewrite init_mem_nextblock; eauto. reflexivity.
        * eapply InitMem.init_mem_romatch. eauto.
        * constructor. eapply initmem_inject; eauto.
    }
    2: {
      cbn. repeat apply conj; eauto. constructor. eauto.
      constructor; cbn; erewrite init_mem_nextblock; eauto; try easy.
      apply Load.match_stbls_flat_inj.
    }
    cbn in Hr. destruct Hr as (r3 & Hr3 & HR). inv Hr3.
    destruct HR as (r3 & Hr3 & HR). inv Hr3.
    destruct HR as (r3 & Hr3 & HR). inv Hr3. inv H3.
    destruct HR as (r3 & Hr3 & HR). inv Hr3. cbn in *.
    destruct HR as ((? & ?) & ? & Hr). 
    inv Hr. specialize (H1 RAX). rewrite <- H5 in H1.
    cbn in H1. inv H1.

    eapply rsp_pa with (r2 := i).
    { intros Hx. inv Hx. apply H3. apply JMeq_refl. }
    apply rsp_ready. cbn. eexists _, (rs, _), (rs1, _), _. eexists.
    { econstructor; eauto.
      * rewrite <- Hsk. eauto.
      * subst rs. cbn. rewrite H12. easy. }
    unfold entry_asm_play. reflexivity.
    Unshelve. all: cbn; exact tt.
  Qed.

  Import Compiler CKLR VAInject Inject.
  Import -(notations) CallconvAlgebra.
  Definition inj_state := (block * ptrofs * Mem.mem)%type.
  Inductive match_inj_state:
    ccworld (cc_star cc_cklrs) -> world vainj -> cc_ca_world -> inj_state -> inj_state -> Prop :=
  | match_inj_state_intro wn wi b1 ofs1 m1 b2 ofs2 m2 caw se 
      (HM: Load.mm_ca wn (se, wi) (caw_m caw) m1 m2) (HP: Load.mp_ca wn wi b1 ofs1 b2 ofs2):
      match_inj_state wn (se, wi) caw (b1, ofs1, m1) (b2, ofs2, m2).

  Lemma runtime_correct: rsq vid CAsm.cc_compcert (runtime_c p) (runtime_asm tp).
  Proof.
    setoid_rewrite cc_conv_expand. apply rsq_sup. apply runtime_asm_determ.
    { constructor. apply None. }
    intros [w|].
    2: { intros s ([|] & Hs).
         - destruct Hs as (se & q & n & bs & r & H & Hs). rewrite Hs. clear Hs.
           unfold read_c_play. apply rsp_oq. {
             exists true. cbn. inv H. eexists se, (((((Pregmap.init Vundef)#PC <- vf)#RDI <- (Vint (Int.repr 0))#RSI <- (Vptr b ofs))#RDX <- (Vint n)), m), n, bs, (_, m').
             eexists. 2: constructor.
             econstructor; cbn; eauto.
             eapply match_prog_read. 4: eauto.
             apply Hp.
             apply Genv.match_stbls_id.
             apply val_inject_refl. }
           intros q2 Hq2. xinv Hq2.
         - destruct Hs as (se & q & bs & n & r & H & Hs). rewrite Hs. clear Hs.
           unfold write_c_play. apply rsp_oq. {
             exists false. cbn. inv H. eexists se, (((((Pregmap.init Vundef)#PC <- vf)#RDI <- (Vint (Int.repr 1))#RSI <- (Vptr b ofs))#RDX <- (Vint (Int.repr len))), m), bs, n, (_, m).
             eexists. 2: constructor.
             econstructor; cbn; eauto.
             eapply match_prog_write. 4: eauto.
             apply Hp.
             apply Genv.match_stbls_id.
             apply val_inject_refl. }
           intros q2 Hq2. xinv Hq2. }
    intros s (i & Hs). destruct i; cbn in Hs.
    Ltac inv_lessdef:=
      match goal with
      | [ H: Val.lessdef_list _ _ |- _ ] => inv H
      | [ H: Val.lessdef _ _ |- _ ] => inv H
      end.
    - destruct Hs as (se & q & n & bs & r & H & Hs). rewrite Hs. clear Hs.
      inv H. unfold read_c_play. apply rsp_oq. {
        exists true. cbn. eexists se, (((((Pregmap.init Vundef)#PC <- vf)#RDI <- (Vint (Int.repr 0))#RSI <- (Vptr b ofs))#RDX <- (Vint n)), m), n, bs, (_, m').
        eexists. 2: constructor.
        econstructor; cbn; eauto.
        eapply match_prog_read. 4: eauto.
        apply Hp.
        apply Genv.match_stbls_id.
        apply val_inject_refl. }
      intros q Hq. cbn in Hq. dependent destruction Hq.
      eapply rsp_pq with (m2 := inl (F_read n)). reflexivity.
      eapply rsp_oa. {
        exists true. cbn. 
      set (w1 := (Load.nw_of_world w)). set (w2 := (Load.injw_of_world w)). set (w3 := (Load.caw_of_world w)).
      unfold CAsm.cc_compcert in *. cbn in w, HM |- *.
      eprod_crush. destruct s7.
      match goal with
      | [ H: Invariant.rel_inv _ _ _ |- _ ] => inv H; eprod_crush; subst
      end.
      (* cklrs *)
      eapply (Load.cklrs_match_query_inv' (existT _ x2 c0)) in H as
          (mx & bx & ofsx & vfx & Hqx & Hmx & Hpx & Hvx). subst x0. cbn in *.
      (* lessdef *)
      inv H1. repeat inv_lessdef.
      (* cc_c_asm: need to show args_removed changes nothing *)
      inv H2. inv HRM. inv H.
      2: { match goal with
          | [ H: size_arguments _ > 0 |- _ ] => rewrite rw_sig_size_arguments in H  end.
           lia. }
      (* cc_asm vainj *)
      destruct m2. destruct H3 as (Hreg & Hpc & Him).
      (* arguments *)
      match goal with
      | [ H: cons _ _ = _ |- _ ] => cbn in H; rewrite Hwin in H; cbn in H; inv H
      end.

      assert (exists b' ofs', r0#RSI = Vptr b' ofs' /\ Val.inject i (Vptr bx ofsx) (Vptr b' ofs')) as (b' & ofs' & Hofs & Hb').
      { specialize (Hreg RSI). rewrite <- H2 in Hreg. inv Hreg.
        eexists _, _. split; eauto. }

      assert (HMS: match_inj_state w1 w2 w3 (b, ofs, m) (b', ofs', m0)).
      { econstructor.
        (* mem *)
        - inv Him. econstructor; eauto. reflexivity.
          cbn. apply Mem.unchanged_on_refl.
        (* ptr *)
        - econstructor; eauto. inv Hb'. constructor; eauto. }
      inv HMS.
      exploit Load.ca_storebytes; eauto. intros (mx1 & Hs & Hm).
      inv Hm.

        eexists _, _, _, _, (_, _).
        eexists.
        2: { unfold read_asm_play. repeat constructor. }
        econstructor; eauto.
      + cbn in HVF. cbn in HSE.  eprod_crush. inv H8.
        eapply ca_find_funct_read; eauto.
        apply H7. apply HVF.
      + specialize (Hreg RDI). rewrite <- H0 in Hreg. inv Hreg; eauto.
      + specialize (Hreg RDX). rewrite <- H3 in Hreg. inv Hreg; eauto.
      }
      intros r2 H2. cbn in H2. apply not_and_or in H2 as [H2|H2]. easy.
      assert (bs = r2) as <-.
      { apply NNPP. intros Hx. apply H2. intros Hy. apply Hx.
        apply JMeq_eq; eauto. } clear H2.

      set (w1 := (Load.nw_of_world w)). set (w2 := (Load.injw_of_world w)). set (w3 := (Load.caw_of_world w)).
      unfold CAsm.cc_compcert in *. cbn in w, HM |- *.
      eprod_crush. destruct s7.
      match goal with
      | [ H: Invariant.rel_inv _ _ _ |- _ ] => inv H; eprod_crush; subst
      end.
      (* cklrs *)
      eapply (Load.cklrs_match_query_inv' (existT _ x2 c0)) in H as
          (mx & bx & ofsx & vfx & Hqx & Hmx & Hpx & Hvx). subst x0. cbn in *.
      (* lessdef *)
      inv H1. repeat inv_lessdef.
      (* cc_c_asm: need to show args_removed changes nothing *)
      inv H2. inv HRM. inv H.
      2: { match goal with
          | [ H: size_arguments _ > 0 |- _ ] => rewrite rw_sig_size_arguments in H  end.
           lia. }
      (* cc_asm vainj *)
      destruct m2. destruct H3 as (Hreg & Hpc & Him).
      (* arguments *)
      match goal with
      | [ H: cons _ _ = _ |- _ ] => cbn in H; rewrite Hwin in H; cbn in H; inv H
      end.

      assert (exists b' ofs', r0#RSI = Vptr b' ofs' /\ Val.inject i (Vptr bx ofsx) (Vptr b' ofs')) as (b' & ofs' & Hofs & Hb').
      { specialize (Hreg RSI). rewrite <- H2 in Hreg. inv Hreg.
        eexists _, _. split; eauto. }

      assert (HMS: match_inj_state w1 w2 w3 (b, ofs, m) (b', ofs', m0)).
      { econstructor.
        (* mem *)
        - inv Him. econstructor; eauto. reflexivity.
          cbn. apply Mem.unchanged_on_refl.
        (* ptr *)
        - econstructor; eauto. inv Hb'. constructor; eauto. }
      inv HMS.
      exploit Load.ca_storebytes; eauto. intros (mx1 & Hs & Hm).
      inv Hm.
      set (v := (Vint (Int.repr (Z.of_nat (length bs))))).
      eapply rsp_pa with (r2 := ((r0#RAX <- v)#PC <- (r0#RA), mx1)).
      {
        intros HR. cbn in HR. dependent destruction HR. apply HN0. clear HM0 HN0.

        (* m --store--> m'
           |            |
           |          mm_cklr
           |            |
         mm_ca          m2
           |            |
           |           inj
           |            |
          m0 --store--> mx1
         *)

        eexists (cr v m2). split.
        { eapply Load.cklrs_match_reply_intro; eauto. }
        eexists (cr v m2). split.
        (* need sig *)
        { constructor. easy. }
        eexists (cr v m2). split.
        { constructor. constructor. }
        exists ((r#RAX <- v)#PC <- (r#RA), m2). split.
        { cbn in Hreg |- *.
          (* destruct w3; cbn in HSG, HRS |- *. *)
          (* subst caw_sg.  *)
          constructor; eauto.
          - intros r1. destruct r1; cbn; eauto. easy.
          - apply Mem.unchanged_on_refl.
          - rewrite rw_sig_size_arguments.
            replace (loc_init_args 0 (r RSP))
              with (fun (_: block) (_: Z) => False); eauto.
            repeat (apply Axioms.functional_extensionality; intros).
            apply PropExtensionality.propositional_extensionality.
            split; try easy. intros HX. inv HX. lia.
          - rewrite rw_sig_size_arguments.
            intros * HX. inv HX. lia. }
        { exists (s0, wj). split. split; eauto. split.
          - intros. cbn in Hreg. apply (mi_acc inj) in HJ.
            destruct r1; cbn; eauto. 
            destruct i0; cbn; eauto.
            subst v. eauto.
          - constructor; eauto. }
      }

      apply rsp_ready. exists true.
      eexists _, (r0, m0), _, _, ((r0#RAX <- v)#PC <- (r0#RA), mx1).
      eexists.
      { econstructor; eauto.
      + cbn in HVF. cbn in HSE.  eprod_crush. inv r1.
        eapply ca_find_funct_read; eauto.
        apply m1. apply HVF.
      + specialize (Hreg RDI). rewrite <- H0 in Hreg. inv Hreg; eauto.
      + specialize (Hreg RDX). rewrite <- H3 in Hreg. inv Hreg; eauto.
      }
      cbn. reflexivity.
    - destruct Hs as (se & q & bs & n & r & H & Hs). rewrite Hs. clear Hs.
      inv H. unfold write_c_play. apply rsp_oq. {
        exists false. cbn. eexists se, (((((Pregmap.init Vundef)#PC <- vf)#RDI <- (Vint (Int.repr 1))#RSI <- (Vptr b ofs))#RDX <- (Vint (Int.repr len))), m), bs, n, (_, m).
        eexists. 2: constructor.
        econstructor; cbn; eauto.
        eapply match_prog_write. 4: eauto.
        apply Hp.
        apply Genv.match_stbls_id.
        apply val_inject_refl.
      }
      intros q Hq. cbn in Hq. dependent destruction Hq.
      eapply rsp_pq with (m2 := inr (F_write bs)). reflexivity.
      eapply rsp_oa. {
        exists false. cbn.

      set (w1 := (Load.nw_of_world w)). set (w2 := (Load.injw_of_world w)). set (w3 := (Load.caw_of_world w)).
      destruct m2 as [rs mt].
      unfold CAsm.cc_compcert in *. cbn in w, HM |- *.
      destruct HI as [HI1 HI2].
      eprod_crush. destruct s7.
      match goal with
      | [ H: Invariant.rel_inv _ _ _ |- _ ] => inv H; eprod_crush; subst
      end.
      eapply (Load.cklrs_match_query_inv' (existT _ x2 c0)) in H as
          (mx & bx & ofsx & vfx & Hqx & Hmx & Hpx & Hvx). subst x0. cbn in *.
      (* lessdef *)
      inv H1. repeat inv_lessdef.
      (* cc_c_asm: need to show args_removed changes nothing *)
      inv H2. inv HRM. inv H.
      2: { match goal with
        | [ H: size_arguments _ > 0 |- _ ] =>
            rewrite rw_sig_size_arguments in H; try lia  end. }
      (* cc_asm vainj *)
      destruct H3 as (Hreg & Hpc & Him).
      (* arguments *)
      match goal with
      | [ H: cons _ _ = _ |- _ ] => cbn in H; rewrite Hwin in H; cbn in H; inv H
      end.
      assert (exists b' ofs', rs#RSI = Vptr b' ofs' /\ Val.inject i (Vptr bx ofsx) (Vptr b' ofs')) as (b' & ofs' & Hofs & Hb').
      { specialize (Hreg RSI). rewrite <- H2 in Hreg. inv Hreg.
        eexists _, _. split; eauto. }
      assert (HCA: Load.mm_ca w1 w2 (caw_m w3) m mt).
      { inv Him. econstructor; eauto. reflexivity.
        apply Mem.unchanged_on_refl. }

        eexists _, _, _, _, (_, _).
        exists. 2: { repeat constructor. }
         econstructor; cbn; eauto.
        + cbn in HVF. cbn in HSE.  eprod_crush. inv H8.
          eapply ca_find_funct_write; eauto.
          apply H7. apply HVF.
        + specialize (Hreg RDI). rewrite <- H0 in Hreg. inv Hreg; eauto.
        + specialize (Hreg RDX). rewrite <- H3 in Hreg. inv Hreg; eauto.
        + inv Him. eapply Load.ca_loadbytes; eauto.
          econstructor; eauto. inv Hb'. constructor; eauto.
      }
      intros r2 H2. cbn in H2. apply not_and_or in H2 as [H2|H2]. easy.
      assert (n = r2) as <-.
      { apply NNPP. intros Hx. apply H2. intros Hy. apply Hx.
        apply JMeq_eq; eauto. } clear H2.
      set (w1 := (Load.nw_of_world w)). set (w2 := (Load.injw_of_world w)). set (w3 := (Load.caw_of_world w)).
      destruct m2 as [rs mt].
      unfold CAsm.cc_compcert in *. cbn in w, HM |- *.
      destruct HI as [HI1 HI2].
      eprod_crush. destruct s7.
      match goal with
      | [ H: Invariant.rel_inv _ _ _ |- _ ] => inv H; eprod_crush; subst
      end.
      eapply (Load.cklrs_match_query_inv' (existT _ x2 c0)) in H as
          (mx & bx & ofsx & vfx & Hqx & Hmx & Hpx & Hvx). subst x0. cbn in *.
      (* lessdef *)
      inv H1. repeat inv_lessdef.
      (* cc_c_asm: need to show args_removed changes nothing *)
      inv H2. inv HRM. inv H.
      2: { match goal with
        | [ H: size_arguments _ > 0 |- _ ] =>
            rewrite rw_sig_size_arguments in H; try lia  end. }
      (* cc_asm vainj *)
      destruct H3 as (Hreg & Hpc & Him).
      (* arguments *)
      match goal with
      | [ H: cons _ _ = _ |- _ ] => cbn in H; rewrite Hwin in H; cbn in H; inv H
      end.
      assert (exists b' ofs', rs#RSI = Vptr b' ofs' /\ Val.inject i (Vptr bx ofsx) (Vptr b' ofs')) as (b' & ofs' & Hofs & Hb').
      { specialize (Hreg RSI). rewrite <- H2 in Hreg. inv Hreg.
        eexists _, _. split; eauto. }
      
      set (v := (Vint n)).
      eapply rsp_pa with (r2 := ((rs#RAX <- v)#PC <- (rs#RA), mt)).
      {
        intros HR. cbn in HR. dependent destruction HR. apply HN. clear HM HN.
        eexists (cr v mx). split.
        { eapply Load.cklrs_match_reply_intro; eauto. }
        eexists (cr v mx). split.
        (* need sig *)
        { constructor. easy. }
        eexists (cr v mx). split.
        { constructor. constructor. }
        exists ((r#RAX <- v)#PC <- (r#RA), mx). split.
        { cbn in Hreg |- *. constructor; eauto.
          - intros r1. destruct r1; cbn; eauto. easy.
          - apply Mem.unchanged_on_refl.
          - apply Mem.unchanged_on_refl.
          - rewrite rw_sig_size_arguments.
            intros * HX. inv HX. lia. }
        { exists (s0, i). split. reflexivity. split; eauto.
          intros. cbn in Hreg. destruct r0; cbn; eauto. destruct i0; cbn; eauto.
          subst v. eauto. }
      }

      assert (HCA: Load.mm_ca w1 w2 (caw_m w3) m mt).
      { inv Him. econstructor; eauto. reflexivity.
        apply Mem.unchanged_on_refl. }

      apply rsp_ready. exists false.
      eexists _, (rs, mt), _, _, ((rs#RAX <- v)#PC <- (rs#RA), mt).
      eexists.
      { econstructor; eauto.
        + cbn in HVF. cbn in HSE.  eprod_crush. inv r0.
          eapply ca_find_funct_write; eauto.
          apply m0. apply HVF.
        + specialize (Hreg RDI). rewrite <- H0 in Hreg. inv Hreg; eauto.
        + specialize (Hreg RDX). rewrite <- H3 in Hreg. inv Hreg; eauto.
        + inv Him. eapply Load.ca_loadbytes; eauto.
          econstructor; eauto. inv Hb'. constructor; eauto.
        + cbn. reflexivity. }
      cbn. reflexivity.
      Unshelve. exact (Int.repr 0).
  Qed.

  Lemma load_sem_correct L_c L_asm:
    determinate L_asm ->
    forward_simulation CAsm.cc_compcert CAsm.cc_compcert L_c L_asm ->
    load_c_sem p L_c [= load_asm_sem tp L_asm.
  Proof.
    intros HD HL. eapply rsq_id_conv with (p := rs_ready).
    eapply rsq_comp_when. constructor. apply entry_correct.
    eapply rsq_comp_when. constructor.
    2: { apply rsq_closure. 3: apply runtime_correct.
         1-2: eauto with typeclass_instances. }
    apply fsim_rsq; eauto.
  Qed.

  (* Lemma load_prog_correct : *)
  (*   load_c_prog p [= load_asm_prog tp. *)
  (* Abort. *)
End LOADER_CORRECT.

(** ** Rot13 Clight Program *)

Require Import Clight Ctypes Cop.

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
    Scall None (Evar rot13_write_id rw_type) [ one; buf; n ]
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
    assert (exists m2, Mem.storebytes m1 bb1 0 (Byte ## uryyb_bytes) = Some m2) as (m2 & Hm2).
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
      - crush_expr. eapply eval_Ecast. crush_expr. all: reflexivity. }
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
      - crush_expr. }
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
    { apply star_one. econstructor 1. crush_step; crush_expr. }
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
    { apply star_one. econstructor 1. crush_step; crush_expr. }
    econstructor 3.
    { repeat econstructor. }
  Qed.

End DECODE.

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
