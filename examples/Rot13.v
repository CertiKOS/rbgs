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

From compcert.common Require Import LanguageInterface Smallstep Globalenvs.
From compcert.process Require Import Process.
Require Import Asm.
Import Memory Values Integers ListNotations.
Require Import CompCertStrat.
Close Scope list.
Close Scope Z_scope.

Axiom (Hwin: Archi.win64 = false).

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

Definition P : esig := {| op := Genv.symtbl; ar _ := Integers.int |}.
Inductive F_op : Type := F_read : Integers.int64 -> F_op | F_write : list byte -> F_op.
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
      @pq S P se (inl (F_read (Int64.repr 100))) ::
      @oa S P se (inl (F_read (Int64.repr 100))) uryyb_bytes ::
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
      (Hd: d = app d1 d2) (Hn: Int64.unsigned n = Z.of_nat (length d1)) (Hs: fifo_play d2 ready s):
    fifo_play d ready (@oq 0 F (F_read n) :: @pa 0 F (F_read n) d1 :: s)
  | fifo_read_all n d s (Hn: (Int64.unsigned n > Z.of_nat (length d))%Z) (Hs: fifo_play nil ready s):
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
    (p1 + p2)%strat ⊙
    α+ ⊙
    (α'+ + id F)%strat ⊙
    (id F + (Δ+ ⊙ fifo) + id F)%strat ⊙
    (ρ'+ + id F)%strat.

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

    (* (F+F) + (F+F) ---> ((F+F)+F) + F *)

    apply falph_question_l. apply falph_answer_l.
    apply falph_question_m. apply falph_answer_m.
    apply falph_question_r. apply falph_answer_r.
    apply falph_ready.

    2: { apply comp_oq. apply comp_lq. apply comp_ra. apply comp_la.
         apply comp_oq. apply comp_lq. apply comp_ra.
         repeat constructor. }

    Unshelve. 2: refine pnil_ready.
    eexists _, _. repeat apply conj.

    (* ((F+F)+F) + F ---> F + (F+F) + F *)

    eexists _, _. repeat apply conj.
    cbn. apply falphr_question_m. apply falphr_answer_m.
    apply falphr_question_r. apply falphr_answer_r. apply falphr_ready.

    cbn. apply id_has_q. apply id_has_a. apply id_has_pnil_ready.

    (* left by default. so this is what we want *)
    repeat constructor.

    2: { repeat constructor. }.

    Unshelve. 2: refine pnil_ready.
    eexists _, _. repeat apply conj.

    (* F + (F+F) + F ---> F + 0 + F *)
    eexists _, _. repeat apply conj.
    2: { cbn. apply id_has_q. apply id_has_a. apply id_has_pnil_ready. }
    eexists _, _. repeat apply conj. apply id_has_pnil_ready.

    eexists _, _. repeat apply conj.
    cbn. apply fdel_question_l. apply fdel_answer_l. apply fdel_question_r. apply fdel_answer_r. apply fdel_ready.
    cbn. eapply fifo_write with (d1 := uryyb_bytes).
    rewrite app_nil_l. reflexivity. cbn.
    instantiate (1 := (Int.repr 5)). reflexivity.
    eapply fifo_read_all with (n := (Int64.repr 100)). cbn.
    rewrite Int64.unsigned_repr. lia. cbn. lia. apply fifo_nil.

    repeat constructor.
    repeat constructor.
    repeat constructor.
    2: repeat constructor.

    (* F + 0 + F ---> F + F *)

    Unshelve. 2: refine pnil_ready.
    eexists _, _. repeat apply conj.
    cbn. apply frhor_ready.
    cbn. apply id_has_q with (m := F_write hello_bytes).
    apply id_has_a with (n := (Int.repr 5)). apply id_has_pnil_ready.

    eapply fcomp_oq_r.
    eapply (fcomp_pq_r (E1 := F) (E2 := F)).
    eapply (fcomp_oa_r (E1 := F) (E2 := F)).
    eapply (fcomp_pa_r (E1 := F) (E2 := F)).
    constructor.
  Qed.

End STRATEGY.


Require Import CAsm Load InitMem Maps AST.
Require Import Conventions Mach Asm.

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
  Inductive valid_read_c: Genv.symtbl -> c_query -> Int64.int -> list byte -> c_reply -> Prop :=
  | valid_read_c_intro se q r vf b ofs n m bytes m'
    (HVF: Genv.find_funct (Clight.globalenv se prog) vf = Some read)
    (HREAD: Mem.storebytes m b (Ptrofs.unsigned ofs) (map Byte bytes) = Some m')
    (HLEN: (Z.of_nat (length bytes) <= Int64.unsigned n)%Z)
    (HQ: q = cq vf rw_sig [Vint (Int.repr 0); Vptr b ofs; Vlong n]%list m)
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
    (HQ: q = cq vf rw_sig [Vint (Int.repr 1); Vptr b ofs; Vlong (Int64.repr len)]%list m)
    (HR: r = cr (Vint n) m) :
    valid_write_c se q bytes n r.
  Definition write_c : S ->> li_c :=
    sup se, sup q, sup bytes, sup n, sup r, sup (_: valid_write_c se q bytes n r), down (write_c_play se q bytes n r).
  Definition runtime_c : S ->> li_c := join read_c write_c.
  Definition load_c_prog : S ->> P :=
    entry_c ⊙ (lts_strat (Clight.semantics1 prog)) ⊙ runtime_c.
  Definition load_c_sem (L: Smallstep.semantics li_c li_c) : S ->> P :=
    entry_c ⊙ (lts_strat L) ⊙ runtime_c.

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
    (HMAIN: prog_main prog = Some main)
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
  Inductive valid_read_asm: Genv.symtbl -> (regset * Mem.mem) -> Int64.int -> list byte -> (regset * Mem.mem) -> Prop :=
  | valid_read_asm_intro se (rs: regset) m n bytes rs' m' b ofs
      (HVF: Genv.find_funct (Genv.globalenv se prog) rs#PC = Some read_asm)
      (HDI: rs#RDI = Vint (Int.repr 0))
      (HSI: rs#RSI = Vptr b ofs)
      (HDX: rs#RDX = Vlong n)
      (HN: (Z.of_nat (length bytes) <= Int64.unsigned n)%Z)
      (HM: Mem.storebytes m b (Ptrofs.unsigned ofs) (map Byte bytes) = Some m')
      (HAX: rs'#(IR RAX) = Vint (Int.repr (Z.of_nat (length bytes)))) :
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
      (HDX: rs#RDX = Vlong (Int64.repr n))
      (HM: Mem.loadbytes m b (Ptrofs.unsigned ofs) n = Some (map Byte bytes))
      (HAX: rs'#(IR RAX) = Vint r) :
    valid_write_asm se (rs, m) bytes r (rs', m).
  Definition write_asm : S ->> li_asm :=
    sup se, sup q, sup bytes, sup n, sup r, sup (_: valid_write_asm se q bytes n r), down (write_asm_play se q bytes n r).
  Definition runtime_asm : S ->> li_asm := join read_asm write_asm.
  Definition load_asm_prog : S ->> P :=
    entry_asm ⊙ (lts_strat (Asm.semantics prog)) ⊙ runtime_asm.
  Definition load_asm_sem (L: Smallstep.semantics li_asm li_asm) : S ->> P :=
    entry_asm ⊙ (lts_strat L) ⊙ runtime_asm.

End ASM_LOADER.

Section LOADER_CORRECT.
  Import Clight Ctypes.
  Transparent Archi.ptr64.

  Context p tp (Hp: Compiler.transf_clight_program p = Errors.OK tp).
  Context
    (Hromatch: forall se m, init_mem se (AST.erase_program p) = Some m ->
        ValueAnalysis.romatch_all se (VAInject.bc_of_symtbl se) m).

  Lemma Hsk: erase_program p = erase_program tp.
  Proof.
    eapply match_prog_skel; eauto. apply Compiler.transf_clight_program_match. eauto.
  Qed.

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
          * eapply Hromatch. eauto.
          * constructor. eapply initmem_inject; eauto.
      - cbn. repeat apply conj; eauto. constructor. eauto.
        constructor; cbn; erewrite init_mem_nextblock; eauto; try easy.
        apply match_stbls_flat_inj.
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
        * eapply Hromatch. eauto.
        * constructor. eapply initmem_inject; eauto.
    }
    2: {
      cbn. repeat apply conj; eauto. constructor. eauto.
      constructor; cbn; erewrite init_mem_nextblock; eauto; try easy.
      apply match_stbls_flat_inj.
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

  Import Compiler CKLR CallconvAlgebra VAInject Inject.
  Definition inj_state := (block * ptrofs * Mem.mem)%type.
  Inductive match_inj_state:
    ccworld (cc_cklrs^{*}) -> world vainj -> cc_ca_world -> inj_state -> inj_state -> Prop := 
  | match_inj_state_intro wn wi b1 ofs1 m1 b2 ofs2 m2 caw se 
      (HM: mm_ca wn (se, wi) (caw_m caw) m1 m2) (HP: mp_ca wn wi b1 ofs1 b2 ofs2):
      match_inj_state wn (se, wi) caw (b1, ofs1, m1) (b2, ofs2, m2).
  Instance runtime_asm_determ:
    Deterministic (runtime_asm tp).
  Admitted.

  Lemma runtime_correct: rsq vid CAsm.cc_compcert (runtime_c p) (runtime_asm tp).
  Proof.
    setoid_rewrite cc_conv_expand. apply rsq_sup. apply runtime_asm_determ.
    { constructor. apply None. }
    intros [w|].
    2: { intros s ([|] & Hs).
         - destruct Hs as (se & q & n & bs & r & H & Hs). rewrite Hs. clear Hs.
           unfold read_c_play. apply rsp_oq. {
             exists true. cbn. inv H. eexists se, (((((Pregmap.init Vundef)#PC <- vf)#RDI <- (Vint (Int.repr 0))#RSI <- (Vptr b ofs))#RDX <- (Vlong n)), m), n, bs, ((Pregmap.init Vundef)#RAX <- (Vint (Int.repr (Z.of_nat (Datatypes.length bs)))), m').
             eexists. 2: constructor.
             econstructor; cbn; eauto.
             eapply match_prog_read. 4: eauto.
             apply Compiler.transf_clight_program_match. eauto.
             apply Genv.match_stbls_id.
             apply val_inject_refl. }
           intros q2 Hq2. xinv Hq2.
         - destruct Hs as (se & q & bs & n & r & H & Hs). rewrite Hs. clear Hs.
           unfold write_c_play. apply rsp_oq. {
             exists false. cbn. inv H. eexists se, (((((Pregmap.init Vundef)#PC <- vf)#RDI <- (Vint (Int.repr 1))#RSI <- (Vptr b ofs))#RDX <- (Vlong (Int64.repr len))), m), bs, n, ((Pregmap.init Vundef)#RAX <- (Vint n), m).
             eexists. 2: constructor.
             econstructor; cbn; eauto.
             eapply match_prog_write. 4: eauto.
             apply Compiler.transf_clight_program_match. eauto.
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
        exists true. cbn. eexists se, (((((Pregmap.init Vundef)#PC <- vf)#RDI <- (Vint (Int.repr 0))#RSI <- (Vptr b ofs))#RDX <- (Vlong n)), m), n, bs, ((Pregmap.init Vundef)#RAX <- (Vint (Int.repr (Z.of_nat (Datatypes.length bs)))), m').
        eexists. 2: constructor.
        econstructor; cbn; eauto.
        eapply match_prog_read. 4: eauto.
        apply Compiler.transf_clight_program_match. eauto.
        apply Genv.match_stbls_id.
        apply val_inject_refl.
      }
      intros q Hq. cbn in Hq. dependent destruction Hq.
      eapply rsp_pq with (m2 := inl (F_read n)). reflexivity.
      eapply rsp_oa. {
        exists true. cbn. 
      set (w1 := (nw_of_world w)). set (w2 := (injw_of_world w)). set (w3 := (caw_of_world w)).
      unfold CAsm.cc_compcert in *. cbn in w, HM |- *.
      eprod_crush. destruct s7.
      match goal with
      | [ H: Invariant.rel_inv _ _ _ |- _ ] => inv H; eprod_crush; subst
      end.
      (* cklrs *)
      eapply (cklrs_match_query_inv (existT _ x2 c0)) in H as
          (mx & bx & ofsx & vfx & Hqx & Hmx & Hpx & Hvx). subst x0. cbn in *.
      (* lessdef *)
      inv H1. repeat inv_lessdef.
      (* cc_c_asm: need to show args_removed changes nothing *)
      inv H2. inv HRM. inv H.
      2: { match goal with
          | [ H: size_arguments _ > 0 |- _ ] => rewrite rw_sig_size_arguments in H  end.
           lia. apply Hwin. }
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
      exploit ca_storebytes; eauto. intros (mx1 & Hs & Hm).
      inv Hm.

        eexists _, _, _, _, ((Pregmap.init Vundef)#RAX <- (Vint (Int.repr (Z.of_nat (Datatypes.length bs)))), _).
        eexists.
        2: { unfold read_asm_play. repeat constructor. }
        econstructor; eauto.
      + cbn in HVF. cbn in HSE.  eprod_crush. inv H8.
        eapply ca_find_funct_read; eauto.
        apply Compiler.transf_clight_program_match. eauto.
        apply H7. apply HVF.
      + specialize (Hreg RDI). rewrite <- H0 in Hreg. inv Hreg; eauto.
      + specialize (Hreg RDX). rewrite <- H3 in Hreg. inv Hreg; eauto.
      }
      intros r2 H2. cbn in H2. apply not_and_or in H2 as [H2|H2]. easy.
      assert (bs = r2) as <-.
      { apply NNPP. intros Hx. apply H2. intros Hy. apply Hx.
        apply JMeq_eq; eauto. } clear H2.

      set (w1 := (nw_of_world w)). set (w2 := (injw_of_world w)). set (w3 := (caw_of_world w)).
      unfold CAsm.cc_compcert in *. cbn in w, HM |- *.
      eprod_crush. destruct s7.
      match goal with
      | [ H: Invariant.rel_inv _ _ _ |- _ ] => inv H; eprod_crush; subst
      end.
      (* cklrs *)
      eapply (cklrs_match_query_inv (existT _ x2 c0)) in H as
          (mx & bx & ofsx & vfx & Hqx & Hmx & Hpx & Hvx). subst x0. cbn in *.
      (* lessdef *)
      inv H1. repeat inv_lessdef.
      (* cc_c_asm: need to show args_removed changes nothing *)
      inv H2. inv HRM. inv H.
      2: { match goal with
          | [ H: size_arguments _ > 0 |- _ ] => rewrite rw_sig_size_arguments in H  end.
           lia. apply Hwin. }
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
      exploit ca_storebytes; eauto. intros (mx1 & Hs & Hm).
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
        { eapply cklrs_match_reply_intro; eauto. }
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
            apply Hwin.
          - rewrite rw_sig_size_arguments.
            intros * HX. inv HX. lia.
            apply Hwin. }
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
        apply Compiler.transf_clight_program_match. eauto.
        apply m1. apply HVF.
      + specialize (Hreg RDI). rewrite <- H0 in Hreg. inv Hreg; eauto.
      + specialize (Hreg RDX). rewrite <- H3 in Hreg. inv Hreg; eauto. }
      cbn. reflexivity.
    - destruct Hs as (se & q & bs & n & r & H & Hs). rewrite Hs. clear Hs.
      inv H. unfold write_c_play. apply rsp_oq. {
        exists false. cbn. eexists se, (((((Pregmap.init Vundef)#PC <- vf)#RDI <- (Vint (Int.repr 1))#RSI <- (Vptr b ofs))#RDX <- (Vlong (Int64.repr len))), m), bs, n, ((Pregmap.init Vundef)#RAX <- (Vint n), m).
        eexists. 2: constructor.
        econstructor; cbn; eauto.
        eapply match_prog_write. 4: eauto.
        apply Compiler.transf_clight_program_match. eauto.
        apply Genv.match_stbls_id.
        apply val_inject_refl.
      }
      intros q Hq. cbn in Hq. dependent destruction Hq.
      eapply rsp_pq with (m2 := inr (F_write bs)). reflexivity.
      eapply rsp_oa. {
        exists false. cbn.

      set (w1 := (nw_of_world w)). set (w2 := (injw_of_world w)). set (w3 := (caw_of_world w)).
      destruct m2 as [rs mt].
      unfold CAsm.cc_compcert in *. cbn in w, HM |- *.
      eprod_crush. destruct s7.
      match goal with
      | [ H: Invariant.rel_inv _ _ _ |- _ ] => inv H; eprod_crush; subst
      end.
      eapply (cklrs_match_query_inv (existT _ x2 c0)) in H as
          (mx & bx & ofsx & vfx & Hqx & Hmx & Hpx & Hvx). subst x0. cbn in *.
      (* lessdef *)
      inv H1. repeat inv_lessdef.
      (* cc_c_asm: need to show args_removed changes nothing *)
      inv H2. inv HRM. inv H.
      2: { match goal with
        | [ H: size_arguments _ > 0 |- _ ] =>
            rewrite rw_sig_size_arguments in H; try lia  end. apply Hwin. }
      (* cc_asm vainj *)
      destruct H3 as (Hreg & Hpc & Him).
      (* arguments *)
      match goal with
      | [ H: cons _ _ = _ |- _ ] => cbn in H; rewrite Hwin in H; cbn in H; inv H
      end.
      assert (exists b' ofs', rs#RSI = Vptr b' ofs' /\ Val.inject i (Vptr bx ofsx) (Vptr b' ofs')) as (b' & ofs' & Hofs & Hb').
      { specialize (Hreg RSI). rewrite <- H2 in Hreg. inv Hreg.
        eexists _, _. split; eauto. }
      assert (HCA: mm_ca w1 w2 (caw_m w3) m mt).
      { inv Him. econstructor; eauto. reflexivity.
        apply Mem.unchanged_on_refl. }

        eexists _, _, _, _, ((Pregmap.init Vundef)#RAX <- (Vint n), _).
        exists. 2: { repeat constructor. }
         econstructor; cbn; eauto.
        + cbn in HVF. cbn in HSE.  eprod_crush. inv H8.
          eapply ca_find_funct_write; eauto.
          apply Compiler.transf_clight_program_match. eauto.
          apply H7. apply HVF.
        + specialize (Hreg RDI). rewrite <- H0 in Hreg. inv Hreg; eauto.
        + specialize (Hreg RDX). rewrite <- H3 in Hreg. inv Hreg; eauto.
        + inv Him. eapply ca_loadbytes; eauto.
          econstructor; eauto. inv Hb'. constructor; eauto.
      }
      intros r2 H2. cbn in H2. apply not_and_or in H2 as [H2|H2]. easy.
      assert (n = r2) as <-.
      { apply NNPP. intros Hx. apply H2. intros Hy. apply Hx.
        apply JMeq_eq; eauto. } clear H2.
      set (w1 := (nw_of_world w)). set (w2 := (injw_of_world w)). set (w3 := (caw_of_world w)).
      destruct m2 as [rs mt].
      unfold CAsm.cc_compcert in *. cbn in w, HM |- *.
      eprod_crush. destruct s7.
      match goal with
      | [ H: Invariant.rel_inv _ _ _ |- _ ] => inv H; eprod_crush; subst
      end.
      eapply (cklrs_match_query_inv (existT _ x2 c0)) in H as
          (mx & bx & ofsx & vfx & Hqx & Hmx & Hpx & Hvx). subst x0. cbn in *.
      (* lessdef *)
      inv H1. repeat inv_lessdef.
      (* cc_c_asm: need to show args_removed changes nothing *)
      inv H2. inv HRM. inv H.
      2: { match goal with
        | [ H: size_arguments _ > 0 |- _ ] =>
            rewrite rw_sig_size_arguments in H; try lia  end. apply Hwin. }
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
        { eapply cklrs_match_reply_intro; eauto. }
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
            intros * HX. inv HX. lia. apply Hwin. }
        { exists (s0, i). split. reflexivity. split; eauto.
          intros. cbn in Hreg. destruct r0; cbn; eauto. destruct i0; cbn; eauto.
          subst v. eauto. }
      }

      assert (HCA: mm_ca w1 w2 (caw_m w3) m mt).
      { inv Him. econstructor; eauto. reflexivity.
        apply Mem.unchanged_on_refl. }

      apply rsp_ready. exists false.
      eexists _, (rs, mt), _, _, ((rs#RAX <- v)#PC <- (rs#RA), mt).
      eexists.
      { econstructor; eauto.
        + cbn in HVF. cbn in HSE.  eprod_crush. inv r0.
          eapply ca_find_funct_write; eauto.
          apply Compiler.transf_clight_program_match. eauto.
          apply m0. apply HVF.
        + specialize (Hreg RDI). rewrite <- H0 in Hreg. inv Hreg; eauto.
        + specialize (Hreg RDX). rewrite <- H3 in Hreg. inv Hreg; eauto.
        + inv Him. eapply ca_loadbytes; eauto.
          econstructor; eauto. inv Hb'. constructor; eauto.
        + cbn. reflexivity. }
      cbn. reflexivity.
  Qed.

  Lemma load_sem_correct L_c L_asm:
    determinate L_asm ->
    forward_simulation CAsm.cc_compcert CAsm.cc_compcert L_c L_asm ->
    load_c_sem p L_c [= load_asm_sem tp L_asm.
  Proof.
    intros HD HL. eapply rsq_id_conv with (p := rs_ready).
    eapply rsq_comp_when. constructor. apply entry_correct.
    eapply rsq_comp_when. constructor. 2: apply runtime_correct.
    apply fsim_rsq; eauto.
  Qed.

  (* Lemma load_prog_correct : *)
  (*   load_c_prog p [= load_asm_prog tp. *)
  (* Admitted. *)
End LOADER_CORRECT.

Require process.Secret.
Require Import Clight Ctypes.

Section ROT13.
  Import Secret.
  Section WITH_SE.
    Import Events.
    Context (se: Genv.symtbl).
    Variant rot13_state :=
      | init (bytes: list byte)
      (* The first i bytes have been decoded. These intermediate steps correspond
       to internal steps in the loop of rot13.c, so that we don't have to do
       induction proof on the Clight loops *)
      | wip (bytes: list byte) (i: Z)
      | done (bytes: list byte).

    Definition mem_state := (mem * block * Z)%type.

    Inductive rot13_initial_state: query li_c -> (rot13_state * mem_state)%type -> Prop :=
    | rot13_initial_state_intro m sg b b_buf len bytes
        (HB1: Genv.find_symbol se secret_rot13_id = Some b)
        (HL: Mem.loadbytes m b_buf 0 len = Some (map Byte bytes))
        (HSG: sg = rot13_sig):
      rot13_initial_state
        (cq (Vptr b Ptrofs.zero) sg [ Vptr b_buf Ptrofs.zero; Vlong (Int64.repr len) ] m) (init bytes, (m, b_buf, len)).

    Inductive rot13_final_state: (rot13_state * mem_state)%type -> reply li_c -> Prop :=
    | rot13_final_state_intro m m' b_buf len bytes
        (HS: Mem.storebytes m b_buf 0 (map Byte bytes) = Some m'):
      rot13_final_state (done bytes, (m, b_buf, len)) (cr Vundef m').

    Open Scope Z_scope.

    Inductive rot13_step: (rot13_state * mem_state)%type -> trace -> (rot13_state * mem_state) -> Prop :=
    | rot13_step1 bytes m: rot13_step (init bytes, m) E0 (wip bytes 0, m)
    | rot13_stepi bytes bytes' i m
        (HB: forall b, nth bytes (Z.to_nat i) b -> Byte.unsigned b >= 97)
        (HI: 0 <= i < Z.of_nat (length bytes))
        (HU: nth_update bytes (Z.to_nat i) rot13_byte bytes'):
      rot13_step (wip bytes i, m) E0 (wip bytes' (i + 1), m)
    | rot13_stepn bytes i m
        (HN: i = Z.of_nat (length bytes)):
      rot13_step (wip bytes i, m) E0 (done bytes, m).

  End WITH_SE.

  Definition rot13_c : Clight.program. Admitted.
  Definition L_rot13 : Smallstep.semantics li_c li_c :=
    {|
      activate se :=
        {|
          Smallstep.step _ := rot13_step;
          Smallstep.initial_state := rot13_initial_state se;
          Smallstep.at_external := fun _ _ => False;
          Smallstep.after_external := fun _ _ _ => False;
          Smallstep.final_state := rot13_final_state;
          Smallstep.globalenv := tt;
        |};
      skel := AST.erase_program rot13_c;
      footprint := AST.footprint_of_program rot13_c;
    |}.
  Lemma ϕ_rot13: forward_simulation 1%cc 1%cc L_rot13 (Clight.semantics2 rot13_c).
  Admitted.

End ROT13.

Definition secret_c_main : function. Admitted.
Definition secret_c_rot13 : function. Admitted.

Definition secret_c_main_id: positive := 1.
Definition secret_c_rot13_id: positive := 2.
Definition secret_c_write_id: positive := 3.
Definition secret_c_msg_id: positive := 4.

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

Program Definition composite_secret_program: Clight.program :=
  {|
    prog_defs := [
      (secret_c_main_id, Gfun (Internal secret_c_main));
      (secret_c_rot13_id, Gfun (Internal secret_c_rot13));
      (secret_c_write_id, Gfun write);
      (secret_c_msg_id, Gvar msg_globvar)];
    prog_public := nil;
    prog_main := Some secret_c_main_id;
    prog_types := [];
    prog_comp_env := (PTree.empty _);
  |}.
Next Obligation. reflexivity. Qed.

Section SECRET.
  Import Clight Ctypes.
  Hypothesis (Hwin: Archi.win64 = false).
  Definition secret_sk := AST.erase_program composite_secret_program.

  Lemma secret_init_mem se:
    Genv.valid_for secret_sk se ->
    exists m, init_mem se secret_sk = Some m /\
           (forall b, Genv.find_symbol se secret_c_msg_id = Some b ->
                 Mem.loadbytes m b 0 5 = Some (map Byte hello_bytes)).
  Proof.
    intros Hvalid.
    edestruct init_mem_exists with (p := secret_sk) as [m Hm]; eauto.
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
      eapply (@Genv.store_init_data_list_loadbytes se b msg_il) in H6.
      + erewrite Mem.loadbytes_drop; eauto.
        right. right. right. constructor.
      + eapply Genv.store_zeros_loadbytes. eauto.
  Qed.

  Lemma main_block se:
    Genv.valid_for secret_sk se ->
    exists b, Genv.find_symbol (globalenv se composite_secret_program) secret_c_main_id = Some b /\
           Genv.find_funct (globalenv se composite_secret_program) (Vptr b Ptrofs.zero) = Some (Internal secret_c_main).
  Proof.
    intros Hse. exploit @Genv.find_def_symbol; eauto.
    intros [H _]. edestruct H as (b & Hb1 & Hb2); eauto.
    2: {exists b. split; eauto. eapply genv_funct_symbol; eauto.}
    reflexivity.
  Qed.
  Lemma rot13_block se:
    Genv.valid_for secret_sk se ->
    exists b, Genv.find_symbol (globalenv se composite_secret_program) secret_c_rot13_id = Some b /\
           Genv.find_funct (globalenv se composite_secret_program) (Vptr b Ptrofs.zero) = Some (Internal secret_c_rot13).
  Proof.
    intros Hse. exploit @Genv.find_def_symbol; eauto.
    intros [H _]. edestruct H as (b & Hb1 & Hb2); eauto.
    2: {exists b. split; eauto. eapply genv_funct_symbol; eauto.}
    reflexivity.
  Qed.
  Lemma write_block se:
    Genv.valid_for secret_sk se ->
    exists b, Genv.find_symbol (globalenv se composite_secret_program) secret_c_write_id = Some b /\
           Genv.find_funct (globalenv se composite_secret_program) (Vptr b Ptrofs.zero) = Some write.
  Proof.
    intros Hse. exploit @Genv.find_def_symbol; eauto.
    intros [H _]. edestruct H as (b & Hb1 & Hb2); eauto.
    2: {exists b. split; eauto. eapply genv_funct_symbol; eauto.}
    reflexivity.
  Qed.
  Lemma msg_block se:
    Genv.valid_for secret_sk se ->
    exists b, Genv.find_symbol (globalenv se composite_secret_program) secret_c_msg_id = Some b.
  Proof.
    intros Hse. exploit @Genv.find_def_symbol; eauto.
    intros [H _]. edestruct H as (b & Hb1 & Hb2); eauto.
    reflexivity.
  Qed.

  Definition L_secret := Secret.secret_spec.
  Definition L_compose := fun (i: bool) => if i then L_secret else L_rot13.
  Lemma ϕ_secret : Γ_secret secret_sk [= load_c_sem composite_secret_program (SmallstepLinking.semantics L_compose secret_sk).
  Proof.
    intros p Hp. cbn in Hp. destruct Hp as ((se & Hse) & Hp).
    eapply Downset.closed in Hp; eauto. clear Hp.
    edestruct secret_init_mem as (m & Hm1 & Hm2). apply Hse.
    edestruct main_block as (b & Hb1 & Hb2). apply Hse.
    edestruct write_block as (b1 & Hb3 & Hb4). apply Hse.
    edestruct msg_block as (b2 & Hb5). apply Hse.
    assert (Hflag: Mem.alloc_flag m = true).
    { eapply init_mem_alloc_flag; eauto. }
    assert (exists m3, Mem.storebytes m b2 0 (map Byte uryyb_bytes) = Some m3) as (m3 & Hm3).
    { admit. }
    eexists _, _. repeat apply conj.
    3: { unfold entry_c_play. unfold Γ_secret_play.
         apply comp_oq. apply comp_lq. apply comp_rq. apply comp_oa.
         apply comp_ra. apply comp_la. instantiate (1 := pnil_ready). apply comp_ready. }
    { cbn. eexists se, _, _, Int.zero. eexists.
      econstructor; eauto. admit. admit.
      unfold entry_c_play. reflexivity. }
    specialize (Hm2 _ Hb5).
    eexists _, _. repeat apply conj.
    3: { apply comp_oq. apply comp_lq. apply comp_rq. apply comp_oa.
         apply comp_ra. apply comp_la. instantiate (1 := pnil_ready). apply comp_ready. }
    2: { exists false. cbn. eexists se, _, uryyb_bytes, _, _. exists.
         econstructor; eauto.
         replace 0%Z with (Ptrofs.unsigned Ptrofs.zero) in Hm3 by reflexivity.
         eapply Mem.loadbytes_storebytes_same; eauto.
         unfold write_c_play. reflexivity. }
    cbn. eapply closure_has_cons.
    2: apply closure_has_nil.
    2: apply seq_comp_has_nil2; eauto.
    cbn. econstructor; eauto.
    { (* initial step *)
      econstructor.
      - instantiate (1 := true).
        cbn. unfold valid_query. split; cbn; try congruence.
        admit.
      - cbn. econstructor; eauto. admit.  }
    econstructor 4.
    { apply star_one. econstructor 1. econstructor 1; eauto. }
    econstructor 4.
    { apply star_one. econstructor 2.
      - constructor; eauto. admit.
      - unfold valid_query. split; cbn; try congruence.
        admit.
      - instantiate (3 := false). constructor; eauto. }
    econstructor 4.
    { apply star_one. econstructor 1. econstructor 1. }
    (* loop 5 times *)
    Ltac solve_nth_range :=
      intros;
      repeat match goal with
        | [ H: nth _ _ _ |- _  ] => inv H
        end; rewrite Byte.unsigned_repr by (cbn; lia); lia.
    econstructor 4.
    { apply star_one. econstructor 1. econstructor 2;
        [ solve_nth_range | cbn; lia | repeat constructor ]. }
    econstructor 4.
    { apply star_one. econstructor 1. econstructor 2;
        [ solve_nth_range | cbn; lia | repeat constructor ]. }
    econstructor 4.
    { apply star_one. econstructor 1. econstructor 2;
        [ solve_nth_range | cbn; lia | repeat constructor ]. }
    econstructor 4.
    { apply star_one. econstructor 1. econstructor 2;
        [ solve_nth_range | cbn; lia | repeat constructor ]. }
    econstructor 4.
    { apply star_one. econstructor 1. econstructor 2;
        [ solve_nth_range | cbn; lia | repeat constructor ]. }
    econstructor 4.
    { apply star_one. econstructor 1. econstructor 3. reflexivity. }
    econstructor 4.
    (* rot13 returns to secret *)
    { apply star_one. econstructor 3.
      - constructor. eauto.
      - econstructor. admit. }
    econstructor 4.
    { apply star_one. econstructor 1. econstructor 2. }
    econstructor 2.
    { econstructor.
      - econstructor; eauto. admit. admit. admit.
      - intros [|] Hj.
        + unfold valid_query in Hj. cbn in Hj. admit.
        + admit. }
    { repeat econstructor. }
    econstructor 4.
    { apply star_one. econstructor 1. econstructor 3. }
    econstructor 3.
    { econstructor. econstructor. }
    Unshelve. admit. admit.
  Admitted.

  Context rot13_asm (Hrot13: Compiler.transf_clight_program rot13_c = Errors.OK rot13_asm).
  Context linked_secret_asm (HL: Linking.link rot13_asm Secret.secret_asm_program = Some linked_secret_asm).
  Lemma π_secret_cc : forward_simulation cc_compcert cc_compcert Σ_secret (Asm.semantics linked_secret_asm).
  Admitted.

  Lemma ϕ_secret_cc : Γ_secret [= load_asm_prog linked_secret_asm.
  Admitted.

End SECRET.
