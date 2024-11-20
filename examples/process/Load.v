Require Import Coqlib Integers.

Require Import Events Smallstep Globalenvs Values Memory.
Require LanguageInterface.
Import -(notations) LanguageInterface.
Require Import AST Ctypes Clight.

Require Import List Maps.
Import ListNotations.
Require Import Conventions Mach Asm.

Require Import InitMem.
Require Import CAsm.

Require Import Classical.

Axiom (Hwin: Archi.win64 = false).

Ltac subst_dep :=
  subst;
  lazymatch goal with
  | H: existT ?P ?x _ = existT ?P ?x _ |- _ =>
      apply inj_pair2 in H; subst_dep
  | _ => idtac
  end.

Ltac eprod_crush :=
  repeat
    (match goal with
     | [ H: ?a * ?b |- _ ] => destruct H;cbn [fst snd] in *; subst
     | [ H: (?a, ?b) = (?c, ?d) |- _ ] => inv H
     | [ H: ?x /\ ?y |- _] => destruct H
     | [ H: (exists _, _) |- _] => destruct H
     | [ H: unit |- _] => destruct H
     end).

Ltac inv_inj:=
  match goal with
  | [ H: Val.inject_list _ _ _ |- _ ] => inv H
  | [ H: Val.inject _ (Vint _) _ |- _ ] => inv H
  | [ H: Val.inject _ (Vlong _) _ |- _ ] => inv H
  | [ H: Val.inject _ (Vptr _ _) _ |- _ ] => inv H
  end.

Ltac inv_lessdef:=
  match goal with
  | [ H: Val.lessdef_list _ _ |- _ ] => inv H
  | [ H: Val.lessdef _ _ |- _ ] => inv H
  end.

Section WRITE_EMPTY.

  Import CallconvAlgebra CallConv CKLR.
  Import Inject InjectFootprint Extends VAInject VAExtends.
  Import ValueDomain ValueAnalysis VAInject.
  Transparent Mem.load Mem.loadbytes Mem.storebytes.

  Program Definition mem_write_empty (m: Mem.mem) b :=
    (Mem.mkmem (PMap.set b (m.(Mem.mem_contents)!!b) m.(Mem.mem_contents))
       m.(Mem.mem_access) m.(Mem.nextblock) m.(Mem.alloc_flag) _ _ _).
  Next Obligation. apply Mem.access_max. Qed.
  Next Obligation. eauto using Mem.nextblock_noaccess. Qed.
  Next Obligation.
    destruct (peq b b0).
    - subst. rewrite PMap.gss. apply Mem.contents_default.
    - rewrite PMap.gso; eauto. apply Mem.contents_default.
  Qed.

  Definition cklr_mem_write_empty_match (c: cklr) :=
    forall w m1 m2 b1 b2, match_mem c w m1 m2 ->
    exists w', w ~> w' /\ match_mem c w' (mem_write_empty m1 b1) (mem_write_empty m2 b2).

  Lemma storebytes_empty m b ofs:
    Mem.storebytes m b ofs nil = Some (mem_write_empty m b).
  Proof.
    unfold Mem.storebytes; cbn. destruct Mem.range_perm_dec.
    - f_equal. destruct m. cbn. apply Mem.mkmem_ext; eauto.
    - exfalso. apply n. intros p Hp. lia.
  Qed.

  Lemma cklr_storebytes_empty (c: cklr) (w: world c) m1 m2 m3 b1 b2 ofs1 ofs2:
    cklr_mem_write_empty_match c ->
    Mem.storebytes m1 b1 (Ptrofs.unsigned ofs1) nil = Some m3 ->
    match_mem c w m1 m2 ->
    exists wx m4, w ~> wx
             /\ Mem.storebytes m2 b2 (Ptrofs.unsigned ofs2) nil = Some m4
             /\ match_mem c wx m3 m4.
  Proof.
    intros HC HS HM.
    specialize (HC _ _ _ b1 b2 HM) as (w' & Hw' & Hc).
    exists w', (mem_write_empty m2 b2). split; eauto.
    split. apply storebytes_empty.
    rewrite storebytes_empty in HS. inv HS. apply Hc.
  Qed.

  Lemma mem_write_empty_nextblock m b:
    Mem.nextblock (mem_write_empty m b) = Mem.nextblock m.
  Proof. unfold mem_write_empty. destruct m. reflexivity. Qed.

  Lemma mem_write_empty_mem_inj f m1 m2 b1 b2:
    Mem.mem_inj f m1 m2 ->
    Mem.mem_inj f (mem_write_empty m1 b1) (mem_write_empty m2 b2).
  Proof.
    intros H. inv H. econstructor; cbn; eauto.
    intros. rewrite !PMap.gsident. eauto.
  Qed.

  Lemma mem_write_empty_inject f m1 m2 b1 b2:
    Mem.inject f m1 m2 ->
    Mem.inject f (mem_write_empty m1 b1) (mem_write_empty m2 b2).
  Proof.
    intros H. inv H.
    econstructor; cbn; eauto using mem_write_empty_mem_inj.
  Qed.

  Lemma inj_mem_write_empty_match: cklr_mem_write_empty_match inj.
  Proof.
    unfold cklr_mem_write_empty_match.
    intros. inv H.
    eexists. split. reflexivity.
    rewrite <- (mem_write_empty_nextblock m1 b1).
    rewrite <- (mem_write_empty_nextblock m2 b2).
    econstructor. apply mem_write_empty_inject. eauto.
  Qed.

  Lemma injp_mem_write_empty_match: cklr_mem_write_empty_match injp.
  Proof.
    unfold cklr_mem_write_empty_match.
    intros. inv H.
    exploit mem_write_empty_inject; eauto. intros HX.
    eexists (injpw f (mem_write_empty m1 b1) (mem_write_empty m2 b2) HX).
    split.
    - constructor; eauto; try (red; easy).
      + split; cbn; try easy. intros. rewrite PMap.gsident. easy.
      + split; cbn; try easy. intros. rewrite PMap.gsident. easy.
      + red. intros. congruence.
    - constructor.
  Qed.

  Lemma ext_mem_write_empty_match: cklr_mem_write_empty_match ext.
  Proof.
    unfold cklr_mem_write_empty_match.
    intros. inv H. exists w. split. reflexivity.
    constructor; eauto using mem_write_empty_mem_inj.
  Qed.

  Lemma mem_write_empty_extends m1 m2 b1 b2:
    Mem.extends m1 m2 ->
    Mem.extends (mem_write_empty m1 b1) (mem_write_empty m2 b2).
  Proof.
    intros H. inv H.
    constructor; cbn; eauto using mem_write_empty_mem_inj.
  Qed.

  Lemma mem_write_empty_load ch m b b0 ofs:
    Mem.load ch (mem_write_empty m b) b0 ofs = Mem.load ch m b0 ofs.
  Proof.
    Local Transparent Mem.load.
    unfold Mem.load. cbn. rewrite PMap.gsident. reflexivity.
  Qed.

  Lemma mem_write_empty_loadbytes m b b0 ofs len:
    Mem.loadbytes (mem_write_empty m b) b0 ofs len = Mem.loadbytes m b0 ofs len.
  Proof.
    unfold Mem.loadbytes. cbn. rewrite PMap.gsident. reflexivity.
  Qed.

  Lemma mem_write_empty_romatch_all se bc m b:
    romatch_all se bc m ->
    romatch_all se bc (mem_write_empty m b).
  Proof.
    intros H. red. intros. specialize (H cu H0).
    red. intros. specialize (H _ _ _ H1 H2). eprod_crush.
    repeat apply conj; eauto.
    - intros. eapply H3. erewrite <- mem_write_empty_load; eauto.
    - intros. eapply H3. erewrite <- mem_write_empty_loadbytes; eauto.
    - intros. eapply H3. erewrite <- mem_write_empty_load; eauto.
  Qed.

  Lemma mem_write_empty_smatch bc m b b0 am:
    smatch bc m b0 am ->
    smatch bc (mem_write_empty m b) b0 am.
  Proof.
    intros H. inv H. constructor.
    - intros. eapply H0. erewrite <- mem_write_empty_load; eauto.
    - intros. eapply H1. erewrite <- mem_write_empty_loadbytes; eauto.
  Qed.

  Lemma mem_write_empty_bmatch bc m b b0 am:
    bmatch bc m b0 am ->
    bmatch bc (mem_write_empty m b) b0 am.
  Proof.
    intros H. inv H. constructor.
    - apply mem_write_empty_smatch. eauto.
    - intros. apply H1. erewrite <- mem_write_empty_load; eauto.
  Qed.

  Lemma mem_write_empty_mmatch bc m b am:
    mmatch bc m am ->
    mmatch bc (mem_write_empty m b) am.
  Proof.
    intros H. inv H.
    constructor; eauto; intros;
      eauto using mem_write_empty_bmatch, mem_write_empty_smatch.
  Qed.

  Lemma vaext_mem_write_empty_match: cklr_mem_write_empty_match vaext.
  Proof.
    unfold cklr_mem_write_empty_match.
    intros. inv H.
    assert (HX: vaext_wf se bc (mem_write_empty m1 b1)).
    { inv H1. constructor;
        eauto using mem_write_empty_romatch_all,
        mem_write_empty_mmatch. }
    exists (vaextw se bc (mem_write_empty m1 b1) HX). split.
    - constructor; cbn; eauto. reflexivity.
      intros. unfold Mem.loadbytes in H4 |- *.
      rewrite <- H4. cbn. rewrite PMap.gsident. reflexivity.
    - constructor. eauto using mem_write_empty_extends.
  Qed.

  Lemma vainj_mem_write_empty_match: cklr_mem_write_empty_match vainj.
  Proof.
    unfold cklr_mem_write_empty_match.
    intros. inv H. exists (se, w0). split. reflexivity.
    constructor; eauto.
    - apply mem_write_empty_romatch_all; eauto.
    - inv H2. rewrite <- (mem_write_empty_nextblock m1 b1).
      rewrite <- (mem_write_empty_nextblock m2 b2).
      econstructor. apply mem_write_empty_inject. eauto.
  Qed.

End WRITE_EMPTY.

Hint Resolve injp_mem_write_empty_match
  inj_mem_write_empty_match
  ext_mem_write_empty_match
  vainj_mem_write_empty_match
  vaext_mem_write_empty_match.


Import Ctypes.                  (* shadow Tnil and Tcons from RelationClasses *)

Notation tint := (Tint I32 Unsigned noattr).

Definition main_sig := signature_of_type Tnil tint cc_default.

Require Compiler.

Section INIT_C_ASM.

  Context p tp (Hp: Compiler.match_prog p tp).

  Hypothesis
    (Hromatch: forall se m,
        init_mem se (AST.erase_program p) = Some m ->
        ValueAnalysis.romatch_all se (VAInject.bc_of_symtbl se) m).

  Local Transparent Archi.ptr64.

  Lemma match_stbls_flat_inj se:
    Genv.match_stbls (Mem.flat_inj (Genv.genv_next se)) se se.
  Proof.
    split; eauto; unfold Mem.flat_inj; intros.
    - destruct plt; try easy. eexists. reflexivity.
    - intros. unfold Mem.flat_inj. exists b2. destruct plt; try easy.
    - destruct plt; try easy. inv H. reflexivity.
    - destruct plt; try easy. inv H. reflexivity.
    - destruct plt; try easy. inv H. reflexivity.
  Qed.

  Lemma match_prog_skel: erase_program p = erase_program tp.
  Proof.
    intros. edestruct Compiler.clight_semantic_preservation as [H1 ?]; eauto.
    destruct H1. destruct X. apply fsim_skel.
  Qed.

End INIT_C_ASM.

Variant sys_query :=
  | write_query: list byte -> sys_query
  | read_query: int64 -> sys_query.

Variant sys_reply :=
  | write_reply: int -> sys_reply
  | read_reply: list byte -> sys_reply.

Definition li_sys :=
  {|
    query := sys_query;
    reply := sys_reply;
    entry q := Vundef;
  |}.

Notation tvoid := (Tvoid).
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

Section FIND_FUNCT.
  Import Linking.
  Import AST.

  Definition link_prod {C1 C2} {LC1: Linker C1} {LC2: Linker C2}
    '(c1, c2) '(c3, c4): option (C1 * C2) :=
    match link c1 c3, link c2 c4 with
    | Some c1', Some c2' => Some (c1', c2')
    | _, _ => None
    end.

  Inductive linkorder_rel {C1 C2} {LC1: Linker C1} {LC2: Linker C2}:
    (C1 * C2) -> (C1 * C2) -> Prop :=
    linkorder_rel_intro c1 c2 c3 c4
      (H1: linkorder c1 c3) (H2: linkorder c2 c4):
      linkorder_rel (c1, c2) (c3, c4).

  Program Instance linker_prod {C1 C2} {LC1 : Linker C1} {LC2 : Linker C2} : Linker (C1 * C2) :=
    {|
      link := link_prod;
      linkorder := linkorder_rel;
    |}.
  Next Obligation. constructor; eapply linkorder_refl. Qed.
  Next Obligation.
    inv H. inv H0. constructor; eapply linkorder_trans; eauto.
  Qed.
  Next Obligation.
    inv H. destruct link eqn: Hx; inv H1.
    destruct (link c4 c2) eqn: Hy; inv H0.
    apply link_linkorder in Hx. apply link_linkorder in Hy.
    split; constructor; easy.
  Qed.

  Inductive compose_match_fundef {C1 C2 F1 F2 F3}
    (mf1: C1 -> F1 -> F2 -> Prop) (mf2: C2 -> F2 -> F3 -> Prop): C1 * C2 -> F1 -> F3 -> Prop :=
  | compose_match_fundef_intro c1 c2 f1 f2 f3
      (H1: mf1 c1 f1 f2) (H2: mf2 c2 f2 f3):
      compose_match_fundef mf1 mf2 (c1, c2) f1 f3.

  Import RelOperators.

  Lemma match_program_gen_compose
    {C1 C2 F1 F2 F3 V1 V2 V3}
    {c1: C1} {c2: C2} {mf1 mf2 mv1 mv2}
    {p1: AST.program F1 V1} {p2: AST.program F2 V2} {p3: AST.program F3 V3}
    {LC1: Linker C1} {LC2: Linker C2}:
    Linking.match_program_gen mf1 mv1 c1 p1 p2 ->
    Linking.match_program_gen mf2 mv2 c2 p2 p3 ->
    Linking.match_program_gen (compose_match_fundef mf1 mf2)
      (rel_compose mv1 mv2) (c1, c2) p1 p3.
  Proof.
    intros (A1 & A2 & A3) (B1 & B2 & B3).
    repeat apply conj; try congruence.
    clear - A1 B1. revert A1 B1.
    generalize (prog_defs p1) as l1.
    generalize (prog_defs p2) as l2.
    generalize (prog_defs p3) as l3.
    induction l3; intros * H1 H2; inv H1; inv H2. constructor.
    constructor.
    - inv H. inv H5. constructor. congruence.
      destruct a. destruct b1. destruct a1. cbn in *. subst.
      destruct g1.
      + inv H2. inv H3. econstructor; eauto. split; eauto.
        econstructor; eauto.
      + inv H2. inv H3. econstructor; eauto.
        inv H1. inv H2. constructor. eexists; split; eauto.
    - eapply IHl3; eauto.
  Defined.

  Lemma match_program_gen_compose_match_if
    {C1 F1 F2 V1 V2}
    {c1: C1} {mf1 mf2 mv1 mv2}
    {p1: AST.program F1 V1} {p2: AST.program F2 V2} {p3: AST.program F2 V2}
    {LC1: Linker C1} {LF2: Linker F2} {LV2: Linker V2} {P: unit -> bool}:
    Linking.match_program_gen mf1 mv1 c1 p1 p2 ->
    (if (P tt) then Linking.match_program mf2 mv2 p2 p3 else p2 = p3) ->
    Linking.match_program_gen
      (compose_match_fundef mf1 (if P tt then mf2 else fun _ => eq))
      (rel_compose mv1 (if P tt then mv2 else eq)) (c1, p2) p1 p3.
  Proof.
    intros A B.
    destruct (P tt).
    - unfold match_program in B.
      eapply match_program_gen_compose; eauto.
    - subst. destruct A as (A1 & A2 & A3).
      repeat apply conj; try congruence.
      clear - A1. revert A1.
      generalize (prog_defs p1) as l1.
      generalize (prog_defs p3) as l3.
      induction l3; intros * H1; inv H1. constructor.
      constructor.
      + destruct a1 as [ ? [|] ]; destruct a as [ ? [|] ]; inv H3; inv H0.
        * constructor; eauto. cbn.
          econstructor; eauto. split; eauto. apply linkorder_refl.
          econstructor; eauto.
        * constructor; eauto. cbn.
          constructor. inv H3. constructor.
          eexists; split; eauto.
      + eapply IHl3; eauto.
  Defined.

  Lemma if_commute {A B} (P: bool) (r1 r2: A -> B -> Prop) (a: A) (b: B):
    (if P then r1 else r2) a b = (if P then r1 a b else r2 a b).
  Proof. destruct P; reflexivity. Qed.

End FIND_FUNCT.

Obligation Tactic := idtac.

(* The weakest condition that can be used. We can't use se1 = se2 because we
   can't derive it from [match_senv cc_compcert w se1 se2] *)
Definition wp_match_senv (se1 se2: Genv.symtbl) :=
  (forall id, Genv.public_symbol se2 id = Genv.public_symbol se1 id) /\
    (forall sk, Genv.valid_for sk se1 <-> Genv.valid_for sk se2) /\
    (forall i, Genv.symbol_address se1 i Ptrofs.zero = Vundef <->
         Genv.symbol_address se2 i Ptrofs.zero = Vundef).

Program Definition cc_wp_id {li}: callconv li li :=
  {|
    ccworld := unit;
    match_query w q1 q2 := entry q1 = Vundef /\ entry q2 = Vundef /\ q1 = q2;
    match_senv w := wp_match_senv;
    match_reply w := eq;
  |}.
Next Obligation. intros. apply H. Qed.
Next Obligation. intros. apply H. Qed.
Next Obligation.
  intros. cbn in *. eprod_crush. subst.
  rewrite H0. apply H.
Qed.

Lemma cklr_find_symbol_none (c: CKLR.cklr) w se1 se2 i:
  match_senv (cc_c c) w se1 se2 ->
  Genv.find_symbol se1 i = None <->
  Genv.find_symbol se2 i = None.
Proof.
  split; intros.
  - apply CKLR.match_stbls_proj in H.
    destruct (Genv.find_symbol se2 i) eqn: Hi; try easy. exfalso.
    destruct (plt b (Genv.genv_next se2)).
    + eapply Genv.mge_img in p; eauto.
      destruct p as (b1 & Hb1).
      eapply Genv.mge_symb in Hb1; eauto.
      unfold Genv.find_symbol in Hi.
      rewrite <- Hb1 in Hi. unfold Genv.find_symbol in H0. congruence.
    + apply n. eapply Genv.genv_symb_range; eauto.
  - apply CKLR.match_stbls_proj in H.
    destruct (Genv.find_symbol se1 i) eqn: Hi; try easy. exfalso.
    destruct (plt b (Genv.genv_next se1)).
    + eapply Genv.mge_dom in p; eauto.
      destruct p as (b1 & Hb1).
      eapply Genv.mge_symb in Hb1; eauto.
      unfold Genv.find_symbol in Hi.
      rewrite Hb1 in Hi. unfold Genv.find_symbol in H0. congruence.
    + apply n. eapply Genv.genv_symb_range; eauto.
Qed.

Lemma cc_compcert_wp_match_senv' se1 se2:
  (exists w, match_senv cc_compcert w se1 se2) ->
       (forall i, Genv.symbol_address se1 i Ptrofs.zero = Vundef <->
               Genv.symbol_address se2 i Ptrofs.zero = Vundef).
Proof.
  intros [w Hw] i. cbn in *. eprod_crush.
  destruct s6. subst. inv H0.
  assert (HX: Genv.find_symbol se1 i = None <-> Genv.find_symbol se2 i = None).
  { assert (Genv.find_symbol se1 i = None <-> Genv.find_symbol s0 i = None).
    { clear - H. revert se1 s0 H. induction x.
      - intros; cbn in H. subst; eauto. reflexivity.
      - intros. cbn in *. eprod_crush. etransitivity.
        2: eapply IHx; eauto.
        repeat destruct s1; cbn in H.
        + eapply (cklr_find_symbol_none InjectFootprint.injp); eauto.
        + eapply (cklr_find_symbol_none Inject.inj); eauto.
        + eapply (cklr_find_symbol_none Extends.ext); eauto.
        + destruct p.
          eapply (cklr_find_symbol_none VAInject.vainj); eauto.
          instantiate (1 := (_, _)). split; apply H.
        + eapply (cklr_find_symbol_none VAExtends.vaext); eauto. }
    etransitivity. eauto.
    eapply (cklr_find_symbol_none Inject.inj); eauto. }
  unfold Genv.symbol_address.
  destruct (Genv.find_symbol se1 i) eqn: HA;
    destruct (Genv.find_symbol se2 i) eqn: HB; try easy.
  exfalso. assert (Some b = None). apply HX. easy. easy.
  exfalso. assert (Some b = None). apply HX. easy. easy.
  Unshelve. cbn. exact tt.
Qed.

Lemma cc_compcert_wp_match_senv se1 se2:
  (exists w, match_senv cc_compcert w se1 se2) ->
  wp_match_senv se1 se2.
Proof.
  intros [w Hw]. split; [| split].
  - eapply match_senv_public_preserved; eauto.
  - intros. eapply match_senv_valid_for; eauto.
  - eapply cc_compcert_wp_match_senv'; eauto.
Qed.

Next Obligation. intros. cbn in *. easy. Qed.

Section SYS_C_ASM.

  Local Transparent Archi.ptr64.
  Import CallconvAlgebra CallConv CKLR.
  Import Inject InjectFootprint Extends VAInject VAExtends.

  Import Compiler.

  Inductive acc_cklr : ccworld cc_cklrs -> ccworld cc_cklrs -> Prop :=
  | acc_cklr_vaext w w':
    w ~> w' -> acc_cklr (inr w) (inr w')
  | acc_cklr_vainj w w':
    w ~> w' -> acc_cklr (inl (inr w)) (inl (inr w'))
  | acc_cklr_ext w w':
    w ~> w' -> acc_cklr (inl (inl (inr w))) (inl (inl (inr w')))
  | acc_cklr_inj w w':
    w ~> w' -> acc_cklr (inl (inl (inl (inr w)))) (inl (inl (inl (inr w'))))
  | acc_cklr_injp w w':
    w ~> w' -> acc_cklr (inl (inl (inl (inl w)))) (inl (inl (inl (inl w')))).

  Inductive mm_cklr: ccworld cc_cklrs -> mem -> mem -> Prop :=
  | mm_cklr_vaext w m m' (HM: match_mem vaext w m m'): mm_cklr (inr w) m m'
  | mm_cklr_vainj w m m' (HM: match_mem vainj w m m'): mm_cklr (inl (inr w)) m m'
  | mm_cklr_ext w m m' (HM: match_mem ext w m m'): mm_cklr (inl (inl (inr w))) m m'
  | mm_cklr_inj w m m' (HM: match_mem inj w m m'): mm_cklr (inl (inl (inl (inr w)))) m m'
  | mm_cklr_injp w m m' (HM: match_mem injp w m m'): mm_cklr (inl (inl (inl (inl w)))) m m'.

  Inductive mp_cklr: ccworld cc_cklrs -> block -> ptrofs -> block -> ptrofs -> Prop :=
  | mp_cklr_vaext w b ofs b' ofs' (HP: ptrbits_inject (mi vaext w) (b, ofs) (b', ofs')):
      mp_cklr (inr w) b ofs b' ofs'
  | mp_cklr_vainj w b ofs b' ofs' (HP: ptrbits_inject (mi vainj w) (b, ofs) (b', ofs')):
      mp_cklr (inl (inr w)) b ofs b' ofs'
  | mp_cklr_ext w b ofs b' ofs' (HP: ptrbits_inject (mi ext w) (b, ofs) (b', ofs')):
      mp_cklr (inl (inl (inr w))) b ofs b' ofs'
  | mp_cklr_inj w b ofs b' ofs' (HP: ptrbits_inject (mi inj w) (b, ofs) (b', ofs')):
      mp_cklr (inl (inl (inl (inr w)))) b ofs b' ofs'
  | mp_cklr_injp w b ofs b' ofs' (HP: ptrbits_inject (mi injp w) (b, ofs) (b', ofs')):
      mp_cklr (inl (inl (inl (inl w)))) b ofs b' ofs'.

  Inductive mv_cklr: ccworld cc_cklrs -> val -> val -> Prop :=
  | mv_cklr_vaext w v v' (HV: Val.inject (mi vaext w) v v'):
      mv_cklr (inr w) v v'
  | mv_cklr_vainj w v v' (HV: Val.inject (mi vainj w) v v'):
      mv_cklr (inl (inr w)) v v'
  | mv_cklr_ext w v v' (HV: Val.inject (mi ext w) v v'):
      mv_cklr (inl (inl (inr w))) v v'
  | mv_cklr_inj w v v' (HV: Val.inject (mi inj w) v v'):
      mv_cklr (inl (inl (inl (inr w)))) v v'
  | mv_cklr_injp w v v' (HV: Val.inject (mi injp w) v v'):
      mv_cklr (inl (inl (inl (inl w)))) v v'.

  Lemma inject_bytes j bytes y:
    list_rel (memval_inject j) (map Byte bytes) y ->
    y = map Byte bytes.
  Proof.
    revert y. induction bytes; intros; inv H; eauto.
    cbn. f_equal.
    - inv H2. reflexivity.
    - eapply IHbytes. eauto.
  Qed.

  Local Transparent Mem.loadbytes Mem.storebytes.

  Lemma cklr_loadbytes' (c: cklr) (w: world c) m m' b b' ofs ofs' len bytes:
    Mem.loadbytes m b (Ptrofs.unsigned ofs) len = Some (map Byte bytes) ->
    match_mem c w m m' ->
    ptrbits_inject (mi c w) (b, ofs) (b', ofs') ->
    Mem.loadbytes m' b' (Ptrofs.unsigned ofs') len = Some (map Byte bytes).
  Proof.
    intros HL HM HP.
    destruct (zlt 0 len).
    - exploit ptrbits_ptr_inject; eauto.
      eapply Mem.loadbytes_range_perm; eauto. lia. intros HX.
      exploit cklr_loadbytes; eauto. unfold k1, uncurry. rewrite HL.
      intros Ho. inv Ho. apply inject_bytes in H1. congruence.
    - unfold Mem.loadbytes in HL |- *.
      destruct Mem.range_perm_dec; inv HL.
      rewrite Z_to_nat_neg in * by lia. cbn in *.
      symmetry in H0. apply map_eq_nil in H0. subst.
      destruct Mem.range_perm_dec. easy.
      exfalso. apply n. intros p Hp. lia.
  Qed.

  Lemma cklr_loadbytes w m b ofs m' b' ofs' len bytes:
    mm_cklr w m m' ->
    mp_cklr w b ofs b' ofs' ->
    Mem.loadbytes m b (Ptrofs.unsigned ofs) len = Some (map Byte bytes) ->
    Mem.loadbytes m' b' (Ptrofs.unsigned ofs') len = Some (map Byte bytes).
  Proof. intros Hm Hp Hl. inv Hm; inv Hp; eapply cklr_loadbytes'; eauto. Qed.

  Lemma bytes_inject mi bytes:
    list_rel (memval_inject mi) (map Byte bytes) (map Byte bytes).
  Proof.
    induction bytes.
    - constructor.
    - constructor; eauto. constructor.
  Qed.

  Lemma cklr_storebytes' (c: cklr) (w: world c) m1 m2 m3 b1 b2 ofs1 ofs2 bytes:
    bytes <> nil ->
    Mem.storebytes m1 b1 (Ptrofs.unsigned ofs1) (map Byte bytes) = Some m3 ->
    match_mem c w m1 m2 ->
    ptrbits_inject (mi c w) (b1, ofs1) (b2, ofs2) ->
    exists wx m4, w ~> wx
             /\ Mem.storebytes m2 b2 (Ptrofs.unsigned ofs2) (map Byte bytes) = Some m4
             /\ match_mem c wx m3 m4.
  Proof.
    intros HB HS HM HP.
    destruct (zlt 0 (Z.of_nat (length bytes))).
    - exploit ptrbits_ptr_inject; eauto.
      eapply Mem.storebytes_range_perm; eauto.
      rewrite map_length. lia. intros HX.
      exploit cklr_storebytes; eauto.
      left. apply HX. apply bytes_inject.
      unfold k1, uncurry. rewrite HS.
      intros Ho. inv Ho.
      destruct H1 as (wx & Hw & Hm).
      exists wx, y. split; eauto.
    - destruct bytes. congruence. cbn in g. lia.
  Qed.

  Lemma cklr_storebytes w m1 m2 m3 b1 ofs1 b2 ofs2 bytes:
    mm_cklr w m1 m2 ->
    mp_cklr w b1 ofs1 b2 ofs2 ->
    Mem.storebytes m1 b1 (Ptrofs.unsigned ofs1) (map Byte bytes) = Some m3 ->
    exists wx m4, acc_cklr w wx
             /\ Mem.storebytes m2 b2 (Ptrofs.unsigned ofs2) (map Byte bytes) = Some m4
             /\ mm_cklr wx m3 m4.
  Proof.
    intros Hm Hp Hs. inv Hm; inv Hp.
    Ltac solve_cklr_storebytes' :=
      edestruct cklr_storebytes' as (? & ? & ? & ? & ?); eauto;
      [ easy |  eexists _, _; split; repeat (constructor; eauto) ].
    Ltac solve_cklr_storebytes_empty :=
      edestruct cklr_storebytes_empty as (? & ? & ? & ? & ?); [ | eauto | eauto | ]; eauto;
        eexists _, _; split; repeat (constructor; eauto).
    - destruct bytes; [ solve_cklr_storebytes_empty | solve_cklr_storebytes'].
    - destruct bytes; [ solve_cklr_storebytes_empty | solve_cklr_storebytes'].
    - destruct bytes; [ solve_cklr_storebytes_empty | solve_cklr_storebytes'].
    - destruct bytes; [ solve_cklr_storebytes_empty | solve_cklr_storebytes'].
    - destruct bytes; [ solve_cklr_storebytes_empty | solve_cklr_storebytes'].
  Qed.

  Import Datatypes.

  Instance acc_cklr_kf: KripkeFrame unit (ccworld cc_cklrs) :=
    {| acc _ := acc_cklr; |}.

  Instance acc_cklr_refl: Reflexive acc_cklr.
  Proof.
    red. destruct x; eauto. 2: { constructor. reflexivity. }
    destruct c; eauto. 2: { constructor. reflexivity. }
    destruct c; eauto. 2: { constructor. reflexivity. }
    destruct c; eauto. 2: { constructor. reflexivity. }
    constructor. reflexivity.
  Qed.

  Instance acc_cklr_trans: Transitive acc_cklr.
  Proof.
    red. intros x y z Hxy Hyz. inv Hxy; inv Hyz;
      constructor; etransitivity; eauto.
  Qed.

  Inductive mm_cklrs: ccworld (cc_cklrs^{*}) -> mem -> mem -> Prop :=
  | mm_cklrs_zero m: mm_cklrs (existT _ 0%nat tt) m m
  | mm_cklrs_succ n se w wx wn m1 m2 m3:
        w ~> wx /\ mm_cklr wx m1 m2 -> mm_cklrs (existT _ n wn) m2 m3 ->
        mm_cklrs (existT _ (S n) (se, w, wn)) m1 m3.

  Inductive mp_cklrs: ccworld (cc_cklrs^{*}) -> block -> ptrofs -> block -> ptrofs -> Prop :=
  | mp_cklrs_zero b ofs: mp_cklrs (existT _ 0%nat tt) b ofs b ofs
  | mp_cklrs_succ n se w wn b1 ofs1 b2 ofs2 b3 ofs3:
        mp_cklr w b1 ofs1 b2 ofs2 -> mp_cklrs (existT _ n wn) b2 ofs2 b3 ofs3 ->
        mp_cklrs (existT _ (S n) (se, w, wn)) b1 ofs1 b3 ofs3.

  Inductive mv_cklrs: ccworld (cc_cklrs^{*}) -> val -> val -> Prop :=
  | mv_cklrs_zero v: mv_cklrs (existT _ 0%nat tt) v v
  | mv_cklrs_succ n se w wn v1 v2 v3:
        mv_cklr w v1 v2 -> mv_cklrs (existT _ n wn) v2 v3 ->
        mv_cklrs (existT _ (S n) (se, w, wn)) v1 v3.

  Lemma cklr_match_query_inv (w: ccworld cc_cklrs) b ofs len m q vf i:
    match_query cc_cklrs w
                (cq vf rw_sig [Vint i; Vptr b ofs; Vlong len] m)
                q ->
    exists m' b' ofs' vf',
      q = (cq vf' rw_sig [Vint i; Vptr b' ofs'; Vlong len] m')
      /\ mm_cklr w m m' /\ mp_cklr w b ofs b' ofs' /\ mv_cklr w vf vf'.
  Proof.
    Ltac solve_cklr_match_query_inv :=
      cbn; intros Hq; inv Hq; repeat inv_inj;
      eexists _, _, _, _; repeat split; try econstructor;eauto.
    destruct w. 2: solve_cklr_match_query_inv.
    destruct c. 2: solve_cklr_match_query_inv.
    destruct c. 2: solve_cklr_match_query_inv.
    destruct c; solve_cklr_match_query_inv.
  Qed.

  Lemma cklrs_match_query_inv (nw: ccworld (cc_cklrs ^ {*})) b ofs len m q vf i:
    match_query (cc_cklrs ^ {*}) nw
                (cq vf rw_sig [Vint i; Vptr b ofs; Vlong len] m)
                q ->
    exists m' b' ofs' vf',
      q = (cq vf' rw_sig [Vint i; Vptr b' ofs'; Vlong len] m')
      /\ mm_cklrs nw m m' /\ mp_cklrs nw b ofs b' ofs' /\ mv_cklrs nw vf vf'.
  Proof.
    destruct nw. cbn. revert vf b ofs m. induction x; cbn.
    - intros. subst. destruct c.
      eexists _, _, _, _. repeat split; try econstructor; eauto.
    - cbn in *. destruct c as [[se w] wn].
      intros * (qm & Hq1 & Hq2).
      apply cklr_match_query_inv in Hq1 as
          (mm & bm & ofsm & vfm & Hqm & Hmm & Hmp & Hmv).
      subst qm.
      specialize (IHx _ _ _ _ _ Hq2) as
        (m' & b' & ofs' & vf' & Hq' & Hm' & Hp' & Hv').
      exists m', b', ofs', vf'. repeat split; try econstructor; eauto.
      split. reflexivity. eauto.
  Qed.

  Lemma cklr_match_query_inv' (w: ccworld cc_cklrs) b ofs len m q vf i sg:
    match_query cc_cklrs w
                (cq vf sg [Vint i; Vptr b ofs; Vint len] m)
                q ->
    exists m' b' ofs' vf',
      q = (cq vf' sg [Vint i; Vptr b' ofs'; Vint len] m')
      /\ mm_cklr w m m' /\ mp_cklr w b ofs b' ofs' /\ mv_cklr w vf vf'.
  Proof.
    destruct w. 2: solve_cklr_match_query_inv.
    destruct c. 2: solve_cklr_match_query_inv.
    destruct c. 2: solve_cklr_match_query_inv.
    destruct c; solve_cklr_match_query_inv.
  Qed.

  Lemma cklrs_match_query_inv' (nw: ccworld (cc_cklrs ^ {*})) b ofs len m q vf i sg:
    match_query (cc_cklrs ^ {*}) nw
                (cq vf sg [Vint i; Vptr b ofs; Vint len] m)
                q ->
    exists m' b' ofs' vf',
      q = (cq vf' sg [Vint i; Vptr b' ofs'; Vint len] m')
      /\ mm_cklrs nw m m' /\ mp_cklrs nw b ofs b' ofs' /\ mv_cklrs nw vf vf'.
  Proof.
    destruct nw. cbn. revert vf b ofs m. induction x; cbn.
    - intros. subst. destruct c.
      eexists _, _, _, _. repeat split; try econstructor; eauto.
    - cbn in *. destruct c as [[se w] wn].
      intros * (qm & Hq1 & Hq2).
      apply cklr_match_query_inv' in Hq1 as
          (mm & bm & ofsm & vfm & Hqm & Hmm & Hmp & Hmv).
      subst qm.
      specialize (IHx _ _ _ _ _ Hq2) as
        (m' & b' & ofs' & vf' & Hq' & Hm' & Hp' & Hv').
      exists m', b', ofs', vf'. repeat split; try econstructor; eauto.
      split. reflexivity. eauto.
  Qed.

  Lemma cklr_match_reply_intro w0 w m1 m2 v:
    w0 ~> w -> mm_cklr w m1 m2 ->
    match_reply cc_cklrs w0 {| cr_retval := Vint v; cr_mem := m1 |}
                {| cr_retval := Vint v; cr_mem := m2 |}.
  Proof.
    intros Hw Hm. inv Hw; inv Hm.
    - eexists w'; split; eauto. constructor; eauto.
    - eexists w'; split; eauto. constructor; eauto.
    - eexists w'; split; eauto. constructor; eauto.
    - eexists w'; split; eauto. constructor; eauto.
    - eexists w'; split; eauto. constructor; eauto.
  Qed.

  Lemma cklrs_match_reply_intro x c m1 m2 v:
    mm_cklrs (existT (fun n : nat => ccworld (cc_cklrs ^ n)) x c) m1 m2 ->
    match_reply (cc_cklrs ^ x) c {| cr_retval := Vint v; cr_mem := m1 |}
                {| cr_retval := Vint v; cr_mem := m2 |}.
  Proof.
    revert m1 m2. induction x.
    - intros. inv H. reflexivity.
    - intros. simple inversion H. inv H0.
      exploit eq_sigT_fst. apply H2. intros. inv H0.
      subst_dep.
      destruct H1. cbn.
      exists (cr (Vint v) m3). split; eauto.
      eapply cklr_match_reply_intro; eauto.
  Qed.

  Hypothesis (Hwin64: Archi.win64 = false).

  Import ValueDomain ValueAnalysis VAInject.

  Inductive mm_ca: ccworld (cc_cklrs^{*}) -> world vainj -> mem -> mem -> mem -> Prop :=
  | mm_ca_intro wn wi wj m1 m2 m3 se mbefore
    (HN: mm_cklrs wn m1 m2) (HI: match_mem inj wj m2 m3) (HJ: wi ~> wj)
    (HRO: romatch_all se (bc_of_symtbl se) m2)
    (HNEXT: (Genv.genv_next se <= Mem.nextblock m2)%positive)
    (MBEFORE: Mem.unchanged_on (fun _ _ => False) mbefore m2):
    mm_ca wn (se, wi) mbefore m1 m3.

  Inductive mp_ca: ccworld (cc_cklrs^{*}) -> world inj -> block -> ptrofs -> block -> ptrofs -> Prop :=
  | mp_ca_intro wn wi b1 ofs1 b2 ofs2 b3 ofs3:
    mp_cklrs wn b1 ofs1 b2 ofs2 ->
    ptrbits_inject (mi inj wi) (b2, ofs2) (b3, ofs3) ->
    mp_ca wn wi b1 ofs1 b3 ofs3.

  Inductive mv_ca: ccworld (cc_cklrs^{*}) -> world inj -> val -> val -> Prop :=
  | mv_ca_intro wn wi v1 v2 v3
    (HN: mv_cklrs wn v1 v2) (HI: Val.inject (mi inj wi) v2 v3):
    mv_ca wn wi v1 v3.

  Lemma mp_cklr_acc w1 w2 b1 ofs1 b2 ofs2:
    mp_cklr w1 b1 ofs1 b2 ofs2 -> acc_cklr w1 w2 -> mp_cklr w2 b1 ofs1 b2 ofs2.
  Proof. intros HP HW. inv HP; inv HW; constructor; rauto. Qed.

  (* Lemma cklr_find_funct p se1 se2 vf1 vf2 w f: *)
  (*   match_senv cc_cklrs w se1 se2 -> *)
  (*   mv_cklr w vf1 vf2 -> *)
  (*   Genv.find_funct (Clight.globalenv se1 p) vf1 = Some f -> *)
  (*   Genv.find_funct (Genv.globalenv se2 p) vf2 = Some f. *)
  (* Proof. *)
  (*   intros HSE HVF HF. pose proof (match_program_gen_id p) as H. *)
  (*   inv HVF. *)
  (*   - cbn in *. inv HSE. cbn in HV. inv HV; eauto. *)
  (*     + unfold inj_of_bc in H2. *)
  (*       destruct (bc b1); inv H2; *)
  (*         rewrite Ptrofs.add_zero; eauto. *)
  (*     + unfold Genv.find_funct in HF. inv HF. *)
  (*   - destruct w0. cbn in *. destruct HSE as [-> HSE]. inv HSE. *)
  (*     eapply Genv.find_funct_match in H as (c & tfd & Hw & Hf & Hm); *)
  (*      subst; eauto. *)
  (*   - destruct w0. inv HSE. cbn in HV. inv HV; eauto. *)
  (*     + inv H0. rewrite Ptrofs.add_zero. eauto. *)
  (*     + unfold Genv.find_funct in HF. inv HF. *)
  (*   - destruct w0. inv HSE. cbn in *. *)
  (*     eapply Genv.find_funct_match in H as (c & tfd & Hw & Hf & Hm); *)
  (*      subst; eauto. *)
  (*   - destruct w0. inv HSE. cbn in *. *)
  (*     eapply Genv.find_funct_match in H as (c & tfd & Hw & Hf & Hm'); *)
  (*      subst; eauto. *)
  (* Qed. *)

  (* Lemma cklrs_find_funct p se1 se2 vf1 vf2 wn f: *)
  (*   match_senv (cc_cklrs ^ {*}) wn se1 se2 -> *)
  (*   mv_cklrs wn vf1 vf2 -> *)
  (*   Genv.find_funct (Clight.globalenv se1 p) vf1 = Some f -> *)
  (*   Genv.find_funct (Genv.globalenv se2 p) vf2 = Some f. *)
  (* Proof. *)
  (*   destruct wn. revert se1 se2 vf1 vf2. induction x. *)
  (*   - cbn. intros. subst. inv H0. eauto. *)
  (*   - intros * HSE HV. *)
  (*     destruct c as [[se w] wn]. *)
  (*     destruct HSE as (Hse1 & Hsen). *)
  (*     simple inversion HV. inv H. subst. *)
  (*     exploit eq_sigT_fst. apply H1. intros HNat. inv HNat. *)
  (*     subst_dep. inv H1. intros Hv1 Hvn Hf. *)
  (*     eapply IHx. 1, 2: cbn; eauto. *)
  (*     eapply cklr_find_funct; eauto. *)
  (* Qed. *)

  Lemma cklrs_loadbytes w m b ofs m' b' ofs' len bytes:
    mm_cklrs w m m' ->
    mp_cklrs w b ofs b' ofs' ->
    Mem.loadbytes m b (Ptrofs.unsigned ofs) len = Some (map Byte bytes) ->
    Mem.loadbytes m' b' (Ptrofs.unsigned ofs') len = Some (map Byte bytes).
  Proof.
    destruct w. revert m b ofs m' b' ofs' len bytes. induction x.
    - intros. inv H. subst_dep. inv H0. eauto.
    - intros * HM HP HL.
      simple inversion HM. inv H.
      exploit eq_sigT_fst. apply H1. intros HNat. inv HNat.
      subst_dep. intros (Hw & Hm) Hms.
      simple inversion HP. inv H.
      exploit eq_sigT_fst. apply H1. intros HNat. inv HNat.
      subst_dep. inv H1. intros Hp Hps.
      erewrite IHx. reflexivity. apply Hms. apply Hps. eauto.
      eapply cklr_loadbytes. 1, 3: eauto.
      inv Hp; inv Hw; constructor; rstep.
  Qed.

  Lemma cklrs_storebytes w m1 m2 b1 ofs1 b2 ofs2 bytes m3:
    mm_cklrs w m1 m2 ->
    mp_cklrs w b1 ofs1 b2 ofs2 ->
    Mem.storebytes m1 b1 (Ptrofs.unsigned ofs1) (map Byte bytes) = Some m3 ->
    exists m4,
      Mem.storebytes m2 b2 (Ptrofs.unsigned ofs2) (map Byte bytes) = Some m4
      /\ mm_cklrs w m3 m4.
  Proof.
    destruct w. revert m1 m2 b1 ofs1 b2 ofs2 m3. induction x.
    - intros. inv H. subst_dep. inv H0.
      exists m3. split; eauto. constructor.
    - intros * HM HP HS.
      simple inversion HM. inv H.
      exploit eq_sigT_fst. apply H1. intros HNat. inv HNat.
      subst_dep. intros (Hw & Hm) Hms.
      simple inversion HP. inv H.
      exploit eq_sigT_fst. apply H1. intros HNat. inv HNat.
      subst_dep. intros Hp Hps. inv H1.
      eapply mp_cklr_acc in Hp. 2: apply Hw.
      exploit cklr_storebytes; eauto.
      intros (ww & mx & Hww & Hmx & Hmm).
      specialize (IHx _ _ _ _ _ _ _ _ Hms Hps Hmx) as (mt & Hmt & Hmmt).
      exists mt; split; eauto.
      econstructor; eauto. split. 2: eauto.
      etransitivity; eauto.
  Qed.

  Lemma ca_storebytes n w m1 b1 ofs1 m2 b2 ofs2 bytes m3 se mbefore:
    mm_ca n (se, w) mbefore m1 m2 ->
    mp_ca n w b1 ofs1 b2 ofs2 ->
    Mem.storebytes m1 b1 (Ptrofs.unsigned ofs1) (map Byte bytes) = Some m3 ->
    exists m4,
      Mem.storebytes m2 b2 (Ptrofs.unsigned ofs2) (map Byte bytes) = Some m4
      /\ mm_ca n (se, w) mbefore m3 m4.
  Proof.
    intros HM HP HS. inv HM. inv HP.
    exploit cklrs_storebytes; eauto. intros (mc & Hmc & Hmmc).
    assert (exists wt mt,  wj ~> wt
             /\ Mem.storebytes m2 b2 (Ptrofs.unsigned ofs2) (map Byte bytes) = Some mt
             /\ match_mem inj wt mc mt)
      as (wt & mt & Hwt & Hmt & Hmm).
    { destruct bytes.
      - eapply (cklr_storebytes_empty inj) in Hmc; eauto.
      - eapply cklr_storebytes' in Hmc; eauto.
        apply Hmc. congruence. rstep. }
    exists mt. split; eauto. econstructor; eauto.
    - etransitivity; eauto.
    - intros b Hb. eapply romatch_storebytes; eauto.
    - erewrite Mem.nextblock_storebytes; eauto.
    - destruct MBEFORE. split; try easy.
      + etransitivity; eauto.
        erewrite <- Mem.nextblock_storebytes; eauto.
        reflexivity.
      + rewrite unchanged_on_alloc_flag. symmetry.
        eapply Mem.storebytes_alloc_flag; eauto.
  Qed.

  Lemma ca_loadbytes n w m1 b1 ofs1 m2 b2 ofs2 bytes se mbefore len:
    mm_ca n (se, w) mbefore m1 m2 ->
    mp_ca n w b1 ofs1 b2 ofs2 ->
    Mem.loadbytes m1 b1 (Ptrofs.unsigned ofs1) len = Some (map Byte bytes) ->
    Mem.loadbytes m2 b2 (Ptrofs.unsigned ofs2) len = Some (map Byte bytes).
  Proof.
    intros HM HP HL. inv HM. inv HP.
    exploit cklrs_loadbytes; eauto. intros Hl.
    eapply cklr_loadbytes'; eauto. rstep.
  Qed.

  Definition nw_of_world (w: ccworld CAsm.cc_compcert): sigT (fun n => ccworld (cc_cklrs ^ n)).
  Proof. cbn in w. destruct w. destruct p. exact s0. Defined.

  Definition injw_of_world (w: ccworld CAsm.cc_compcert): world vainj.
  Proof. cbn in w. destruct w.
         destruct p0. destruct p1. destruct p2.
         exact p3. Defined.

  Definition caw_of_world (w: ccworld CAsm.cc_compcert): cc_ca_world.
  Proof. cbn in w. eprod_crush. exact c. Defined.

  Definition sig_of_world (w: ccworld CAsm.cc_compcert): signature.
  Proof. cbn in w. destruct w.
         destruct p0. destruct p0. destruct p0. exact s1. Defined.

  Import ListNotations.

  Lemma rw_sig_size_arguments: size_arguments rw_sig = 0.
  Proof. cbn. destruct Archi.win64; cbn; lia. Qed.

End SYS_C_ASM.



(** ** C and Asm Loader definitions *)

Require Import CAsm InitMem Maps AST.
Require Import Conventions Mach Asm.
Require Import Ctypes.

(* ----------------------------------------------------------------- *)
(** ** Find_funct utilities, used in Rot13 example *)

Require Import AST Ctypes.
Require Import Util.

Definition read_asm : Asm.fundef := AST.External (EF_external "read" rw_sig).
Definition write_asm : Asm.fundef := AST.External (EF_external "write" rw_sig).


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
    | [ H: Compiler.match_if _ ?m _ _ |- _] => unfold Compiler.match_if, m in H; rewrite Load.if_commute in H
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

  Lemma match_program_gen_id {F V} (p: AST.program F V):
    match_program_gen (fun _ => eq) eq tt p p.
  Proof.
    split. 2: eauto.
    generalize (prog_defs p) as l.
    induction l; intros; constructor; eauto.
    constructor. reflexivity.
    destruct a. cbn. destruct g; repeat econstructor; eauto.
    destruct v. constructor. reflexivity.
    Unshelve. exact tt.
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
  Import ValueDomain.

  Lemma cklr_find_funct p se1 se2 vf1 vf2 w f:
    match_senv cc_cklrs w se1 se2 ->
    mv_cklr w vf1 vf2 ->
    Genv.find_funct (Clight.globalenv se1 p) vf1 = Some f ->
    Genv.find_funct (Genv.globalenv se2 p) vf2 = Some f.
  Proof.
    intros HSE HVF HF. pose proof (match_program_gen_id p) as H.
    inv HVF.
    - cbn in *. inv HSE. cbn in HV. inv HV; eauto.
      + unfold inj_of_bc in H2.
        destruct (bc b1); inv H2;
          rewrite Ptrofs.add_zero; eauto.
      + unfold Genv.find_funct in HF. inv HF.
    - destruct w0. cbn in *. destruct HSE as [-> HSE]. inv HSE.
      eapply Genv.find_funct_match in H as (c & tfd & Hw & Hf & Hm);
       subst; eauto.
    - destruct w0. inv HSE. cbn in HV. inv HV; eauto.
      + inv H0. rewrite Ptrofs.add_zero. eauto.
      + unfold Genv.find_funct in HF. inv HF.
    - destruct w0. inv HSE. cbn in *.
      eapply Genv.find_funct_match in H as (c & tfd & Hw & Hf & Hm);
       subst; eauto.
    - destruct w0. inv HSE. cbn in *.
      eapply Genv.find_funct_match in H as (c & tfd & Hw & Hf & Hm');
       subst; eauto.
  Qed.

  Lemma cklrs_find_funct p se1 se2 vf1 vf2 wn f:
    match_senv (cc_cklrs ^ {*}) wn se1 se2 ->
    mv_cklrs wn vf1 vf2 ->
    Genv.find_funct (Clight.globalenv se1 p) vf1 = Some f ->
    Genv.find_funct (Genv.globalenv se2 p) vf2 = Some f.
  Proof.
    destruct wn. revert se1 se2 vf1 vf2. induction x.
    - cbn. intros. subst. inv H0. eauto.
    - intros * HSE HV.
      destruct c as [[se w] wn].
      destruct HSE as (Hse1 & Hsen).
      simple inversion HV. inv H. subst.
      exploit eq_sigT_fst. apply H1. intros HNat. inv HNat.
      subst_dep. inv H1. intros Hv1 Hvn Hf.
      eapply IHx. 1, 2: cbn; eauto.
      eapply cklr_find_funct; eauto.
  Qed.


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
    eapply cklrs_find_funct in HF. 2, 3: eauto. clear HSE HVF.
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
    eapply cklrs_find_funct in HF. 2, 3: eauto. clear HSE HVF.
    eapply match_prog_write; eauto. apply HI. apply HF.
  Qed.

End FIND_FUNCT.

(** ------------------------------------------------------------------------- *)
(** Strategy definitions *)

Require Import Poset Lattice Downset Program.Equality.
Require Import IntStrat CompCertStrat.

Module STRAT.

Definition P : esig := {| op := Genv.symtbl; ar _ := Integers.int |}.
Inductive F_op : Type := F_read : int -> F_op | F_write : list byte -> F_op.
Definition F : esig :=
  {|
    op := F_op;
    ar m := match m with F_read _ => list byte | F_write _ => Integers.int end;
  |}.
Definition S : esig := F + F.

Section C_LOADER.
  Import Ctypes Clight.
  Context (prog: Clight.program).
  Let sk := AST.erase_program prog.

  (** *** The entry part of the C Loader *)
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

  (** *** The runtime part of the C Loader *)
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

  (** *** The entry part of the Asm Loader *)
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

  (** *** The runtime part of the Asm Loader *)
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

(** Deterministic property of the asm runtime *)

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

(** ** Loader correctness *)

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
            split; try easy. intros HX. inv HX. lia. apply Hwin.
          - rewrite rw_sig_size_arguments.
            intros * HX. inv HX. lia. apply Hwin. }
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
            intros * HX. inv HX. lia. apply Hwin. }
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

End STRAT.
