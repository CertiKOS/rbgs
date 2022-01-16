From Coq Require Import
     Relations
     RelationClasses
     List
     FunctionalExtensionality.
From models Require Import
     IntSpec.
From examples Require Import
     CAL CompCertIntSpec RefConv.
From lattices Require Import
     Upset Downset FCD.
From structures Require Import
     Effects Lattice.
From compcert Require Import
     Memory AST Values
     Clight Ctypes
     LanguageInterface
     Events Globalenvs
     Smallstep.
From compcertox Require Import
     Lifting CModule.
Import ListNotations ISpec.

Unset Asymmetric Patterns.

(** The language interface "C simple" which does not include the memory *)
Inductive c_esig : esig :=
| c_event : val -> signature -> list val -> c_esig val.

(** Some auxiliary definitions *)
Definition overlay_rc {E: esig} {S1 S2: Type} (rc: E <=> c_esig) (rel: S2 -> mem * S1 -> Prop):
  E # S2 <=> c_esig # (mem * S1)%type := rc * rel_rc rel.

Inductive lts_state_rc_rel {S: Type}: rc_rel (c_esig # (mem * S)) (li_c @ S)%li :=
| lts_state_rc_rel_intro vf sg args m s R (qs: query (li_c @ S)) qe:
  qs = (cq vf sg args m, s) ->
  qe = st (c_event vf sg args) (m, s) ->
  subrel (fun '(r, (m, s)) '(r', s') => r' = cr r m /\ s = s') R ->
  lts_state_rc_rel _ qe _ (li_sig qs) R.

Program Definition lts_state_rc {S: Type} : c_esig # (mem * S) <=> (li_c @ S)%li :=
  {|
    refconv_rel := lts_state_rc_rel;
  |}.
Next Obligation.
  intros x y Hxy H. destruct H.
  econstructor; eauto. etransitivity; eauto.
Qed.

Inductive st_mem_rc_rel {S: Type}: rc_rel (s_esig S) (s_esig (mem * S)) :=
| st_mem_rc_rel_intro s m R:
  subrel (fun s' '(m', t') => s' = t' /\ m = m') R ->
  st_mem_rc_rel _ (state_event s) _ (state_event (m, s)) R.

Program Definition st_mem_rc {S: Type}: s_esig S <=> s_esig (mem * S) :=
  {|
    refconv_rel := st_mem_rc_rel;
  |}.
Next Obligation.
  intros x y Hxy H. destruct H.
  constructor. etransitivity; eauto.
Qed.

Definition underlay_rc {E: esig} {S: Type} (rc: E <=> c_esig):
  E # S <=> c_esig # (mem * S) := rc * st_mem_rc.

(** ** Construction of a certified abstraction layer *)
Record certi_layer {E1 E2: esig} {S1 S2: Type} {se: Genv.symtbl} :=
  {
    L1: 0 ~> E1 * s_esig S1;    (** underlay *)
    L1_rc: E1 <=> c_esig;
    L2: 0 ~> E2 * s_esig S2;    (** overlay *)
    L2_rc: E2 <=> c_esig;
    module: list Clight.program;
    sk: AST.program unit unit;
    abs_rel: S2 -> mem * S1 -> Prop;

    layer_rel:
    L2 [= right_arrow (overlay_rc L2_rc abs_rel)
       @ right_arrow lts_state_rc
       @ ang_lts_spec (((semantics module sk) @ S1)%lts se)
       @ left_arrow lts_state_rc
       @ left_arrow (underlay_rc L1_rc)
       @ L1;
  }.

(** ** Layer Composition *)
Section COMP.

  Context {E1 E2 E3: esig} {S1 S2 S3: Type} (se: Genv.symtbl).
  Context (C1: @certi_layer E1 E2 S1 S2 se)
          (C2: @certi_layer E2 E3 S2 S3 se).
  Context (sk_comp: AST.program unit unit)
          (Hsk: Linking.link (sk C1) (sk C2) = Some sk_comp).
  Program Definition comp_certi_layer: @certi_layer E1 E3 S1 S3 se :=
    {|
      L1 := L1 C1;
      L1_rc := L1_rc C1;
      L2 := L2 C2;
      L2_rc := L2_rc C2;
      module := module C1 ++ module C2;
      sk := sk_comp;
      (* This is probably wrong *)
      abs_rel :=
      fun s3 '(m, s1) =>
        exists s2, (abs_rel C1) s2 (m, s1)
              /\ (abs_rel C2) s3 (m, s2);
    |}.
  Next Obligation.
  Admitted.

End COMP.

(** * Example: ring buffer and bounded queue *)

(** With CompCertO semantics embedded in the interaction specification, we
    substitute Clight programs for the layer implementation. *)

(** ** Language interfaces vs. effect signatures *)

(** We define "marshalling" transformations between coarse-grained language
    interfaces and fine-grained effect signatures as adjunctions, similar to the
    embedding of calling conventions. We lift the language interfaces with
    abstract states to smooth the convertion. To further connect the abstract
    states with values in memory blocks we use the calling conventions induced
    by the abstraction relations from CompCertOX. *)

Require Import Coqlib.

Definition set_id: positive := 101.
Definition get_id: positive := 102.
Definition inc1_id: positive := 103.
Definition inc2_id: positive := 104.
Definition enq_id: positive := 105.
Definition deq_id: positive := 106.

(** ** Definition of Clight program *)
Definition arr_id: positive := 1.
Definition cnt1_id: positive := 2.
Definition cnt2_id: positive := 3.
Definition get_arg_id: positive := 1.
Definition set_arg1_id: positive := 1.
Definition set_arg2_id: positive := 2.
Definition enq_arg_id: positive := 1.

Require Import Maps.

Section CLIGHT.
  Notation tint := (Tint I32 Unsigned noattr).
  Notation tarray := (fun ty size => Tarray ty size noattr).
  Notation tptr := (fun ty => Tpointer ty noattr).
  Notation tvoid := (Tvoid).

  Definition Nz: Z := Z.of_nat CAL.N.

  (**
<<
    int get(int i) {
      return arr[i];
    }
>>
   *)
  Definition rb_get_body : statement :=
    Sreturn
      (Some
         (Ederef
            (Ebinop Cop.Oadd
                    (Evar arr_id (tarray tint Nz))
                    (Evar get_arg_id tint)
                    (tptr tint))
            tint)).
  Definition rb_get : function :=
    {|
      fn_return := tint;
      fn_callconv := cc_default;
      fn_params := [(get_arg_id, tint)];
      fn_vars := [];
      fn_temps := [];
      fn_body := rb_get_body;
    |}.

  (**
<<
    void set(int i, int v) {
      arr[i] = v;
    }
>>
   *)
  Definition rb_set_body : statement :=
    Sassign
      (Ederef
         (Ebinop Cop.Oadd
                 (Evar arr_id (tarray tint Nz))
                 (Evar set_arg1_id tint)
                 (tptr tint))
         tint)
      (Evar set_arg2_id tint).
  Definition rb_set : function :=
    {|
      fn_return := tvoid;
      fn_callconv := cc_default;
      fn_params := [(set_arg1_id, tint); (set_arg2_id, tint)];
      fn_vars := [];
      fn_temps := [];
      fn_body := rb_set_body;
    |}.
  (**
<<
    int inc1() {
      cnt1 += 1;
      return cnt1;
    }
>>
  *)
  Definition rb_inc1_body : statement :=
    Sassign
      (Ederef (Evar cnt1_id tint) tint)
      (Ebinop Cop.Oadd
              (Evar cnt1_id tint)
              (Econst_int (Integers.Int.repr 1) tint)
              tint).
  Definition rb_inc1 : function :=
    {|
      fn_return := tvoid;
      fn_callconv := cc_default;
      fn_params := [];
      fn_vars := [];
      fn_temps := [];
      fn_body := rb_inc1_body;
    |}.

  (**
<<
    int inc2() {
      cnt2 += 1;
      return cnt2;
    }
>>
  *)
  Definition rb_inc2_body : statement :=
    Sassign
      (Ederef (Evar cnt2_id tint) tint)
      (Ebinop Cop.Oadd
              (Evar cnt2_id tint)
              (Econst_int (Integers.Int.repr 1) tint)
              tint).
  Definition rb_inc2 : function :=
    {|
      fn_return := tvoid;
      fn_callconv := cc_default;
      fn_params := [];
      fn_vars := [];
      fn_temps := [];
      fn_body := rb_inc2_body;
    |}.
  (* FIXME: *)
  Definition arr_gvar : globvar type :=
    {|
      gvar_info := tarray tint Nz;
      gvar_init := [Init_space (Nz * 4)];
      gvar_readonly := false;
      gvar_volatile := false;
    |}.
  Program Definition rb_program: Clight.program :=
    {|
      prog_defs := [(get_id, Gfun (Internal rb_get));
        (set_id, Gfun (Internal rb_set));
        (inc1_id, Gfun (Internal rb_inc1));
        (inc2_id, Gfun (Internal rb_inc2));
        (arr_id, Gvar arr_gvar)];
      prog_public := [get_id; set_id; inc1_id; inc2_id];
      prog_main := 999%positive;
      prog_types := [];
      prog_comp_env := (PTree.empty _);
    |}.
  Next Obligation. reflexivity. Qed.

  (**
<<
    void enq(int v) {
      int i = inc2();
      set(i, v);
    }
>>
   *)

  Definition bq_enq_tmp : positive := 2.
  Definition bq_enq_body : statement :=
    Ssequence
      (Scall (Some bq_enq_tmp) (Evar inc2_id (Tfunction Tnil tint cc_default)) nil)
      (Ssequence
         (Scall None (Evar set_id (Tfunction (Tcons tint (Tcons tint Tnil)) tvoid cc_default))
                ([Etempvar bq_enq_tmp tint; Etempvar enq_arg_id tint]))
         (Sreturn None)).
  Definition bq_enq : function :=
    {|
      fn_return := tvoid;
      fn_callconv := cc_default;
      fn_params := [(enq_arg_id, tint)];
      fn_vars := [];
      fn_temps := [(bq_enq_tmp, tint)];
      fn_body := bq_enq_body;
    |}.

  (**
<<
    int deq() {
      int i = inc1();
      return get(i);
    }
>>
   *)
  Definition bq_deq_tmp1 : positive := 1.
  Definition bq_deq_tmp2 : positive := 2.
  Definition bq_deq_body : statement :=
    Ssequence
      (Scall (Some bq_deq_tmp1) (Evar inc1_id (Tfunction Tnil tint cc_default)) nil)
      (Ssequence
         (Scall (Some bq_deq_tmp2) (Evar get_id (Tfunction (Tcons tint Tnil) tint cc_default))
                ([Evar bq_deq_tmp1 tint]))
         (Sreturn (Some (Evar bq_deq_tmp2 tint)))).
  Definition bq_deq : function :=
    {|
      fn_return := tint;
      fn_callconv := cc_default;
      fn_params := [];
      fn_vars := [];
      fn_temps := [(bq_deq_tmp1, tint); (bq_deq_tmp2, tint)];
      fn_body := bq_enq_body;
    |}.

  Definition inc1_sg: signature :=
    signature_of_type Tnil tint cc_default.
  Definition inc2_sg: signature :=
    signature_of_type Tnil tint cc_default.
  Definition get_sg: signature :=
    signature_of_type (Tcons tint Tnil) tint cc_default.
  Definition set_sg: signature :=
    signature_of_type (Tcons tint (Tcons tint Tnil)) tvoid cc_default.

  Definition inc1_ext: fundef function :=
    External (EF_external "inc1" inc1_sg) Tnil tint cc_default.
  Definition inc2_ext: fundef function :=
    External (EF_external "inc2" inc2_sg) Tnil tint cc_default.
  Definition get_ext: fundef function :=
    External (EF_external "get" get_sg) (Tcons tint Tnil) tint cc_default.
  Definition set_ext: fundef function :=
    External (EF_external "set" set_sg) (Tcons tint (Tcons tint Tnil)) tvoid cc_default.

  Program Definition bq_program : Clight.program :=
    {|
      prog_defs := [(enq_id, Gfun (Internal bq_enq));
                    (deq_id, Gfun (Internal bq_deq));
                    (inc1_id, Gfun inc1_ext);
                    (inc2_id, Gfun inc2_ext);
                    (get_id, Gfun get_ext);
                    (set_id, Gfun set_ext)];
      prog_public := [enq_id; deq_id];
      prog_main := 999%positive;
      prog_types := [];
      prog_comp_env := (PTree.empty _);
    |}.
  Next Obligation. reflexivity. Qed.

  Definition enq_sg: signature :=
    signature_of_type (Tcons tint Tnil) tvoid cc_default.
  Definition deq_sg: signature :=
    signature_of_type Tnil tint cc_default.

End CLIGHT.

Section MARSHALL.

  (* TODO: there seems to be a problem with the definition of subst: the arity
     [ar] has to be the same for both E and F. *)
  Parameter spec_val_rel: CAL.val -> val -> Prop.
  Context (se: Genv.symtbl).

  Inductive val_rel : forall ar, ar -> val -> Prop :=
  | unit_val: val_rel unit tt Vundef
  | nat_val n i:
    Integers.Int.intval i = Z.of_nat n -> val_rel nat n (Vint i)
  | spec_val sv v:
    spec_val_rel sv v -> val_rel CAL.val sv v.

  Inductive rb_rel : forall ar, rb_sig ar -> c_query -> Prop :=
  | set_rel i v b arg1 arg2:
    val_rel _ i arg1 -> val_rel _ v arg2 ->
    Genv.find_symbol se set_id = Some b ->
    rb_rel _ (set i v) (cq (Vptr b Integers.Ptrofs.zero) set_sg [arg1;arg2])
  | get_rel i b arg:
    val_rel _ i arg ->
    Genv.find_symbol se get_id = Some b ->
    rb_rel _ (CAL.get i) (cq (Vptr b Integers.Ptrofs.zero) get_sg [arg])
  | inc1_rel b:
    Genv.find_symbol se inc1_id = Some b ->
    rb_rel _ inc1 (cq (Vptr b Integers.Ptrofs.zero) inc1_sg [])
  | inc2_rel b:
    Genv.find_symbol se inc2_id = Some b ->
    rb_rel _ inc2 (cq (Vptr b Integers.Ptrofs.zero) inc2_sg []).

  Inductive bq_rel : forall ar, bq_sig ar -> c_query -> Prop :=
  | enq_rel v b arg:
    val_rel _ v arg ->
    Genv.find_symbol se enq_id = Some b ->
    bq_rel _ (enq v) (cq (Vptr b Integers.Ptrofs.zero) enq_sg [arg])
  | deq_rel b:
    Genv.find_symbol se get_id = Some b ->
    bq_rel _ deq (cq (Vptr b Integers.Ptrofs.zero) deq_sg []).

  Inductive args_type_check (vs: list val) (sg: signature) : Prop :=
  | args_tyck ts:
    Cop.val_casted_list vs ts ->
    typlist_of_typelist ts = sig_args sg ->
    args_type_check vs sg.
  Inductive retval_type_check (v: val) (sg: signature) : Prop :=
  | ret_tyck t:
    Cop.val_casted v t ->
    opttyp_of_type t = sig_res sg ->
    retval_type_check v sg.

  (** Morphisms that compose the adjunctions Erb ⇆ C and Ebq ⇆ C *)

  Definition rb_left: rb_sig ~> li_c :=
    fun _ '(li_sig q) =>
      sup ar, sup { m | rb_rel ar m q /\ args_type_check (cq_args q) (cq_sg q)} ,
      n <- int m;
      inf { r | val_rel ar n r /\ retval_type_check r (cq_sg q) },
      ret (cr r).

  Definition rb_right: li_c ~> rb_sig :=
    fun _ m =>
      inf { q | rb_rel _ m q /\ args_type_check (cq_args q) (cq_sg q)},
      r <- query_int q;
      sup { n | val_rel _ n (cr_retval r) /\
                  retval_type_check (cr_retval r) (cq_sg q) },
      ret n.

  Lemma rb_epsilon: rb_left @ rb_right [= identity.
  Proof.
    intros ? [q].
    (* destruct q as [vf sg args]. *)
    unfold compose, identity, rb_left, rb_right.
    rewrite Sup.mor. apply sup_iff. intros ar.
    unfold fsup. rewrite Sup.mor. apply sup_iff.
    intros [m [? ?]]. cbn. intm.
    unfold finf. rewrite Inf.mor. eapply (inf_at (exist _ q _)).
    cbn. Unshelve. 2: { cbn. split; auto. }
    unfold query_int. unfold int at 2.
    rewrite !Sup.mor. apply sup_iff.
    intros [rc|].
    - setoid_rewrite FCD.ext_ana. cbn.
      rewrite Sup.mor_join. apply join_lub.
      + setoid_rewrite FCD.ext_ana. cbn.
        apply (sup_at None). reflexivity.
      + rewrite !Sup.mor. apply sup_iff. intros [n [? ?]]. cbn.
        setoid_rewrite FCD.ext_ana.
        setoid_rewrite FCD.ext_ana. cbn.
        apply join_lub.
        * apply (sup_at None). reflexivity.
        * rewrite !Inf.mor.
          eapply (inf_at (exist _ (cr_retval rc) _)).
          cbn. Unshelve. 2: cbn; split; auto.
          setoid_rewrite FCD.ext_ana. cbn.
          setoid_rewrite FCD.ext_ana.
          apply (sup_at (Some rc)).
          destruct rc. cbn. reflexivity.
    - fcd. apply (sup_at None). reflexivity.
  Qed.

  Lemma rb_eta: identity [= rb_right @ rb_left.
  Proof.
  Admitted.

  Program Definition rb_adj: rb_sig <~> li_c :=
    {|
      left_arrow := rb_left;
      right_arrow := rb_right;
      epsilon := rb_epsilon;
      eta := rb_eta;
    |}.

  Definition bq_left: bq_sig ~> li_c :=
    fun _ '(li_sig q) =>
      sup ar, sup { m | bq_rel ar m q /\ args_type_check (cq_args q) (cq_sg q)} ,
      n <- int m;
      inf { r | val_rel ar n r /\ retval_type_check r (cq_sg q) },
      ret (cr r).
  Definition bq_right: li_c ~> bq_sig :=
    fun _ m =>
      inf { q | bq_rel _ m q /\ args_type_check (cq_args q) (cq_sg q)},
      r <- query_int q;
      sup { n | val_rel _ n (cr_retval r) /\
                  retval_type_check (cr_retval r) (cq_sg q) },
      ret n.
  Program Definition bq_adj: bq_sig <~> li_c :=
    {|
      left_arrow := bq_left;
      right_arrow := bq_right;
    |}.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.

End MARSHALL.

Notation li_cmem := LanguageInterface.li_c.
Notation cqmem := LanguageInterface.cq.
Notation crmem := LanguageInterface.cr.

Require Import compcertox.Lifting.
Require Import Effects.
(** ** Correctness  *)
Section CORRECT.

  Context (se:Genv.symtbl).

  Definition umem: li_c ~> li_cmem :=
    fun _ '(li_sig q) =>
      match q with
      | cqmem vf sg args m =>
        r <- query_int (cq vf sg args);
        match r with
        | cr retval => ret (crmem retval m)
        end
      end.

  Definition iota {S}: sig li_cmem # S ~> sig li_c # (mem * S) :=
    fun _ '(st q (m, s)) =>
      match q with
      | li_sig (cq vf sg args) =>
          rs <- int (st (li_sig (cqmem vf sg args m)) s);
          match rs with
          | (crmem retval m', s') => ret (cr retval, (m', s'))
          end
      end.

  Close Scope Z_scope.
  (* L2 is the overlay *)
  Record certi_layer {E1 E2 S1 S2} :=
    {
      L1: 0 ~> E1 # S1;
      L1_adj: E1 <~> li_c;
      L2: 0 ~> E2 # S2;
      L2_adj: E2 <~> li_c;
      module: list Clight.program;
      sk: AST.program unit unit;
      abs_rel: S2 -> mem * S1 -> Prop;

      layer_ref:
      L2 [= right_arrow (lift_adjunction L2_adj abs_rel)
         @ iota
         @ slift (ang_lts_spec (CModule.semantics module sk se))
         @ slift (umem @ left_arrow L1_adj)
         @ L1;
    }.

  Hypothesis se_valid: Genv.valid_for (erase_program bq_program) se.

  Lemma inc2_block:
    exists b, Genv.find_symbol (globalenv ((semantics2 bq_program) se)) inc2_id = Some b
         /\ Genv.find_def (globalenv ((semantics2 bq_program) se)) b = Some (Gfun inc2_ext).
  Proof. apply Genv.find_def_symbol; eauto. Qed.

  Lemma set_block:
    exists b, Genv.find_symbol (globalenv ((semantics2 bq_program) se)) set_id = Some b
         /\ Genv.find_def (globalenv ((semantics2 bq_program) se)) b = Some (Gfun set_ext).
  Proof. apply Genv.find_def_symbol; eauto. Qed.

  Instance srun_morphism {E S A} (k: S):
    CDL.Morphism (@srun E S A k).
  Proof.
    unfold srun. split.
    - intros x y. apply Sup.mor.
    - intros x y. apply Inf.mor.
  Qed.

  Hypothesis Nneq0: CAL.N <> 0%nat.

  Lemma enq_helper f c1 n v:
    c1 < CAL.N -> n < CAL.N ->
    slice (update f ((c1 + n) mod CAL.N) v) c1 (S n) = slice f c1 n ++ [v].
  Proof. Admitted.

  Program Definition bq: @certi_layer rb_sig bq_sig rb_state bq_state :=
    {|
      L1 := L_rb;
      L1_adj := rb_adj se;
      L2 := L_bq;
      L2_adj := bq_adj se;
      module := [bq_program];
      sk := erase_program bq_program;
      abs_rel bq '(m, rb) := rb_bq rb bq /\ Ple (Genv.genv_next se) (Mem.nextblock m);
    |}.
  Next Obligation.
    replace (CModule.semantics [bq_program] (erase_program bq_program))
      with (Clight.semantics2 bq_program) by admit.
    intros ? [? m bq]. destruct m.
    (* enq *)
    Local Opaque semantics2.
    - edestruct inc2_block as (inc2b & Hb1 & Hb2).
      edestruct set_block as (setb & Hb3 & Hb4).
      setoid_rewrite Sup.mor. apply sup_iff. intros bq_len.
      setoid_rewrite FCD.ext_ana. cbn.
      unfold bq_adj, right_arr. cbn.
      rewrite !compose_assoc.
      unfold compose at 1. cbn.
      unfold bq_right. unfold finf.
      rewrite !Inf.mor. apply inf_iff. intros [q [Hbqr Hbqt]]. cbn.
      unfold query_int.
      rewrite srun_bind. rewrite srun_int.
      rewrite apply_bind. rewrite apply_int_r.
      unfold compose at 6. cbn.
      setoid_rewrite Inf.mor. setoid_rewrite Inf.mor.
      apply inf_iff. intros [[m rb] [Hr Hm]]. cbn.
      rewrite apply_bind. rewrite apply_int_r.
      unfold compose at 10. unfold iota at 3.
      destruct q as [vf sg args]. cbn.
      rewrite apply_bind. rewrite apply_int_r.
      unfold compose at 13. cbn.
      match goal with
      | |- context[ bind ?f (bind ?g (bind ?h _)) ] =>
          set (f1 := f);
          set (f2 := g);
          set (f3 := h)
      end.
      setoid_rewrite sup_sup.
      do 5 rewrite Sup.mor.
      eapply (sup_at (exist _ (Callstate vf args Kstop m) _)). cbn. Unshelve.
      2: {
        cbn. inv Hbqr. unfold enq_sg. econstructor.
        - unfold Genv.find_funct.
          destruct Integers.Ptrofs.eq_dec; try congruence.
          unfold Genv.find_funct_ptr.
          apply Genv.find_invert_symbol in H4.
          unfold Clight.globalenv. cbn.
          rewrite Genv.find_def_spec. rewrite H4.
          cbn. reflexivity.
        - reflexivity.
        - constructor.
          (* the type of the enq argument *)
          + admit.
          + constructor.
        - cbn. assumption.
      }

      rewrite lts_spec_step.
      rewrite !Sup.mor_join. apply join_l. apply join_l.
      unfold fsup. do 5 rewrite Sup.mor. inv Hbqr.
      eapply (sup_at (exist _ _ _)). cbn.
      Unshelve.
      3: {
        cbn. eapply star_left with (t1 := E0) (t2 := E0). 3: reflexivity.
        {
          constructor. instantiate (1 := bq_enq).
          - unfold Genv.find_funct.
            destruct Integers.Ptrofs.eq_dec; try congruence.
            unfold Genv.find_funct_ptr.
            apply Genv.find_invert_symbol in H4.
            unfold Clight.globalenv. cbn.
            Local Transparent semantics2.
            cbn. rewrite Genv.find_def_spec. rewrite H4.
            cbn. reflexivity.
          - constructor; cbn; try constructor.
            + unfold In. easy.
            + constructor.
            (* because we are using semantics2
               enq_arg_id ≠ bq_enq_tmp *)
            + intros x y Hx Hy. inv Hx; inv Hy; easy.
        }
        eapply star_left with (t1 := E0) (t2 := E0). 3: reflexivity.
        {
          unfold bq_enq at 2. cbn.
          unfold bq_enq_body. constructor.
        }
        eapply star_left with (t1 := E0) (t2 := E0). 3: reflexivity.
        {
          econstructor.
          - cbn. reflexivity.
          - econstructor.
            + eapply eval_Evar_global.
              * reflexivity.
              * apply Hb1.
            + eapply deref_loc_reference. reflexivity.
          - constructor.
          - unfold Genv.find_funct.
            destruct Integers.Ptrofs.eq_dec; try congruence.
            unfold Genv.find_funct_ptr. rewrite Hb2. reflexivity.
          - cbn. reflexivity.
        }
        apply star_refl.
      }

      rewrite lts_spec_step.
      rewrite !Sup.mor_join. apply join_l. apply join_r.
      unfold fsup. rewrite !Sup.mor.
      eapply (sup_at (exist _ _ _)).
      cbn. Unshelve.
      3: {
        cbn. econstructor.
        unfold Genv.find_funct.
        destruct Integers.Ptrofs.eq_dec; try congruence.
        unfold Genv.find_funct_ptr.
        Local Transparent semantics2. cbn in Hb2 |- *.
        rewrite Hb2. reflexivity.
      }
      Local Opaque semantics2.
      unfold query_int.
      rewrite srun_bind. rewrite srun_int.
      rewrite apply_bind. rewrite apply_int_r.
      unfold compose at 3. cbn.
      unfold compose at 3. cbn.
      unfold query_int.
      rewrite apply_bind. rewrite apply_int_r. cbn.
      rewrite !Sup.mor. eapply (sup_at _).
      unfold fsup. rewrite !Sup.mor.
      eapply (sup_at (exist _ inc2 _)). cbn. Unshelve.
      2: {
        cbn. split.
        - constructor. apply Hb1.
        - econstructor. constructor. reflexivity.
      }
      rewrite srun_bind. rewrite apply_bind.
      rewrite srun_bind. rewrite apply_bind.
      rewrite srun_int. rewrite apply_int_r. cbn.
      rewrite !bind_bind. inv Hr. cbn.
      rewrite bind_ret_r. unfold finf.
      rewrite !Inf.mor. apply inf_iff.
      intros [rval [Hrval Hrty]]. cbn.
      repeat (setoid_rewrite FCD.ext_ana; cbn).
      rewrite !Sup.mor.
      eapply (sup_at (exist _ _ _)). cbn. Unshelve.
      3: { cbn. econstructor. }

      rewrite lts_spec_step.
      rewrite !Sup.mor_join. apply join_l. apply join_l.
      unfold fsup. rewrite !Sup.mor.
      eapply (sup_at (exist _ _ _)). cbn. Unshelve.
      3: {
        cbn.
        eapply star_left with (t1 := E0) (t2 := E0). 3: reflexivity.
        { constructor. }
        eapply star_left with (t1 := E0) (t2 := E0). 3: reflexivity.
        { constructor. }
        eapply star_left with (t1 := E0) (t2 := E0). 3: reflexivity.
        { constructor. }
        eapply star_left with (t1 := E0) (t2 := E0). 3: reflexivity.
        {
          econstructor.
          - cbn. reflexivity.
          - econstructor.
            + eapply eval_Evar_global.
              * reflexivity.
              * apply Hb3.
            + eapply deref_loc_reference. reflexivity.
          - econstructor.
            + constructor. reflexivity.
            + cbn. inv Hrval.
              (* type *)
              * exfalso. admit.
              * depsubst. reflexivity.
              * admit.
            + econstructor.
              * constructor. reflexivity.
              * cbn. instantiate (1 := arg).
                (* Type of enq argument *)
                admit.
              * constructor.
          - unfold Genv.find_funct.
            destruct Integers.Ptrofs.eq_dec; try congruence.
            unfold Genv.find_funct_ptr.
            Local Transparent semantics2. cbn in Hb4 |- *.
            rewrite Hb4. reflexivity.
          - cbn. reflexivity.
        }
        apply star_refl.
      }

      rewrite lts_spec_step.
      rewrite !Sup.mor_join. apply join_l. apply join_r.
      unfold fsup. rewrite !Sup.mor.
      eapply (sup_at (exist _ _ _)). cbn. Unshelve.
      3: {
        cbn. econstructor.
        unfold Genv.find_funct.
        destruct Integers.Ptrofs.eq_dec; try congruence.
        unfold Genv.find_funct_ptr.
        Local Transparent semantics2. cbn in Hb4 |- *.
        rewrite Hb4. reflexivity.
      }
      Local Opaque semantics2.
      unfold query_int.
      rewrite srun_bind. rewrite srun_int.
      rewrite apply_bind. rewrite apply_int_r.
      unfold compose at 3. cbn.
      unfold compose at 3. cbn.
      unfold query_int.
      rewrite apply_bind. rewrite apply_int_r. cbn.
      rewrite !Sup.mor. eapply sup_at.
      unfold fsup. rewrite !Sup.mor.
      inv Hrval. 1, 3: admit. depsubst.
      eapply (sup_at (exist _ (set ((c1 + n) mod CAL.N) v) _)). cbn. Unshelve.
      2: {
        cbn. split.
        - constructor; auto.
          constructor. auto.
        - unfold set_sg. econstructor.
          2: reflexivity. constructor.
          constructor. reflexivity.
          constructor. 2: constructor.
          (* type of the enq argument *)
          admit.
      }
      intm. apply assert_r.
      2: { apply Nat.mod_upper_bound. auto. }
      unfold finf. rewrite !Inf.mor.
      apply inf_iff. intros [retv [Hr Htyr]]. cbn.
      repeat (setoid_rewrite FCD.ext_ana; cbn).
      rewrite !Sup.mor. eapply (sup_at (exist _ _ _)).
      cbn. Unshelve.
      3: { cbn. constructor. }

      rewrite lts_spec_step. rewrite !Sup.mor_join.
      apply join_l. apply join_l.
      unfold fsup. rewrite !Sup.mor. eapply (sup_at (exist _ _ _)).
      cbn. Unshelve.
      3: {
        cbn.
        eapply star_left with (t1 := E0) (t2 := E0). 3: reflexivity.
        { constructor. }
        eapply star_left with (t1 := E0) (t2 := E0). 3: reflexivity.
        { constructor. }
        eapply star_left with (t1 := E0) (t2 := E0). 3: reflexivity.
        { constructor. reflexivity. }
        apply star_refl.
      }

      rewrite lts_spec_step. rewrite !Sup.mor_join. apply join_r.
      unfold fsup. rewrite !Sup.mor. eapply (sup_at (exist _ _ _)).
      cbn. Unshelve.
      3: { cbn. constructor. }
      setoid_rewrite FCD.ext_ana. cbn.
      setoid_rewrite FCD.ext_ana. cbn.
      setoid_rewrite FCD.ext_ana. cbn.
      subst f3. cbn. setoid_rewrite FCD.ext_ana. cbn.
      setoid_rewrite FCD.ext_ana. cbn.
      subst f2. cbn.
      unfold fsup. rewrite !Sup.mor. eapply (sup_at (exist _ _ _)).
      cbn. Unshelve.
      3: {
        cbn. split; auto. apply bq_rb_intro with (n := S n); auto.
        - rewrite slice_length in bq_len.
          apply Nat.le_succ_l. auto.
        - change (S ?x) with (1 + x).
          rewrite Nat.add_mod_idemp_r by auto. f_equal.
          induction c1; cbn in *; auto.
      }
      setoid_rewrite FCD.ext_ana. cbn.
      setoid_rewrite FCD.ext_ana. cbn.
      subst f1. cbn.
      unfold fsup. rewrite !Sup.mor.
      eapply (sup_at (exist _ tt _)).
      cbn. Unshelve.
      2: {
        cbn. split.
        - apply unit_val.
        - unfold enq_sg. econstructor; cbn.
          + instantiate (1 := Tvoid). constructor.
          + reflexivity.
      }
      setoid_rewrite FCD.ext_ana. cbn.
      setoid_rewrite FCD.ext_ana. cbn.
      unfold ret. rstep. cbn.
      replace (slice f c1 n ++ [v])
        with (slice (update f ((c1 + n) mod CAL.N) v) c1 (S n)).
      constructor. apply enq_helper; auto.
      rewrite slice_length in bq_len; auto.
    - admit.
  Admitted.

  Definition empty_adj_left {E}: 0 ~> E := bot.

  Definition empty_adj_right {E}: E ~> 0 := top.

  Lemma empty_adj_epsilon {E}:
    (@empty_adj_left E) @ (@empty_adj_right E) [= identity.
  Proof.
    unfold empty_adj_left, empty_adj_right, compose, identity.
    intros ? m. unfold apply.
    Local Transparent bot. unfold bot. cbn.
    fcd. apply sup_iff. intros [].
  Qed.

  Lemma empty_adj_eta {E}:
    identity [= (@empty_adj_right E) @ (@empty_adj_left E).
  Proof.
    unfold empty_adj_left, empty_adj_right, compose, identity.
    intros ? m. unfold apply.
    Local Transparent top. unfold top. cbn.
    fcd. apply inf_iff. intros [].
  Qed.

  Definition empty_adj {E}: 0 <~> E :=
    {|
      left_arrow := empty_adj_left;
      right_arrow := empty_adj_right;
      epsilon := empty_adj_epsilon;
      eta := empty_adj_eta;
    |}.

  Program Definition rb: @certi_layer 0 rb_sig unit rb_state :=
    {|
      L1 := bot;
      L1_adj := empty_adj;
      L2 := L_rb;
      L2_adj := rb_adj se;
      module := [rb_program];
      sk := erase_program rb_program;
      abs_rel rb '(m, tt) := Ple (Genv.genv_next se) (Mem.nextblock m);
    |}.
  Next Obligation.
  Admitted.

End CORRECT.
