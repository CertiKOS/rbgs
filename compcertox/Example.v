From Coq Require Import List.
From compcert Require Import
     Integers Coqlib Maps
     Memory AST Values
     Clight Ctypes
     LanguageInterface
     Events Globalenvs
     Smallstep.
From compcertox Require Import
  Lifting Encapsulation
  ClightP ClightPComp.
Import ListNotations.

(** identifies for the functions *)
Definition set_id: positive := 101.
Definition get_id: positive := 102.
Definition inc1_id: positive := 103.
Definition inc2_id: positive := 104.
Definition enq_id: positive := 105.
Definition deq_id: positive := 106.
(** identifiers for the global variables *)
Definition arr_id: positive := 1.
Definition cnt1_id: positive := 2.
Definition cnt2_id: positive := 3.
(** identifiers for the arguments  *)
Definition get_arg_id: positive := 1.
Definition set_arg1_id: positive := 1.
Definition set_arg2_id: positive := 2.
Definition enq_arg_id: positive := 1.
(** identifiers for the temps *)
Definition rb_inc1_tmp : positive := 1.
Definition rb_inc2_tmp : positive := 1.
Definition bq_enq_tmp : positive := 2.
Definition bq_deq_tmp1 : positive := 1.
Definition bq_deq_tmp2 : positive := 2.

Notation tint := (Tint I32 Unsigned noattr).
Notation tarray := (fun ty size => Tarray ty size noattr).
Notation tptr := (fun ty => Tpointer ty noattr).
Notation tvoid := (Tvoid).

Definition N := 100%nat.
Definition Nz: Z := Z.of_nat N.

Import ClightP.

Section CLIGHTP.

  Definition inc1_sg: signature :=
    signature_of_type Tnil tint cc_default.
  Definition inc2_sg: signature :=
    signature_of_type Tnil tint cc_default.
  Definition get_sg: signature :=
    signature_of_type (Tcons tint Tnil) tint cc_default.
  Definition set_sg: signature :=
    signature_of_type (Tcons tint (Tcons tint Tnil)) tvoid cc_default.
  Definition enq_sg: signature :=
    signature_of_type (Tcons tint Tnil) tvoid cc_default.
  Definition deq_sg: signature :=
    signature_of_type Tnil tint cc_default.

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
         (Eaccess (Epvar arr_id (tarray tint Nz))
            (Etempvar get_arg_id tint) tint)).
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
    Ssequence
      (Sassign
         (Eaccess (Epvar arr_id (tarray tint Nz))
            (Etempvar get_arg_id tint) tint)
         (Etempvar set_arg2_id tint))
      (Sreturn None).
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
      int i = cnt1;
      cnt1 += 1;
      cnt1 %= N;
      return i;
    }
>>
   *)
  Definition rb_inc1_body : statement :=
    Ssequence
      (Ssequence
         (Ssequence
            (Sset rb_inc1_tmp (Epvar cnt1_id tint))
            (Sassign
               (Epvar cnt1_id tint)
               (Ebinop Cop.Oadd
                       (Epvar cnt1_id tint)
                       (Econst_int (Int.repr 1) tint)
                       tint)))
         (Sassign
            (Epvar cnt1_id tint)
            (Ebinop Cop.Omod
                    (Epvar cnt1_id tint)
                    (Econst_int (Int.repr Nz) tint)
                    tint)))
      (Sreturn (Some (Etempvar rb_inc1_tmp tint))).
  Definition rb_inc1 : function :=
    {|
      fn_return := tint;
      fn_callconv := cc_default;
      fn_params := [];
      fn_vars := [];
      fn_temps := [ (rb_inc1_tmp, tint) ];
      fn_body := rb_inc1_body;
    |}.

  (**
<<
    int inc2() {
      int i = cnt1;
      cnt1 += 1;
      cnt1 %= N;
      return i;
    }
>>
  *)
  Definition rb_inc2_body : statement :=
    Ssequence
      (Ssequence
         (Ssequence
            (Sset rb_inc2_tmp (Epvar cnt2_id tint))
            (Sassign
               (Epvar cnt2_id tint)
               (Ebinop Cop.Oadd
                       (Epvar cnt2_id tint)
                       (Econst_int (Int.repr 1) tint)
                       tint)))
         (Sassign
            (Epvar cnt2_id tint)
            (Ebinop Cop.Omod
                    (Epvar cnt2_id tint)
                    (Econst_int (Int.repr Nz) tint)
                    tint)))
      (Sreturn (Some (Etempvar rb_inc2_tmp tint))).
  Definition rb_inc2 : function :=
    {|
      fn_return := tint;
      fn_callconv := cc_default;
      fn_params := [];
      fn_vars := [];
      fn_temps := [ (rb_inc2_tmp, tint) ];
      fn_body := rb_inc2_body;
    |}.


  Definition arr_pvar : privvar type :=
    let tarr := tarray tint Nz in
    {|
      pvar_info := tarr;
      pvar_init := Array Nz (ZMap.init (Val (Vint Int.zero) tint)) tarr;
    |}.
  Definition cnt_pvar : privvar type :=
    {|
      pvar_info := tint;
      pvar_init := Val (Vint Int.zero) tint;
    |}.

  Program Definition rb_program: ClightP.program :=
    {|
      prog_defs := [(get_id, Gfun (Internal rb_get));
        (set_id, Gfun (Internal rb_set));
        (inc1_id, Gfun (Internal rb_inc1));
        (inc2_id, Gfun (Internal rb_inc2))];
      prog_private := [(arr_id, arr_pvar);
        (cnt1_id, cnt_pvar);
        (cnt2_id, cnt_pvar)];
      prog_public := [get_id; set_id; inc1_id; inc2_id];
      prog_main := 999%positive;
      prog_types := [];
      prog_comp_env := (PTree.empty _);
    |}.

  (**
<<
    void enq(int v) {
      int i = inc2();
      set(i, v);
    }
>>
   *)
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
  Definition bq_deq_body : statement :=
    Ssequence
      (Scall (Some bq_deq_tmp1) (Evar inc1_id (Tfunction Tnil tint cc_default)) nil)
      (Ssequence
         (Scall (Some bq_deq_tmp2) (Evar get_id (Tfunction (Tcons tint Tnil) tint cc_default))
                ([Etempvar bq_deq_tmp1 tint]))
         (Sreturn (Some (Etempvar bq_deq_tmp2 tint)))).
  Definition bq_deq : function :=
    {|
      fn_return := tint;
      fn_callconv := cc_default;
      fn_params := [];
      fn_vars := [];
      fn_temps := [(bq_deq_tmp1, tint); (bq_deq_tmp2, tint)];
      fn_body := bq_deq_body;
    |}.

  Definition inc1_ext: fundef :=
    External (EF_external "inc1" inc1_sg) Tnil tint cc_default.
  Definition inc2_ext: fundef :=
    External (EF_external "inc2" inc2_sg) Tnil tint cc_default.
  Definition get_ext: fundef :=
    External (EF_external "get" get_sg) (Tcons tint Tnil) tint cc_default.
  Definition set_ext: fundef :=
    External (EF_external "set" set_sg) (Tcons tint (Tcons tint Tnil)) tvoid cc_default.

  Program Definition bq_program : ClightP.program :=
    {|
      prog_defs := [(enq_id, Gfun (Internal bq_enq));
                    (deq_id, Gfun (Internal bq_deq));
                    (inc1_id, Gfun inc1_ext);
                    (inc2_id, Gfun inc2_ext);
                    (get_id, Gfun get_ext);
                    (set_id, Gfun set_ext)];
      prog_private := [];
      prog_public := [enq_id; deq_id];
      prog_main := 999%positive;
      prog_types := [];
      prog_comp_env := (PTree.empty _);
    |}.

End CLIGHTP.

(** ------------------------------------------------------------------------- *)
(** Ring Buffer Spec *)

Definition rb_state : Type := (nat -> Values.val) * nat * nat.

Inductive rb_sig := inc1 | inc2 | geti | seti.

Inductive rb_internal_state: Type :=
| rb_init: forall (sig: rb_sig) (s: rb_state) (vs: list Values.val) (m: mem), rb_internal_state
| rb_final: forall (s: rb_state) (v: Values.val) (m: mem), rb_internal_state.

Section RB_LTS.

  Variable ge:  genv.

  Inductive rb_initial_state: c_query * rb_state -> rb_internal_state -> Prop :=
  | initial_state_inc1: forall vf b m rbst sig,
      vf = Vptr b Integers.Ptrofs.zero ->
      Genv.find_symbol ge inc1_id = Some b ->
      Ple (Genv.genv_next ge) (Mem.nextblock m) ->
      sig = inc1_sg ->
      rb_initial_state (cq vf sig nil m, rbst) (rb_init inc1 rbst nil m)
  | initial_state_inc2: forall vf b m rbst sig,
      vf = Vptr b Integers.Ptrofs.zero ->
      Genv.find_symbol ge inc2_id = Some b ->
      Ple (Genv.genv_next ge) (Mem.nextblock m) ->
      sig = inc2_sg ->
      rb_initial_state (cq vf sig nil m, rbst) (rb_init inc2 rbst nil m)
  | initial_state_geti: forall vf b v m rbst sig,
      vf = Vptr b Integers.Ptrofs.zero ->
      Genv.find_symbol ge get_id = Some b ->
      Ple (Genv.genv_next ge) (Mem.nextblock m) ->
      Cop.val_casted v tint ->
      sig = get_sg ->
      rb_initial_state (cq vf sig [v] m, rbst) (rb_init geti rbst [v] m)
  | initial_state_seti: forall vf b m rbst sig vargs v1 v2,
      vf = Vptr b Integers.Ptrofs.zero ->
      Genv.find_symbol ge set_id = Some b ->
      Ple (Genv.genv_next ge) (Mem.nextblock m) ->
      sig = set_sg ->
      vargs = [ v1; v2 ] ->
      Cop.val_casted v1 tint ->
      Cop.val_casted v2 tint ->
      rb_initial_state (cq vf sig vargs m, rbst) (rb_init seti rbst vargs m).

  Inductive rb_final_state: rb_internal_state -> c_reply * rb_state -> Prop :=
  | rb_final_state_intro: forall rv m rbst,
      rb_final_state (rb_final rbst rv m) (cr rv m, rbst).

  Inductive rb_step: rb_internal_state -> trace -> rb_internal_state -> Prop :=
  | inc1_step:
    forall f c1 c2 m v,
      v = Vint (Integers.Int.repr (Z.of_nat c1)) ->
      rb_step (rb_init inc1 (f, c1, c2) nil m) E0 (rb_final (f, (S c1 mod N)%nat, c2) v m)
  | inc2_step:
    forall f c1 c2 m v,
      v = Vint (Integers.Int.repr (Z.of_nat c2)) ->
      rb_step (rb_init inc2 (f, c1, c2) nil m) E0 (rb_final (f, c1, (S c2 mod N)%nat) v m)
  | get_step:
    forall f c1 c2 m v i,
      v = Vint (Integers.Int.repr (Z.of_nat i)) ->
      (i < N)%nat ->
      rb_step (rb_init geti (f, c1, c2) [v] m) E0 (rb_final (f, c1, c2) (f i) m)
  | set_step:
    forall f c1 c2 m v1 v2 i,
      v1 = Vint (Integers.Int.repr (Z.of_nat i)) ->
      (i < N)%nat ->
      Cop.val_casted v2 tint ->
      rb_step (rb_init seti (f, c1, c2) [v1; v2] m) E0
        (rb_final ((fun j => if Nat.eq_dec i j then v2 else f j), c1, c2)
                  Vundef m).

  Program Definition rb_lts: lts li_c (li_c@rb_state) rb_internal_state :=
    {|
      Smallstep.genvtype := genv;
      Smallstep.step ge := rb_step;
      Smallstep.initial_state := rb_initial_state;
      Smallstep.at_external _ _ := False;
      Smallstep.after_external _ _ _ := False;
      Smallstep.final_state := rb_final_state;
      Smallstep.globalenv := ge;
    |}.

End RB_LTS.

Definition rb_spec: semantics li_c (li_c@rb_state) :=
  {|
    skel := AST.erase_program rb_program;
    activate se := rb_lts (ClightP.globalenv se rb_program);
    footprint := AST.footprint_of_program rb_program;
  |}.

Instance rb_state_pset : PSet rb_state. Admitted.

Program Definition rb_espec : li_c +-> li_c :=
  comp_esem'
    (encap_prim rb_state)
    (semantics_embed rb_spec)
    (skel rb_spec).

Lemma rb_correct: E.forward_simulation (&1) (&1) rb_espec (eclightp rb_program).
Admitted.

(** ------------------------------------------------------------------------- *)
(** Bounded Queue Spec *)

Inductive bq_sig := enq | deq.

Inductive bq_internal_state: Type :=
| bq_init: forall (sig: bq_sig) (vs: list Values.val) (m: mem), bq_internal_state
| bq_call: forall (sig: rb_sig) (vs: list Values.val) (m: mem), bq_internal_state
| bq_middle: forall (sig: bq_sig) (vs: list Values.val) (m: mem), bq_internal_state
| bq_middlex: forall (sig: bq_sig) (vs: Values.val) (m: mem), bq_internal_state
| bq_final: forall (v: Values.val) (m: mem), bq_internal_state.

Section RB_LTS.

  Variable ge:  genv.

  Inductive bq_initial_state: c_query -> bq_internal_state -> Prop :=
  | initial_state_enq: forall vf b v m  sig,
      vf = Vptr b Integers.Ptrofs.zero ->
      Genv.find_symbol ge enq_id = Some b ->
      Ple (Genv.genv_next ge) (Mem.nextblock m) ->
      Cop.val_casted v tint ->
      sig = enq_sg ->
      bq_initial_state (cq vf sig [v] m) (bq_init enq [v] m)
  | initial_state_deq: forall vf b m  sig,
      vf = Vptr b Integers.Ptrofs.zero ->
      Genv.find_symbol ge deq_id = Some b ->
      Ple (Genv.genv_next ge) (Mem.nextblock m) ->
      sig = deq_sg ->
      bq_initial_state (cq vf sig nil m) (bq_init deq  nil m).

  Inductive bq_final_state: bq_internal_state -> c_reply -> Prop :=
  | bq_final_state_intro: forall rv m,
      bq_final_state (bq_final rv m) (cr rv m).

  Inductive bq_step: bq_internal_state -> trace -> bq_internal_state -> Prop :=
  | enq_step1 v m:
      bq_step (bq_init enq [v] m) E0 (bq_call inc2 [v] m)
  | enq_step2 v1 v2 m:
      bq_step (bq_middle enq [v1; v2] m) E0 (bq_call seti [v1; v2] m)
  | enq_step3 vs m:
      bq_step (bq_middlex enq vs m) E0 (bq_final Vundef m)
  | deq_step1 m:
      bq_step (bq_init deq [] m) E0 (bq_call inc1 [] m)
  | deq_step2 v m:
      bq_step (bq_middle deq [v] m) E0 (bq_call geti [v] m)
  | deq_step3 v m:
      bq_step (bq_middlex deq v m) E0 (bq_final v m).

  Inductive bq_at_external: bq_internal_state -> c_query -> Prop :=
  | bq_ext_inc1 vf sig vs m b:
    vf = Vptr b Integers.Ptrofs.zero ->
    Genv.find_symbol ge inc1_id = Some b ->
    sig = inc1_sg ->
    bq_at_external (bq_call inc1 vs m) (cq vf sig nil m)
  | bq_ext_inc2 vf sig vs m b:
    vf = Vptr b Integers.Ptrofs.zero ->
    Genv.find_symbol ge inc2_id = Some b ->
    sig = inc2_sg ->
    bq_at_external (bq_call inc2 vs m) (cq vf sig nil m)
  | bq_ext_get vf sig v m b:
    vf = Vptr b Integers.Ptrofs.zero ->
    Genv.find_symbol ge get_id = Some b ->
    sig = get_sg ->
    bq_at_external (bq_call geti [v] m) (cq vf sig [v] m)
  | bq_ext_set vf sig vs m b:
    vf = Vptr b Integers.Ptrofs.zero ->
    Genv.find_symbol ge set_id = Some b ->
    sig = set_sg ->
    bq_at_external (bq_call seti vs m) (cq vf sig vs m).

  Inductive bq_after_external: bq_internal_state -> c_reply -> bq_internal_state -> Prop :=
  | bq_aft_inc1 rv m :
    Cop.val_casted rv tint ->
    bq_after_external (bq_call inc1 nil m) (cr rv m) (bq_middle deq [rv] m)
  | bq_aft_inc2 rv v m :
    Cop.val_casted rv tint ->
    bq_after_external (bq_call inc2 [v] m) (cr rv m) (bq_middle enq [rv; v] m)
  | bq_aft_get rv vs m :
    Cop.val_casted rv tint ->
    bq_after_external (bq_call geti vs m) (cr rv m) (bq_middlex deq rv m)
  | bq_aft_set vs m :
    bq_after_external (bq_call seti vs m) (cr Vundef m) (bq_middlex enq Vundef m).

  Program Definition bq_lts: lts li_c li_c bq_internal_state :=
    {|
      Smallstep.genvtype := genv;
      Smallstep.step ge := bq_step;
      Smallstep.initial_state := bq_initial_state;
      Smallstep.at_external := bq_at_external;
      Smallstep.after_external := bq_after_external;
      Smallstep.final_state := bq_final_state;
      Smallstep.globalenv := ge;
    |}.

End RB_LTS.

Definition bq_spec: semantics li_c li_c :=
  {|
    skel := AST.erase_program bq_program;
    activate se := bq_lts (ClightP.globalenv se bq_program);
    footprint := AST.footprint_of_program bq_program;
  |}.

Definition bq_espec: li_c +-> li_c := semantics_embed bq_spec.

Lemma bq_correct: E.forward_simulation (&1) (&1) bq_espec (eclightp bq_program).
Admitted.

(** ------------------------------------------------------------------------- *)
(** Abstract Ring Buffer Spec *)

Definition bq_state : Type := list Values.val.

Inductive bq_abs_state: Type :=
| bq_abs_init: forall (sig: bq_sig) (s: bq_state) (vs: list Values.val) (m: mem), bq_abs_state
| bq_abs_final: forall (s: bq_state) (v: Values.val) (m: mem), bq_abs_state.

Section BQ_LTS.

  Variable ge:  genv.

  Inductive bq_abs_initial_state: c_query * bq_state -> bq_abs_state -> Prop :=
  | abs_initial_state_enq: forall vf b v m bqst sig,
      vf = Vptr b Integers.Ptrofs.zero ->
      Genv.find_symbol ge enq_id = Some b ->
      Ple (Genv.genv_next ge) (Mem.nextblock m) ->
      Cop.val_casted v tint ->
      sig = enq_sg ->
      bq_abs_initial_state (cq vf sig [v] m, bqst) (bq_abs_init enq bqst [v] m)
  | abs_initial_state_deq: forall vf b m bqst sig,
      vf = Vptr b Integers.Ptrofs.zero ->
      Genv.find_symbol ge deq_id = Some b ->
      Ple (Genv.genv_next ge) (Mem.nextblock m) ->
      sig = deq_sg ->
      bq_abs_initial_state (cq vf sig nil m, bqst) (bq_abs_init deq bqst nil m).

  Inductive bq_abs_final_state: bq_abs_state -> c_reply * bq_state -> Prop :=
  | bq_abs_final_state_intro: forall rv m bqst,
      bq_abs_final_state (bq_abs_final bqst rv m) (cr rv m, bqst).

  Inductive bq_abs_step: bq_abs_state -> trace -> bq_abs_state -> Prop :=
  | enq_step:
    forall m vs v,
      (List.length vs < N)%nat ->
      bq_abs_step (bq_abs_init enq vs [v] m) E0 (bq_abs_final (vs++[v]) Vundef m)
  | deq_step:
    forall m vs v,
      bq_abs_step (bq_abs_init deq (v::vs) [] m) E0 (bq_abs_final vs v m).

  Program Definition abs_bq_lts: lts li_c (li_c@bq_state) bq_abs_state :=
    {|
      Smallstep.genvtype := genv;
      Smallstep.step ge := bq_abs_step;
      Smallstep.initial_state := bq_abs_initial_state;
      Smallstep.at_external _ _ := False;
      Smallstep.after_external _ _ _ := False;
      Smallstep.final_state := bq_abs_final_state;
      Smallstep.globalenv := ge;
    |}.

End BQ_LTS.

Section REFINE.

  Instance clightp_linker: Linking.Linker program.
  Admitted.

  (* I messed up the notations. I guess it's because my improper use of & *)
  Hypothesis rb_bq_linking:
    sigT (fun cprog => Linking.link bq_program rb_program = Some cprog).
  (* { cprog  & Linking.link bq_program rb_program = Some cprog }. *)

  Definition rb_bq_prog := projT1 rb_bq_linking.
  Definition rb_bq_skel := AST.erase_program rb_bq_prog.

  Definition abs_bq_spec: semantics li_c (li_c@bq_state) :=
    {|
      skel := AST.erase_program rb_bq_prog;
      activate se := abs_bq_lts (ClightP.globalenv se rb_bq_prog);
      footprint := fun i => footprint_of_program bq_program i
                         \/ footprint_of_program rb_program i;
    |}.

  Instance bq_state_pset : PSet bq_state. Admitted.

  Definition abs_bq_espec : li_c +-> li_c :=
    comp_esem'
      (encap_prim bq_state)
      (semantics_embed abs_bq_spec)
      (skel bq_spec).

  Lemma bq_refine:
    E.forward_simulation
      (&1) (&1) bq_espec
      (comp_esem' bq_espec rb_espec rb_bq_skel).
  Admitted.

  Lemma rb_bq_correct:
    E.forward_simulation
      (&1) (&1) abs_bq_espec
      (comp_esem' (eclightp bq_program) (eclightp rb_program) rb_bq_skel).
  Admitted.

End REFINE.
