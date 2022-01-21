From Coq Require Import List.
From examples Require Import CAL.
From compcert Require Import
     Integers Coqlib Maps
     Memory AST Values
     Clight Ctypes
     LanguageInterface
     Events Globalenvs
     Smallstep.
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

Definition Nz: Z := Z.of_nat CAL.N.

Section CLIGHT.

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
         (Ederef
            (Ebinop Cop.Oadd
                    (Evar arr_id (tarray tint Nz))
                    (Etempvar get_arg_id tint)
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
    Ssequence
      (Sassign
         (Ederef
            (Ebinop Cop.Oadd
                    (Evar arr_id (tarray tint Nz))
                    (Etempvar set_arg1_id tint)
                    (tptr tint))
            tint)
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
            (Sset rb_inc1_tmp (Evar cnt1_id tint))
            (Sassign
               (Evar cnt1_id tint)
               (Ebinop Cop.Oadd
                       (Evar cnt1_id tint)
                       (Econst_int (Int.repr 1) tint)
                       tint)))
         (Sassign
            (Evar cnt1_id tint)
            (Ebinop Cop.Omod
                    (Evar cnt1_id tint)
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
            (Sset rb_inc2_tmp (Evar cnt2_id tint))
            (Sassign
               (Evar cnt2_id tint)
               (Ebinop Cop.Oadd
                       (Evar cnt2_id tint)
                       (Econst_int (Int.repr 1) tint)
                       tint)))
         (Sassign
            (Evar cnt2_id tint)
            (Ebinop Cop.Omod
                    (Evar cnt2_id tint)
                    (Econst_int (Int.repr Nz) tint)
                    tint)))
      (Sreturn (Some (Etempvar rb_inc2_tmp tint))).
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

End CLIGHT.
