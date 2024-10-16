From Coq Require Import List.
From compcert Require Import
     Integers Coqlib Maps
     Memory AST Values
     Clight Ctypes
     LanguageInterface
     Events Globalenvs
     Smallstep CategoricalComp.
From compcert.clightp Require Import
  Lifting Encapsulation
  ClightP PEnv ClightPLink ClightPComp.
Import ListNotations.

Definition query_alloc_flag '(cq _ _ _ m) := Mem.alloc_flag m.
Definition reply_alloc_flag '(cr _ m) := Mem.alloc_flag m.

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
         (Eindex (Epvar arr_id (tarray tint Nz))
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
      (Supdate
         (Eindex (Epvar arr_id (tarray tint Nz))
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
            (Supdate
               (Epvar cnt1_id tint)
               (Ebinop Cop.Oadd
                       (Epvar cnt1_id tint)
                       (Econst_int (Int.repr 1) tint)
                       tint)))
         (Supdate
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
            (Supdate
               (Epvar cnt2_id tint)
               (Ebinop Cop.Oadd
                       (Epvar cnt2_id tint)
                       (Econst_int (Int.repr 1) tint)
                       tint)))
         (Supdate
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

  Definition arr_pvar : privvar :=
    let tarr := tarray tint Nz in
    {|
      pvar_init := Array Nz (ZMap.init (Val (Vint Int.zero) tint)) tarr;
    |}.
  (* Next Obligation. *)
  (*   constructor; eauto. *)
  (*   - intros. rewrite ZMap.gi. constructor. *)
  (*   - unfold type_size_eq. intros. reflexivity. *)
  (* Qed. *)

  Definition cnt_pvar : privvar :=
    {|
      pvar_init := Val (Vint Int.zero) tint;
    |}.
  (* Next Obligation. constructor. Qed. *)

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
      prog_main := Some 999%positive;
      prog_types := [];
      prog_comp_env := (PTree.empty _);
      prog_norepet := _;
      prog_priv_ok := _;
    |}.
  Next Obligation.
    unfold arr_id, cnt1_id, cnt2_id, get_id, set_id, inc1_id, inc2_id in *.
    repeat (constructor; [ simpl; lia | ]). constructor.
  Defined.
  Next Obligation.
    constructor.
    - (repeat apply in_inv in H as [H|H]); inv H.
      + constructor; intros; rewrite ZMap.gi.
        * constructor.
        * reflexivity.
      + constructor.
      + constructor.
    - (repeat apply in_inv in H as [H|H]); inv H.
      + econstructor.
        * intros. rewrite ZMap.gi. constructor. cbn.
          apply Z.divide_refl.
        * cbn. exists 100%Z. lia.
      + constructor. apply Z.divide_refl.
      + constructor. apply Z.divide_refl.
    - unfold pvar_size_ok. (repeat apply in_inv in H as [H|H]); inv H.
      + etransitivity. 2: apply int_max_le_ptrofs_max. cbn. lia.
      + etransitivity. 2: apply int_max_le_ptrofs_max. cbn. lia.
      + etransitivity. 2: apply int_max_le_ptrofs_max. cbn. lia.
    - unfold pvar_type_ok. (repeat apply in_inv in H as [H|H]); inv H; cbn.
      + econstructor; intros; try easy. constructor.
      + constructor.
      + constructor.
  Qed.

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
      (* for linking purpose, external functions have to be public *)
      prog_public := [enq_id; deq_id; inc1_id; inc2_id; get_id; set_id];
      prog_main := Some 999%positive;
      prog_types := [];
      prog_comp_env := (PTree.empty _);
      prog_norepet := _;
      prog_priv_ok := _;
    |}.
  Next Obligation.
    unfold enq_id, deq_id, inc1_id, inc2_id, get_id, set_id.
    repeat (constructor; [ simpl; lia | ]). constructor.
  Defined.
  Next Obligation.
    intros H p Hp. inv Hp.
  Qed.

End CLIGHTP.

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

Ltac crush_loc:=
  cbn;
  lazymatch goal with
  | [ |- eval_loc _ _ _ _ _ _ (Epvar _ _) _ _ ] =>
      eapply eval_Epvar; [ eauto | solve_ptree ]
  end.

Ltac crush_penv :=
  cbn; eauto;
  lazymatch goal with
  | [ |- pwrite _ _ _ _ _ _ _ ] =>
      econstructor; [ solve_ptree | eauto | eauto | try reflexivity ]
  | [ |- pread _ _ _ _ _ _ ] =>
      econstructor; [ solve_ptree | eauto ]
  end.

Ltac crush_eval_expr :=
  cbn;
  lazymatch goal with
  | [ |- eval_expr _ _ _ _ _ _ (Etempvar _ _) _ ] => apply eval_Etempvar; reflexivity
  | [ |- eval_expr _ _ _ _ _ _ (Econst_int _ _) _ ] => apply eval_Econst_int
  | [ |- eval_expr _ _ _ _ _ _ (Ebinop _ _ _ _) _ ] => eapply eval_Ebinop
  | [ |- eval_expr _ _ _ _ _ _ (Evar _ _) _ ] => eapply eval_Elvalue
  | [ |- eval_expr _ _ _ _ _ _ (Ederef _ _) _ ] => eapply eval_Elvalue
  | [ |- eval_expr _ _ _ _ _ _ (Epvar _ _) _ ] =>
      eapply eval_Eloc; [ try crush_loc | try crush_penv | ]; eauto
  end.
Ltac crush_eval_lvalue :=
  cbn;
  lazymatch goal with
  | [ |- eval_lvalue _ _ _ _ _ _ (Evar _ _) _ _ _ ] =>
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
    | [ |- eval_expr _ _ _ _ _ _ _ _ ] => crush_eval_expr
    | [ |- eval_lvalue _ _ _ _ _ _ _ _ _ _ ] => crush_eval_lvalue
    | [ |- eval_exprlist _ _ _ _ _ _ _ _ _ ] => econstructor
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
  | [ |- Step _ (Callstate _ _ _ _, _) _ _ ] =>
      eapply step_internal_function;
      [ eauto | constructor; cbn;
        [ solve_list_norepet
        | solve_list_norepet
        | solve_list_disjoint
        | repeat (econstructor; simpl; auto)
        | reflexivity | eauto ] ]
  | [ |- Step _ (State _ (Ssequence _ _) _ _ _ _, _) _ _ ] => apply step_seq
  | [ |- Step _ (State _ (Sset _ _) _ _ _ _, _) _ _ ] => apply step_set
  | [ |- Step _ (State _ (Scall _ _ _) _ _ _ _, _) _ _ ] => eapply step_call
  | [ |- Step _ (Returnstate _ _ _, _) _ _ ] => eapply step_returnstate
  | [ |- Step _ (State _ Sskip (Kseq _ _) _ _ _, _) _ _ ] => apply step_skip_seq
  | [ |- Step _ (State _ (Sassign _ _) _ _ _ _, _) _ _ ] => eapply step_assign
  | [ |- Step _ (State _ (Supdate _ _) _ _ _ _, _) _ _ ] =>
      eapply step_update;
      [ try crush_loc | try crush_expr | try crush_penv | .. ]; cbn; eauto
  | [ |- Step _ (State _ (Sreturn None) _ _ _ _, _) _ _ ] => eapply step_return_0
  | [ |- Step _ (State _ (Sreturn (Some _)) _ _ _ _, _) _ _ ] => eapply step_return_1
  | [ |- Step _ (State _ ?s _ _ _ _, _) _ _ ] => is_const s; unfold s; crush_step
  end.

Ltac lts_step := eapply star_left with (t1 := E0) (t2 := E0); [ | | reflexivity ].

Ltac crush_star :=
  match goal with
  | [ |- Star _ (Returnstate _ Kstop _) _ _ ] => eapply star_refl
  | _ => lts_step; [ crush_step; crush_expr | cbn; try crush_star ]
  end.


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
  | initial_state_inc1: forall vf b m rbst sig (HFLAG: Mem.alloc_flag m = true),
      vf = Vptr b Integers.Ptrofs.zero ->
      Genv.find_symbol ge inc1_id = Some b ->
      Ple (Genv.genv_next ge) (Mem.nextblock m) ->
      sig = inc1_sg ->
      rb_initial_state (cq vf sig nil m, rbst) (rb_init inc1 rbst nil m)
  | initial_state_inc2: forall vf b m rbst sig (HFLAG: Mem.alloc_flag m = true),
      vf = Vptr b Integers.Ptrofs.zero ->
      Genv.find_symbol ge inc2_id = Some b ->
      Ple (Genv.genv_next ge) (Mem.nextblock m) ->
      sig = inc2_sg ->
      rb_initial_state (cq vf sig nil m, rbst) (rb_init inc2 rbst nil m)
  | initial_state_geti: forall vf b v m rbst sig (HFLAG: Mem.alloc_flag m = true),
      vf = Vptr b Integers.Ptrofs.zero ->
      Genv.find_symbol ge get_id = Some b ->
      Ple (Genv.genv_next ge) (Mem.nextblock m) ->
      Cop.val_casted v tint ->
      sig = get_sg ->
      rb_initial_state (cq vf sig [v] m, rbst) (rb_init geti rbst [v] m)
  | initial_state_seti: forall vf b m rbst sig vargs v1 v2 (HFLAG: Mem.alloc_flag m = true),
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
    skel := clightp_erase_program rb_program;
    activate se := rb_lts (ClightP.globalenv se rb_program);
    footprint := AST.footprint_of_program rb_program;
  |}.

Instance rb_state_pset : PSet rb_state :=
  {
    pset_init _ := (fun _ => Vint (Int.zero), 0, 0)%nat;
  }.

Program Definition rb_espec : li_c +-> li_c :=
  comp_esem' (encap_prim rb_state (skel rb_spec)) (semantics_embed rb_spec) (skel rb_spec).

Inductive nat_rel: nat -> Values.val -> Prop :=
| nat_rel_intro n i
  (HI: Z.of_nat n = Integers.Int.intval i):
  nat_rel n (Vint i).

Inductive rb_penv_rel: rb_state -> penv -> Prop :=
| rb_penv_intro f c1 c2 pe vf vc1 vc2
  (HA: pe ! arr_id = Some (Array Nz vf (tarray tint Nz)))
  (HC1: pe ! cnt1_id = Some (Val vc1 tint))
  (HC2: pe ! cnt2_id = Some (Val vc2 tint))
  (RA: (forall i, (i < N)%nat ->
             exists v, ZMap.get (Z.of_nat i) vf = Val v tint
                  /\ v = f i /\ Cop.val_casted v tint))
  (RC1: nat_rel c1 vc1) (NC1: (c1 < N)%nat)
  (RC2: nat_rel c2 vc2) (NC2: (c2 < N)%nat)
  (HNONE: forall id, id <> arr_id -> id <> cnt1_id -> id <> cnt2_id -> pe ! id = None):
  rb_penv_rel (f, c1, c2) pe.

Inductive rb_query: c_query * rb_state -> c_query * penv -> Prop :=
| rb_query_intro q rbst pe (HPE: rb_penv_rel rbst pe):
  rb_query (q, rbst) (q, pe).
Inductive rb_reply: c_reply * rb_state -> c_reply * penv -> Prop :=
| rb_reply_intro r rbst pe (HPE: rb_penv_rel rbst pe):
  rb_reply (r, rbst) (r, pe).
Program Definition rb_cc: callconv (li_c@rb_state) (li_c@penv) :=
  {|
    ccworld := unit;
    match_senv _ se1 se2 := se1 = se2;
    match_query _ := rb_query;
    match_reply _ := rb_reply;
  |}.
Next Obligation. reflexivity. Qed.
Next Obligation. inv H0. reflexivity. Qed.
Next Obligation. inv H. reflexivity. Qed.

Section RB.

  Definition rb_pset := penv_pset (ClightPComp.vars_of_program rb_program).

  Inductive rb_penv_ms:
    Smallstep.state (encap_prim rb_state (skel rb_spec)) ->
    Smallstep.state (@encap_prim _ penv rb_pset (skel rb_spec)) -> Prop :=
  | rb_penv_ms_q q rbst pe:
    rb_penv_rel rbst pe ->
    rb_penv_ms (@st_q (li_c@rb_state)  (q, rbst)) (@st_q (li_c@penv) (q, pe))
  | rb_penv_ms_r r rbst pe:
    rb_penv_rel rbst pe ->
    rb_penv_ms (@st_r (li_c@rb_state) (r, rbst)) (@st_r (li_c@penv) (r, pe)).

  Hint Constructors rb_penv_ms.

  Lemma rb_correct1:
    E.forward_simulation (&rb_cc) (&1)
      (encap_prim rb_state (skel rb_spec))
      (@encap_prim _ penv rb_pset (skel rb_spec)).
  Proof.
    apply st_normalize_fsim. constructor.
    eapply ST.Forward_simulation with
      (ltof _ (fun (_: unit) => 0%nat))
      (fun _ _ _ _ _ _ s1 s2 => rb_penv_ms s1 s2)
      (fun _ '(_, (rbst, pe)) => rb_penv_rel rbst pe); try easy.
    - intros. cbn in *. eprod_crush; eauto.
    - cbn. intros se Hse. econstructor; try ptree_tac.
      + intros. exists (Vint Int.zero). repeat split.
        constructor. reflexivity.
      + constructor. reflexivity.
      + unfold N. lia.
      + constructor. reflexivity.
      + unfold N. lia.
      + intros. do 3 rewrite PTree.gso by eauto. reflexivity.
    - intros. cbn in *. eprod_crush. econstructor; intros; cbn in *; eprod_crush.
      + subst. eexists tt, _. split. constructor.
        inv H3. eexists tt, (tt, (_, _)). repeat split; eauto.
      + inv H2. inv H. eexists (_, _). split. constructor.
        eexists (tt, (_, _)). repeat split; eauto.
      + inv H2. inv H. eexists (_, _). split. constructor.
        eexists tt, tt. repeat split; eauto.
        eexists. split. constructor. inv H3.
        eexists tt, (tt, (_, _)). repeat split; eauto.
        inv H2. econstructor; eauto.
      + easy.
        Unshelve. all: eauto.
  Qed.

End RB.

Inductive rb_func_rel: rb_sig -> function -> Prop :=
| rb_inc1_rel: rb_func_rel inc1 rb_inc1
| rb_inc2_rel: rb_func_rel inc2 rb_inc2
| rb_set_rel: rb_func_rel seti rb_set
| rb_get_rel: rb_func_rel geti rb_get.

Inductive rb_ms se: rb_internal_state -> state * penv -> Prop :=
| rb_ms_init:
  forall vf pe m rbst vs sg func
    (HFLAG: Mem.alloc_flag m = true)
    (HPE: rb_penv_rel rbst pe)
    (HFUN: rb_func_rel sg func)
    (HF: Genv.find_funct (Genv.globalenv se rb_program) vf
         = Some (Internal func)),
    rb_ms se (rb_init sg rbst vs m) (Callstate vf vs Kstop m, pe)
| rb_ms_final:
  forall rv pe m rbst
    (HFLAG: Mem.alloc_flag m = true)
    (HPE: rb_penv_rel rbst pe),
    rb_ms se (rb_final rbst rv m) (Returnstate rv Kstop m, pe).

Lemma genv_funct_symbol se id b f (p: ClightP.program):
  Genv.find_symbol se id = Some b ->
  (prog_defmap p) ! id = Some (Gfun f) ->
  Genv.find_funct (ClightP.globalenv se p) (Vptr b Ptrofs.zero) = Some f.
Proof.
  intros H1 H2.
  unfold Genv.find_funct, Genv.find_funct_ptr.
  destruct Ptrofs.eq_dec; try congruence.
  apply Genv.find_invert_symbol in H1. cbn.
  rewrite Genv.find_def_spec. rewrite H1.
  rewrite H2. reflexivity.
Qed.

Opaque PTree.set.
Opaque Nat.modulo.

Lemma cnt_inc_simp c i:
  Z.of_nat c = Int.intval i -> (c < N)%nat ->
  Z.of_nat (S c mod N) = Int.intval (Int.modu (Int.add i (Int.repr 1)) (Int.repr Nz)).
Proof.
  intros H1 H2. unfold Int.add, Int.modu.
  apply inj_le in H2. rewrite Nat2Z.inj_succ in H2.
  rewrite H1 in H2.
  repeat rewrite Int.unsigned_repr.
  all: unfold Nz in *; cbn -[Z.mul] in *; unfold Int.unsigned; try lia.
  - unfold Int.unsigned. rewrite <- H1.
    rewrite mod_Zmod.
    + f_equal. rewrite Nat2Z.inj_succ. reflexivity.
    + unfold N. lia.
  - unfold Int.unsigned. rewrite <- H1.
    exploit (Z.mod_pos_bound (Z.of_nat c + 1) (Z.of_nat N)); unfold N; lia.
Qed.

Lemma cop_sem_mod m i j:
  j <> Int.zero -> Cop.sem_mod (Vint i) tint (Vint j) tint m = Some (Vint (Int.modu i j)).
Proof.
  intros Hj. unfold Cop.sem_mod.
  unfold Cop.sem_binarith. cbn.
  unfold Cop.sem_cast. cbn.
  destruct Archi.ptr64. cbn.
  rewrite Int.eq_false; eauto.
  destruct intsize_eq.
  rewrite Int.eq_false; eauto.
  congruence.
Qed.

Open Scope Z_scope.

Hint Constructors rb_func_rel.
Opaque clightp2.
Hint Constructors eval_loc pread pread_val pwrite pwrite_val.
Hint Constructors Cop.val_casted.

Lemma rb_correct2: forward_simulation 1 rb_cc rb_spec (clightp2 rb_program).
Proof.
  constructor. econstructor. reflexivity. firstorder.
  intros. instantiate (1 := fun _ _ _ => _). cbn beta.
  destruct H. set (ms := fun s1 s2 => rb_ms se1 s1 s2).
  eapply forward_simulation_plus with (match_states := ms).
  - intros [q1 rs1] [q2 pe] s1 Hq Hs. inv Hq. cbn in *. subst. inv Hs.
    (* TODO: cleanup by ltac *)
    + eexists (_, _). split.
      * econstructor; eauto.
        eapply genv_funct_symbol; eauto. reflexivity.
        reflexivity. constructor.
      * econstructor; eauto.
        eapply genv_funct_symbol; eauto.
    + eexists (_, _). split.
      * econstructor; eauto.
        eapply genv_funct_symbol; eauto. reflexivity.
        reflexivity. constructor.
      * econstructor; eauto.
        eapply genv_funct_symbol; eauto.
    + eexists (_, _). split.
      * econstructor; eauto.
        eapply genv_funct_symbol; eauto. reflexivity.
        reflexivity. repeat constructor; eauto.
      * econstructor; eauto.
        eapply genv_funct_symbol; eauto.
    + eexists (_, _). split.
      * econstructor; eauto.
        eapply genv_funct_symbol; eauto. reflexivity.
        reflexivity. repeat constructor; eauto.
      * econstructor; eauto.
        eapply genv_funct_symbol; eauto.
  - intros. cbn in *. eprod_crush. inv H1. inv H.
    eexists (_, _). split; constructor; cbn; eauto.
  - intros. inv H1.
  - intros * HS [s2 pe] HM. inv HS; inv HM.
    (* inc1 *)
    + inv HPE. inv RC1. inv HFUN. eexists (_, _). split.
      * eapply plus_left. crush_step.
        lts_step. crush_step.
        lts_step. crush_step.
        lts_step. crush_step.
        lts_step. crush_step. crush_expr.
        lts_step. crush_step.
        lts_step. crush_step.
        lts_step. crush_step.
        lts_step. crush_step.
        lts_step. crush_step.
        lts_step. crush_step; crush_expr.
        apply star_refl. reflexivity.
      * cbn. rewrite HI.
        replace (Int.repr (Int.intval i)) with i
          by now rewrite Int.repr_unsigned.
        econstructor; eauto.
        econstructor; eauto; try ptree_tac.
        -- constructor. apply cnt_inc_simp; eauto.
        -- apply Nat.mod_upper_bound. lia.
        -- intros. rewrite PTree.gso; eauto.
           rewrite PTree.gso; eauto.
    (* inc2 *)
    + inv HPE. inv RC2. inv HFUN. eexists (_, _). split.
      * eapply plus_left. crush_step.
        lts_step. crush_step.
        lts_step. crush_step.
        lts_step. crush_step.
        lts_step. crush_step. crush_expr.
        lts_step. crush_step.
        lts_step. crush_step.
        lts_step. crush_step.
        lts_step. crush_step.
        lts_step. crush_step.
        lts_step. crush_step; crush_expr.
        apply star_refl. reflexivity.
      * cbn. rewrite HI.
        replace (Int.repr (Int.intval i)) with i
          by now rewrite Int.repr_unsigned.
        econstructor; eauto.
        econstructor; eauto; try ptree_tac.
        -- constructor. apply cnt_inc_simp; eauto.
        -- apply Nat.mod_upper_bound. lia.
        -- intros. rewrite PTree.gso; eauto.
           rewrite PTree.gso; eauto.
    (* get *)
    + inv HPE. inv HFUN.
      edestruct RA as (v & HV1 & HV2 & HV3). apply H1.
      assert (HI1: 0 <= Z.of_nat i < 100).
      { unfold N in H1. lia. }
      assert (HI2: 0 <= Z.of_nat i <= Int.max_unsigned).
      { split; try lia. etransitivity. instantiate (1 := 100); lia. easy.  }
      eexists (_, _). split.
      * eapply plus_left. crush_step.
        lts_step. crush_step.
        {
          eapply eval_Eloc; try reflexivity.
          - econstructor; eauto.
            + reflexivity.
            + crush_expr.
            + rewrite Int.unsigned_repr; eauto.
          - rewrite Int.unsigned_repr; eauto.
            econstructor; eauto.
            econstructor; eauto.
            rewrite HV1. subst. econstructor.
        }
        1-2: crush_expr; eauto. subst; eauto.
        apply star_refl. reflexivity.
      * econstructor; eauto. econstructor; eauto.
  (* set *)
    + inv HPE. inv HFUN.
      edestruct RA as (v & HV1 & HV2 & HV3). apply H1.
      assert (HI1: 0 <= Z.of_nat i < 100).
      { unfold N in H1. lia. }
      assert (HI2: 0 <= Z.of_nat i <= Int.max_unsigned).
      { split; try lia. etransitivity. instantiate (1 := 100); lia. easy.  }
      eexists (_, _). split.
      * eapply plus_left. crush_step.
        lts_step. crush_step.
        lts_step.
        {
          eapply step_update; try solve [ reflexivity ].
          - econstructor; eauto.
            + reflexivity.
            + crush_expr.
            + rewrite Int.unsigned_repr; eauto.
          - crush_expr.
          - crush_penv. rewrite Int.unsigned_repr; eauto.
          - eauto.
        }
        lts_step. crush_step.
        lts_step. crush_step; crush_expr.
        apply star_refl. reflexivity.
      * constructor; eauto. econstructor; eauto; try solve_ptree.
        intros ix Hx. destruct (Nat.eq_dec i ix).
        -- subst. eexists. split; eauto.
           rewrite ZMap.gss. reflexivity.
        -- subst.
           edestruct RA. apply Hx. destruct H as (A & B & C).
           eexists. split; eauto.
           rewrite ZMap.gso; eauto.
           intros Hc. apply n. lia.
        -- intros. rewrite PTree.gso; eauto.
  - apply well_founded_ltof.
Qed.

Lemma rb_correct:
  E.forward_simulation (&1) (&1) rb_espec (eclightp rb_program).
Proof.
  eapply encap_fsim_lcomp_sk; eauto. instantiate (1 := &rb_cc).
  - apply rb_correct1.
  - apply encap_fsim_embed. apply rb_correct2.
  - apply Linking.linkorder_refl.
  - apply Linking.linkorder_refl.
Qed.

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
  | initial_state_enq: forall vf b v m  sig (HFLAG: Mem.alloc_flag m = true),
      vf = Vptr b Integers.Ptrofs.zero ->
      Genv.find_symbol ge enq_id = Some b ->
      Ple (Genv.genv_next ge) (Mem.nextblock m) ->
      Cop.val_casted v tint ->
      sig = enq_sg ->
      bq_initial_state (cq vf sig [v] m) (bq_init enq [v] m)
  | initial_state_deq: forall vf b m  sig (HFLAG: Mem.alloc_flag m = true),
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
      Smallstep.initial_state q := bq_initial_state q;
      Smallstep.at_external := bq_at_external;
      Smallstep.after_external := bq_after_external;
      Smallstep.final_state s r := bq_final_state s r;
      Smallstep.globalenv := ge;
    |}.

End RB_LTS.

Definition bq_spec: semantics li_c li_c :=
  {|
    skel := clightp_erase_program bq_program;
    activate se := bq_lts (ClightP.globalenv se bq_program);
    footprint := AST.footprint_of_program bq_program;
  |}.

Program Definition bq_cc: callconv li_c (li_c@penv) :=
  {|
    ccworld := unit;
    match_senv _ := eq;
    match_query _ q1 '(q2, _) := q1 = q2;
    match_reply _ r1 '(r2, _) := r1 = r2;
  |}.
Next Obligation. reflexivity. Qed.
Next Obligation. reflexivity. Qed.
Next Obligation. reflexivity. Qed.

Section BQ.

  Definition bq_pset := penv_pset (ClightPComp.vars_of_program bq_program).

  Inductive bq_penv_ms:
    @Smallstep.state li_c _ (semantics_embed (id_semantics (skel bq_spec))) ->
    Smallstep.state (@encap_prim _ penv bq_pset (skel bq_spec)) -> Prop :=
  | bq_penv_ms_q q pe:
    bq_penv_ms (st_q q) (@st_q (li_c@penv) (q, pe))
  | bq_penv_ms_r r pe:
    bq_penv_ms (st_r r) (@st_r (li_c@penv) (r, pe)).

  Hint Constructors bq_penv_ms.

  Lemma bq_correct1:
    E.forward_simulation (&bq_cc) (&1)
      (semantics_embed (id_semantics (skel bq_spec)))
      (@encap_prim _ penv bq_pset (skel bq_spec)).
  Proof.
    apply st_normalize_fsim. constructor.
    eapply ST.Forward_simulation with
      (ltof _ (fun (_: unit) => 0%nat))
      (fun _ _ _ _ _ _ s1 s2 => bq_penv_ms s1 s2)
      (fun _ _ => True); try easy.
    intros. constructor; intros; cbn in *; eprod_crush; subst.
    - inv H4. eexists tt, _. split. constructor.
      eexists tt, (tt, (tt, _)). repeat split; eauto.
    - inv H3. inv H2.
      eexists (_, _). split. econstructor.
      eexists (tt, (tt, _)). repeat split; eauto.
    - inv H3. inv H2. eexists (_, _). split. econstructor.
      exists tt, tt. repeat split; eauto.
      eprod_crush. inv H3.
      eexists. split. constructor.
      eexists tt, (tt, (tt, _)). repeat split; eauto.
    - easy.
      Unshelve. all: eauto.
  Qed.

End BQ.

Inductive bq_ms se: bq_internal_state -> state * penv -> Prop :=
| bq_ms_enq:
  forall vf m v pe,
    Mem.alloc_flag m = true ->
    Cop.val_casted v tint ->
    Genv.find_funct (Genv.globalenv se bq_program) vf = Some (Internal bq_enq) ->
    bq_ms se (bq_init enq [v] m) (Callstate vf [v] Kstop m, pe)
| bq_ms_deq:
  forall vf m pe,
    Mem.alloc_flag m = true ->
    Genv.find_funct (Genv.globalenv se bq_program) vf = Some (Internal bq_deq) ->
    bq_ms se (bq_init deq [] m) (Callstate vf [] Kstop m, pe)
| bq_ms_call_inc1:
  forall vf k m b pe,
    Mem.alloc_flag m = true ->
    vf = Vptr b Integers.Ptrofs.zero ->
    Genv.find_symbol se inc1_id = Some b ->
    k = (Kcall (Some bq_deq_tmp1) bq_deq empty_env
          (PTree.Node (PTree.Node PTree.Empty (Some Vundef) PTree.Empty) (Some Vundef) PTree.Empty)
          (Kseq
             (Ssequence
                (Scall (Some bq_deq_tmp2) (Evar get_id (Tfunction (Tcons tint Tnil) tint cc_default))
                   [Etempvar bq_deq_tmp1 tint]) (Sreturn (Some (Etempvar bq_deq_tmp2 tint)))) Kstop)) ->
    bq_ms se (bq_call inc1 [] m) (Callstate vf [] k m, pe)
| bq_ms_call_inc2:
  forall vf k m v b pe,
    Mem.alloc_flag m = true ->
    Cop.val_casted v tint ->
    vf = Vptr b Integers.Ptrofs.zero ->
    Genv.find_symbol se inc2_id = Some b ->
    k = (Kcall (Some bq_enq_tmp) bq_enq empty_env
          (PTree.Node (PTree.Node PTree.Empty (Some Vundef) PTree.Empty) (Some v) PTree.Empty)
          (Kseq
             (Ssequence
                (Scall None (Evar set_id (Tfunction (Tcons tint (Tcons tint Tnil)) tvoid cc_default))
                   [Etempvar bq_enq_tmp tint; Etempvar enq_arg_id tint]) (Sreturn None)) Kstop)) ->
    bq_ms se (bq_call inc2 [v] m) (Callstate vf [] k m, pe)

| bq_ms_mid_enq:
  forall m v1 v2 k pe,
    Mem.alloc_flag m = true ->
    Cop.val_casted v1 tint ->
    Cop.val_casted v2 tint ->
    k = (Kcall (Some bq_enq_tmp) bq_enq empty_env
          (PTree.Node (PTree.Node PTree.Empty (Some Vundef) PTree.Empty) (Some v2) PTree.Empty)
          (Kseq
             (Ssequence
                (Scall None (Evar set_id (Tfunction (Tcons tint (Tcons tint Tnil)) tvoid cc_default))
                   [Etempvar bq_enq_tmp tint; Etempvar enq_arg_id tint]) (Sreturn None)) Kstop)) ->
    bq_ms se (bq_middle enq [v1; v2] m) (Returnstate v1 k m, pe)
| bq_ms_mid_deq:
  forall m v k pe,
    Mem.alloc_flag m = true ->
    Cop.val_casted v tint ->
    k = (Kcall (Some bq_deq_tmp1) bq_deq empty_env
          (PTree.Node (PTree.Node PTree.Empty (Some Vundef) PTree.Empty) (Some Vundef) PTree.Empty)
          (Kseq
             (Ssequence
                (Scall (Some bq_deq_tmp2) (Evar get_id (Tfunction (Tcons tint Tnil) tint cc_default))
                   [Etempvar bq_deq_tmp1 tint]) (Sreturn (Some (Etempvar bq_deq_tmp2 tint)))) Kstop)) ->
    bq_ms se (bq_middle deq [v] m) (Returnstate v k m, pe)

| bq_ms_call_get:
  forall vf k m v b pe,
    Mem.alloc_flag m = true ->
    vf = Vptr b Integers.Ptrofs.zero ->
    Genv.find_symbol se get_id = Some b ->
    Cop.val_casted v tint ->
    k = (Kcall (Some bq_deq_tmp2) bq_deq empty_env
          (PTree.Node (PTree.Node PTree.Empty (Some Vundef) PTree.Empty) (Some v) PTree.Empty)
          (Kseq (Sreturn (Some (Etempvar bq_deq_tmp2 tint))) Kstop)) ->
    bq_ms se (bq_call geti [v] m) (Callstate vf [v] k m, pe)
| bq_ms_call_set:
  forall vf k m v1 v2 b pe,
    Mem.alloc_flag m = true ->
    vf = Vptr b Integers.Ptrofs.zero ->
    Genv.find_symbol se set_id = Some b ->
    Cop.val_casted v1 tint ->
    Cop.val_casted v2 tint ->
    k = (Kcall None bq_enq empty_env (PTree.Node (PTree.Node PTree.Empty (Some v1) PTree.Empty) (Some v2) PTree.Empty) (Kseq (Sreturn None) Kstop)) ->
    bq_ms se (bq_call seti [v1; v2] m) (Callstate vf [v1; v2] k m, pe)

| bq_ms_midx_enq:
  forall m v k le pe,
    Mem.alloc_flag m = true ->
    k = (Kcall None bq_enq empty_env le (Kseq (Sreturn None) Kstop)) ->
    bq_ms se (bq_middlex enq v m) (Returnstate v k m, pe)
| bq_ms_midx_deq:
  forall m v rv k pe,
    Mem.alloc_flag m = true ->
    Cop.val_casted rv tint ->
    Cop.val_casted v tint ->
    k = (Kcall (Some bq_deq_tmp2) bq_deq empty_env
          (PTree.Node (PTree.Node PTree.Empty (Some Vundef) PTree.Empty) (Some v) PTree.Empty)
          (Kseq (Sreturn (Some (Etempvar bq_deq_tmp2 tint))) Kstop)) ->
    bq_ms se (bq_middlex deq rv m) (Returnstate rv k m, pe)

| bq_ms_final:
  forall rv m pe,
    Mem.alloc_flag m = true ->
    bq_ms se (bq_final rv m) (Returnstate rv Kstop m, pe).

  Import Ptrofs.

  Lemma clightp_erase_program_defmap (p: program) id g:
    option_map (@erase_globdef fundef type) (prog_defmap p) ! id = Some g ->
    (prog_defmap (clightp_erase_program p)) ! id = Some g.
  Proof.
    unfold prog_defmap. cbn - [PTree_Properties.of_list].
    rewrite PTree_Properties.of_list_elements.
    rewrite PTree.gcombine by reflexivity.
    unfold prog_defmap.
    destruct ((PTree_Properties.of_list (AST.prog_defs p)) ! id)
      eqn: Hd.
    - setoid_rewrite Hd. cbn. intros. inv H.
      destruct ((PTree_Properties.of_list (prog_private p)) ! id)
        eqn: Hp.
      + exfalso.
        pose proof (prog_norepet p).
        apply list_norepet_app in H as (A & B & C).
        eapply C; eauto.
        * apply in_map_iff. eexists (_, _). split; eauto.
        * apply in_map_iff. eexists (_, _).
          split. reflexivity. eauto.
      + reflexivity.
    - setoid_rewrite Hd. inversion 1.
  Qed.

  Theorem clightp_find_def_symbol se p id g:
    Genv.valid_for (clightp_erase_program p) se ->
    (prog_defmap p)!id = Some g ->
    exists b, Genv.find_symbol (globalenv se p) id = Some b
         /\ Genv.find_def (globalenv se p) b = Some g.
  Proof.
    intros Hse Hg.
    edestruct Hse as (b & g' & Hb & Hg' & LO); eauto.
    apply clightp_erase_program_defmap. rewrite Hg. reflexivity.
    exists b. split. assumption.
    cbn. rewrite Genv.find_def_spec.
    apply Genv.find_invert_symbol in Hb. rewrite Hb. auto.
  Qed.

  Lemma inc2_block se:
    Genv.valid_for (clightp_erase_program bq_program) se ->
    exists b, Genv.find_symbol (globalenv se bq_program) inc2_id = Some b /\
           Genv.find_funct (globalenv se bq_program) (Vptr b zero) = Some inc2_ext.
  Proof.
    intros Hse.
    edestruct (@clightp_find_def_symbol se bq_program inc2_id)
      as (b & Hb1 & Hb2); eauto.
    reflexivity.
    exists b. split; eauto. eapply genv_funct_symbol; eauto.
  Qed.

  Lemma set_block se:
    Genv.valid_for (clightp_erase_program bq_program) se ->
    exists b, Genv.find_symbol (globalenv se bq_program) set_id = Some b /\
           Genv.find_funct (globalenv se bq_program) (Vptr b zero) = Some set_ext.
  Proof.
    intros Hse.
    edestruct (@clightp_find_def_symbol se bq_program set_id)
      as (b & Hb1 & Hb2); eauto.
    reflexivity.
    exists b. split; eauto. eapply genv_funct_symbol; eauto.
  Qed.

  Lemma inc1_block se:
    Genv.valid_for (clightp_erase_program bq_program) se ->
    exists b, Genv.find_symbol (globalenv se bq_program) inc1_id = Some b /\
           Genv.find_funct (globalenv se bq_program) (Vptr b zero) = Some inc1_ext.
  Proof.
    intros Hse.
    edestruct (@clightp_find_def_symbol se bq_program inc1_id)
      as (b & Hb1 & Hb2); eauto.
    reflexivity.
    exists b. split; eauto. eapply genv_funct_symbol; eauto.
  Qed.

  Lemma get_block se:
    Genv.valid_for (clightp_erase_program bq_program) se ->
    exists b, Genv.find_symbol (globalenv se bq_program) get_id = Some b /\
           Genv.find_funct (globalenv se bq_program) (Vptr b zero) = Some get_ext.
  Proof.
    intros Hse.
    edestruct (@clightp_find_def_symbol se bq_program get_id)
      as (b & Hb1 & Hb2); eauto.
    reflexivity.
    exists b. split; eauto. eapply genv_funct_symbol; eauto.
  Qed.

Lemma bq_correct2: forward_simulation 1 bq_cc bq_spec (clightp2 bq_program).
Proof.
  constructor. econstructor. reflexivity. firstorder.
  intros. instantiate (1 := fun _ _ _ => _). cbn beta.
  destruct H. subst.
  eapply forward_simulation_plus with (match_states := bq_ms se1).
  - intros. cbn in *. eprod_crush. inv H1.
    + eexists (_, _). split.
      * econstructor; eauto.
        eapply genv_funct_symbol; eauto. reflexivity.
        unfold type_of_function. f_equal; cbn.
        constructor; eauto. constructor.
      * constructor; eauto. eapply genv_funct_symbol; eauto.
    + eexists. split.
      * econstructor; eauto.
        eapply genv_funct_symbol; eauto. reflexivity.
        unfold type_of_function. f_equal; cbn.
        constructor; eauto.
      * constructor; eauto. eapply genv_funct_symbol; eauto.
  - intros. inv H1. inv H.
    eexists. split. constructor. constructor; eauto.
  - intros. inv H1; inv H.
    (* inc1 *)
    + eexists tt, _.  split. 2: split.
      * econstructor; eauto.
        eapply genv_funct_symbol; eauto. reflexivity.
      * assert (b = b0). cbn in *. congruence.
        subst. constructor; eauto.
      * split. constructor. intros. inv H. inv H1.
        eexists. split; constructor; eauto.
    (* inc2 *)
    + eexists tt, _.  split. 2: split.
      * econstructor; eauto.
        eapply genv_funct_symbol; eauto. reflexivity.
      * assert (b = b0).  cbn in *. congruence.
        subst. constructor; eauto.
      * split. constructor. intros. inv H. inv H1.
        eexists. split; constructor; eauto.
    (* get *)
    + eexists tt, _.  split. 2: split.
      * econstructor; eauto.
        eapply genv_funct_symbol; eauto. reflexivity.
      * assert (b = b0). cbn in *. congruence.
        subst. constructor; eauto.
      * split. constructor. intros. inv H. inv H1.
        eexists. split. econstructor; eauto.
        econstructor. 4: reflexivity. all: eauto.
    (* set *)
    + eexists tt, _.  split. 2: split.
      * econstructor; eauto.
        eapply genv_funct_symbol; eauto. reflexivity.
      * assert (b = b0). cbn in *. congruence.
        subst. constructor; eauto.
      * split. constructor. intros. inv H. inv H1.
        eexists. split. econstructor; eauto.
        econstructor; eauto.
  - intros. inv H1; inv H.
    (* enq: from initial to call inc2 *)
    + exploit inc2_block; eauto. intros (b1 & A & B).
      eexists. split.
      * eapply plus_left. constructor; eauto.
        {
          constructor; repeat constructor.
          intros x. inv x. solve_list_disjoint. eauto.
        }
        lts_step. crush_step.
        lts_step. crush_step; crush_expr.
        apply star_refl. reflexivity.
      * econstructor; eauto.
    (* deq: from initial to call inc1 *)
    + exploit inc1_block; eauto. intros (b1 & A & B).
      eexists. split.
      * eapply plus_left. constructor; eauto.
        { constructor; repeat constructor. solve_list_disjoint. eauto. }
        lts_step. crush_step.
        lts_step. crush_step; crush_expr.
        apply star_refl. reflexivity.
      * econstructor; eauto.
    (* enq: after inc2, call set *)
    + exploit set_block; eauto. intros (b1 & A & B).
      eexists. split.
      * eapply plus_left. constructor; eauto.
        lts_step. crush_step.
        lts_step. crush_step.
        lts_step. crush_step; crush_expr.
        apply star_refl. reflexivity.
      * econstructor; eauto.
    (* deq: after inc1, call get *)
    + exploit get_block; eauto. intros (b1 & A & B).
      eexists. split.
      * eapply plus_left. constructor; eauto.
        lts_step. crush_step.
        lts_step. crush_step.
        lts_step. crush_step; crush_expr.
        apply star_refl. reflexivity.
      * econstructor; eauto.
    (* enq: to final state *)
    + eexists. split.
      * eapply plus_left. constructor.
        lts_step. crush_step.
        lts_step. crush_step; crush_expr.
        apply star_refl. reflexivity.
      * constructor. eauto.
    (* deq: to final state *)
    + eexists. split.
      * eapply plus_left. constructor.
        lts_step. crush_step.
        lts_step. crush_step; crush_expr.
        apply star_refl. reflexivity.
      * constructor. eauto.
  - apply well_founded_ltof.
Qed.

Definition bq_espec: li_c +-> li_c := semantics_embed bq_spec.

Lemma bq_correct: E.forward_simulation (&1) (&1) bq_espec (eclightp bq_program).
Proof.
  rewrite ccref_left_unit1 at 2.
  rewrite <- ccref_left_unit2 at 1.
  eapply encap_fsim_vcomp.
  instantiate (1 := comp_esem'
                      (semantics_embed (id_semantics (skel bq_spec)))
                      bq_espec (skel bq_spec)).
  (* TODO: we need a lemma here *)
  - rewrite ccref_left_unit1 at 2.
    rewrite <- ccref_left_unit2 at 1.
    eapply encap_fsim_vcomp; eauto.
    instantiate (1 := semantics_embed _).
    + apply encap_fsim_embed_cat.
      apply left_unit_1'.
    + unfold left_comp_id'.
      apply encap_comp_embed2.
  - eapply encap_fsim_lcomp_sk. instantiate (1 := &bq_cc).
    + apply bq_correct1.
    + apply encap_fsim_embed.
      apply bq_correct2.
    + apply Linking.linkorder_refl.
    + apply Linking.linkorder_refl.
Qed.

(** ------------------------------------------------------------------------- *)
(** Abstract Ring Buffer Spec *)

Definition bq_state : Type := list Values.val.

Inductive bq_abs_state: Type :=
| bq_abs_init: forall (sig: bq_sig) (s: bq_state) (vs: list Values.val) (m: mem), bq_abs_state
| bq_abs_final: forall (s: bq_state) (v: Values.val) (m: mem), bq_abs_state.

Section BQ_LTS.

  Variable ge:  genv.

  Inductive bq_abs_initial_state: c_query * bq_state -> bq_abs_state -> Prop :=
  | abs_initial_state_enq: forall vf b v m bqst sig (HFLAG: Mem.alloc_flag m = true),
      vf = Vptr b Integers.Ptrofs.zero ->
      Genv.find_symbol ge enq_id = Some b ->
      Ple (Genv.genv_next ge) (Mem.nextblock m) ->
      Cop.val_casted v tint ->
      sig = enq_sg ->
      bq_abs_initial_state (cq vf sig [v] m, bqst) (bq_abs_init enq bqst [v] m)
  | abs_initial_state_deq: forall vf b m bqst sig (HFLAG: Mem.alloc_flag m = true),
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

Existing Instance clightp_linker.
Import Linking.

Section REFINE.

  Transparent Linker_prog.

  (* TODO: fix the manual proof *)
  (* I messed up the notations. I guess it's because my improper use of & *)
  Lemma rb_bq_linking:
    (* { cprog  & Linking.link bq_program rb_program = Some cprog }. *)
    sigT (fun cprog => link bq_program rb_program = Some cprog).
  Proof.
    cbn. unfold link_program.
    cbn -[list_norepet_dec]. unfold link_prog.
    assert (link_main_check (AST.prog_main bq_program) (AST.prog_main rb_program)
            && PTree_Properties.for_all
                 (prog_defmap bq_program)
                 (link_prog_check bq_program rb_program) = true).
    {
      apply andb_true_intro. split.
      - apply link_main_reflect. constructor. reflexivity.
      - rewrite PTree_Properties.for_all_correct.
        intros x a H.
        unfold link_prog_check, prog_defmap in *.
        apply PTree_Properties.in_of_list in H. cbn in H.
        destruct H as [|[|[|[|[|[|]]]]]]; inv H.
        all: reflexivity.
    }
    rewrite H.
    destruct link_build_composite_env. destruct a.
    destruct list_norepet_dec eqn: Hx. destruct a.
    - eexists. reflexivity.
    - clear - n. exfalso. apply n. clear n. cbn.
      Ltac rewrite_gso :=
        lazymatch goal with
        | [ H: context[PTree.get ?x (PTree.set ?y _ _)] |- _ ] =>
            rewrite PTree.gso in H by (unfold x, y; lia); eauto
        end.
      constructor.
      {
        intros H.
        destruct H. unfold cnt1_id, arr_id in H. lia.
        destruct H. unfold cnt2_id, arr_id in H. lia.
        apply in_map_iff in H as ((id & p) & Hp & Hq).
        cbn in *. subst.
        apply PTree.elements_complete in Hq.
        rewrite PTree.gcombine in Hq by reflexivity.
        repeat rewrite_gso.
        rewrite !PTree.gempty in Hq. inv Hq.
      }
      constructor.
      {
        intros H.
        destruct H. unfold cnt1_id, cnt2_id in H. lia.
        apply in_map_iff in H as ((id & p) & Hp & Hq).
        cbn in *. subst.
        apply PTree.elements_complete in Hq.
        rewrite PTree.gcombine in Hq by reflexivity.
        repeat rewrite_gso.
        rewrite !PTree.gempty in Hq. inv Hq.
      }
      constructor.
      {
        intros H.
        apply in_map_iff in H as ((id & p) & Hp & Hq).
        cbn in *. subst.
        apply PTree.elements_complete in Hq.
        rewrite PTree.gcombine in Hq by reflexivity.
        repeat rewrite_gso.
        rewrite !PTree.gempty in Hq. inv Hq.
      }
      apply PTree.elements_keys_norepet.
  Qed.

  Opaque link_program linkorder_program clightp_linker.

  Definition rb_bq_prog := projT1 rb_bq_linking.
  Definition rb_bq_skel := clightp_erase_program rb_bq_prog.

  Lemma bq_linkorder: linkorder bq_program rb_bq_prog.
  Proof.
    unfold rb_bq_prog.
    pose proof (projT2 rb_bq_linking). cbn in *.
    apply link_linkorder in H. apply H.
  Qed.

  Lemma rb_linkorder: linkorder rb_program rb_bq_prog.
  Proof.
    unfold rb_bq_prog.
    pose proof (projT2 rb_bq_linking). cbn in *.
    apply link_linkorder in H. apply H.
  Qed.

  Definition abs_bq_spec: semantics li_c (li_c@bq_state) :=
    {|
      skel := clightp_erase_program rb_bq_prog;
      activate se := abs_bq_lts (ClightP.globalenv se rb_bq_prog);
      footprint := fun i => footprint_of_program bq_program i
                         \/ footprint_of_program rb_program i;
    |}.

  Instance bq_state_pset : PSet bq_state :=
    { pset_init _ := nil; }.

  Definition abs_bq_espec : li_c +-> li_c :=
    comp_esem'
      (encap_prim bq_state (skel abs_bq_spec))
      (semantics_embed abs_bq_spec)
      rb_bq_skel.

  Open Scope nat_scope.

  Fixpoint slice (f : nat -> Values.val) (i : nat) (n : nat) : list Values.val :=
    match n with
    | O => nil
    | S n' => f i :: slice f (S i mod N) n'
    end.

  Inductive rb_bq : bq_state -> rb_state -> Prop :=
    bq_rb_intro f c1 c2 n q :
      c1 < N ->
      n <= N ->
      q = slice f c1 n ->
      c2 = (c1 + n) mod N ->
      (forall i, Cop.val_casted (f i) tint) ->
      rb_bq q (f, c1, c2).

  Import Relators.

  Program Definition abs_bq_cc: callconv (li_c@bq_state) (li_c@rb_state) :=
    {|
      ccworld := unit;
      match_senv _ := Logic.eq;
      match_query _ := (Logic.eq * rb_bq)%rel;
      match_reply _ := (Logic.eq * rb_bq)%rel;
    |}.
  Next Obligation. reflexivity. Qed.
  Next Obligation. inv H0. cbn in *. subst. reflexivity. Qed.
  Next Obligation. inv H. cbn in *. subst. reflexivity. Qed.

  Definition bq_rb_spec :=
    CategoricalComp.comp_semantics' (bq_spec @ rb_state) rb_spec rb_bq_skel.
  Definition bq_rb_espec :=
    comp_esem' (encap_prim rb_state rb_bq_skel) (semantics_embed bq_rb_spec) rb_bq_skel.

  Inductive bq_abs_ms se: bq_abs_state -> comp_state (bq_spec @ rb_state) rb_spec -> Prop :=
  | bq_abs_ms_enq:
    forall m v rbst bqst
      (HR: rb_bq bqst rbst)
      (HB: Ple (Genv.genv_next se) (Mem.nextblock m))
      (HV: Cop.val_casted v tint) (HFLAG: Mem.alloc_flag m = true),
      bq_abs_ms se  (bq_abs_init enq bqst [v] m)
        (st1 (bq_spec @ rb_state) _ (bq_init enq [v] m, rbst))
  | bq_abs_ms_deq:
    forall m rbst bqst
      (HR: rb_bq bqst rbst)
      (HB: Ple (Genv.genv_next se) (Mem.nextblock m)) (HFLAG: Mem.alloc_flag m = true),
      bq_abs_ms se (bq_abs_init deq bqst nil m)
        (st1 (bq_spec @ rb_state) _ (bq_init deq nil m, rbst))
  | bq_abs_ms_final:
    forall rv m bqst rbst
      (HR: rb_bq bqst rbst) (HFLAG: Mem.alloc_flag m = true),
      bq_abs_ms se (bq_abs_final bqst rv m)
        (st1 (bq_spec @ rb_state) _ (bq_final rv m, rbst)).

  Section BQ.

    Inductive refine_ms:
      Smallstep.state (encap_prim bq_state rb_bq_skel) ->
      Smallstep.state (encap_prim rb_state rb_bq_skel) -> Prop :=
    | refine_ms_q q rbst bqst:
      rb_bq bqst rbst ->
      refine_ms (@st_q (li_c@bq_state) (q, bqst))
        (@st_q (li_c@rb_state) (q, rbst))
    | refine_ms_r r rbst bqst:
      rb_bq bqst rbst ->
      refine_ms (@st_r (li_c@bq_state) (r, bqst))
        (@st_r (li_c@rb_state) (r, rbst)).

    Hint Constructors refine_ms.

    Lemma bq_refine1:
      E.forward_simulation (&abs_bq_cc) (&1)
        (encap_prim bq_state rb_bq_skel) (encap_prim rb_state rb_bq_skel).
    Proof.
      apply st_normalize_fsim. constructor.
      eapply ST.Forward_simulation with
        (ltof _ (fun (_: unit) => 0%nat))
        (fun _ _ _ _ _ _ s1 s2 => refine_ms s1 s2)
        (fun _ '(_, (bqst, rbst)) => rb_bq bqst rbst); try easy.
      - intros. cbn in *. eprod_crush. eauto.
      - intros. cbn.
        eapply bq_rb_intro with (n := 0).
        all: eauto; unfold N; lia.
      - intros; constructor; intros; cbn in *; eprod_crush.
        + inv H4. eexists tt, _. split. constructor.
          eexists tt, (tt, (_, _)). repeat split; eauto.
        + inv H3. inv H2. eexists (_, _). split. constructor.
          eexists (tt, (_, _)). repeat split; eauto.
        + inv H3. inv H2. eexists (_, _). split. constructor.
          exists tt, tt. repeat split; eauto.
          eprod_crush. cbn in *. inv H3.
          eexists _. split. constructor.
          eexists tt, (tt, (_, _)). repeat split; eauto.
        + easy.
          Unshelve. all: eauto.
    Qed.

  End BQ.

  Lemma rb_bq_c2:
    forall q f c1 c2, rb_bq q (f, c1, c2) -> c2 < N.
  Proof. intros. inv H. apply Nat.mod_upper_bound. unfold N. lia. Qed.

  Lemma refine_correct1:
    forall v vs f c1 c2,
      rb_bq (v :: vs) (f, c1, c2) ->
      v = f c1 /\ rb_bq vs (f, S c1 mod N, c2).
  Proof.
    intros. inv H. destruct n as [|m]. easy.
    inv H6. split. easy.
    eapply bq_rb_intro with (n := m); eauto.
    - apply Nat.mod_upper_bound. unfold N. lia.
    - apply le_Sn_le; eauto.
    - rewrite Nat.add_mod_idemp_l.
      f_equal. lia. unfold N. lia.
  Qed.

  Lemma slice_length f c1 n :
    List.length (slice f c1 n) = n.
  Proof. revert c1. induction n; cbn; auto. Qed.

  Lemma mod_minus:
    forall a, N <= a < N * 2 -> a mod N = a - N.
  Proof.
    intros.
    rewrite Nat.mod_eq.
    cut (a / N = 1). intros. rewrite H0. lia.
    assert (exists b, a = b + 1 * N).
    exists (a - N). lia.
    destruct H0 as (b & Hb). rewrite Hb.
    rewrite Nat.div_add. subst.
    cut (b < N). intros.
    rewrite Nat.div_small. easy. easy. lia.
    unfold N. lia. unfold N. lia.
  Qed.

  Lemma mod_add_not_same a b:
    a < N -> b < N -> b <> 0 -> (a + b) mod N <> a.
  Proof.
    intros. intros X.
    cut (a <> 0).
    2: { intros ->. cbn in *. apply Nat.mod_small in H0. lia. }
    intros Y.
    cut (a + b < N \/ N <= a + b < N * 2). intros [A|A].
    rewrite Nat.mod_small in X; try easy. lia.
    rewrite mod_minus in X; try easy. lia.
    destruct (lt_dec (a+b) N). lia. lia.
  Qed.

  Lemma refine_correct2:
    forall v vs f c1 c2,
      List.length vs < N ->
      Cop.val_casted v tint ->
      rb_bq vs (f, c1, c2) ->
      rb_bq (vs++[v]) (fun j : nat => if Nat.eq_dec c2 j then v else f j, c1, S c2 mod N).
  Proof.
    intros. inv H1. apply le_lt_or_eq in H6 as [A|A].
    - eapply bq_rb_intro with (n := S n); eauto.
      + clear - H5 A. revert c1 H5. induction n; cbn; intros.
        * destruct Nat.eq_dec. reflexivity. exfalso. apply n.
          rewrite Nat.add_0_r. now apply Nat.mod_small.
        * rewrite IHn.
          -- cbn. f_equal.
             ++ destruct Nat.eq_dec; try easy.
                exfalso. eapply mod_add_not_same. apply H5. apply A. easy. apply e.
             ++ replace ((S c1 mod N + n) mod N) with ((c1 + S n) mod N). easy.
                change (S ?x) with (1 + x).
                rewrite Nat.add_mod_idemp_l. f_equal. lia.
                unfold N. lia.
          -- apply Nat.lt_succ_l. auto.
          -- apply Nat.mod_upper_bound. unfold N. lia.
      + change (S ?x) with (1 + x).
        rewrite Nat.add_mod_idemp_r. f_equal. lia.
        unfold N. lia.
      + intros. destruct Nat.eq_dec; eauto.
    - rewrite slice_length in H. lia.
  Qed.

  Opaque clightp2.
  Import CategoricalComp.

  Lemma bq_refine2:
    forward_simulation 1 abs_bq_cc abs_bq_spec bq_rb_spec.
  Proof.
    constructor. econstructor. reflexivity. firstorder.
    intros. instantiate (1 := fun _ _ _ => _). cbn beta.
    destruct H. destruct wB.
    eapply forward_simulation_plus with (match_states := bq_abs_ms se1).
    - intros. cbn in *. eprod_crush. cbn in *. inv H1.
      + eexists. split.
        * econstructor.  instantiate (1 := (_, _)).
          constructor; cbn. econstructor; eauto. reflexivity.
        * econstructor; eauto.
      + eexists. split.
        * econstructor.  instantiate (1 := (_, _)).
          constructor; cbn. econstructor; eauto. reflexivity.
        * econstructor; eauto.
    - intros. inv H; inv H1.
      eexists (_, _). split; repeat constructor. eauto.
    - intros. inv H1.
    - intros. inv H1; inv H.
      (* enq *)
      + exploit (inc2_block se1). cbn in *.
        eapply Genv.valid_for_linkorder; eauto.
        apply linkorder_erase. apply bq_linkorder.
        intros (b1 & A & B).
        exploit (set_block se1).
        eapply Genv.valid_for_linkorder; eauto.
        apply linkorder_erase. apply bq_linkorder.
        intros (b2 & C & D).
        destruct rbst as [[f c1] c2].
        eexists. split.
        * eapply plus_left. cbn. constructor.
          { instantiate (1 := (_, _)). constructor; eauto. constructor. }
          lts_step.
          {
            eapply step_push.
            - instantiate (1 := (_, _)).  constructor; cbn.
              econstructor; eauto. eauto.
            - eapply initial_state_inc2; eauto.
          }
          lts_step.
          { apply step2. constructor. reflexivity. }
          lts_step.
          {
            eapply step_pop.
            - constructor.
            - instantiate (1 := (_, _)). constructor; cbn.
              constructor. constructor. cbn. reflexivity. reflexivity.
          }
          lts_step.
          { apply step1. instantiate (1 := (_, _)).
            constructor; eauto. constructor. }
          lts_step.
          {
            eapply step_push.
            - instantiate (1 := (_, _)).  constructor; cbn.
              econstructor; eauto. eauto.
            - econstructor; eauto.
          }
          lts_step.
          { eapply step2. constructor; eauto. eapply rb_bq_c2; eauto. }
          lts_step.
          {
            eapply step_pop.
            - constructor.
            - instantiate (1 := (_, _)). constructor; cbn.
              constructor. reflexivity.
          }
          lts_step.
          { eapply step1. instantiate (1 := (_, _)). repeat constructor. }
          apply star_refl. reflexivity.
        * constructor; eauto. now apply refine_correct2.
      (* deq *)
      + exploit (inc1_block se1).
        eapply Genv.valid_for_linkorder; eauto.
        apply linkorder_erase. apply bq_linkorder.
        intros (b1 & A & B).
        exploit (get_block se1).
        eapply Genv.valid_for_linkorder; eauto.
        apply linkorder_erase. apply bq_linkorder.
        intros (b2 & C & D).
        destruct rbst as [[f c1] c2].
        eexists. split.
        * eapply plus_left. cbn. constructor.
          { instantiate (1 := (_, _)). constructor; eauto. constructor. }
          lts_step.
          {
            eapply step_push.
            - instantiate (1 := (_, _)).  constructor; cbn.
              econstructor; eauto. eauto.
            - eapply initial_state_inc1; eauto.
          }
          lts_step.
          { eapply step2. constructor. reflexivity. }
          lts_step.
          {
            eapply step_pop.
            - constructor.
            - instantiate (1 := (_, _)). constructor; cbn.
              constructor. constructor. cbn. reflexivity. reflexivity.
          }
          lts_step.
          { apply step1. instantiate (1 := (_, _)).
            constructor; eauto. constructor. }
          lts_step.
          {
            eapply step_push.
            - instantiate (1 := (_, _)).  constructor; cbn.
              econstructor; eauto. eauto.
            - econstructor; eauto.
          }
          lts_step.
          { eapply step2. constructor. reflexivity. inv HR; eauto. }
          lts_step.
          {
            eapply step_pop.
            - constructor.
            - instantiate (1 := (_, _)). constructor; cbn.
              constructor. inv HR. apply H8. reflexivity.
          }
          lts_step.
          { eapply step1. instantiate (1 := (_, _)). repeat constructor. }
          apply star_refl. reflexivity.
        * eapply refine_correct1 in HR as [X Y]. subst.
          constructor; eauto. 
    - apply well_founded_ltof.
  Qed.

  Lemma spec_assoc {U: Type} `{PSet U} (L1: semantics li_c (li_c@U))
    (L2: semantics li_c li_c) sk1 sk2 sk sk_prim1 sk_prim2:
    linkorder sk1 sk ->
    linkorder (skel L1) sk ->
    linkorder sk_prim1 sk ->
    linkorder sk_prim2 sk ->
    E.forward_simulation (&1) (&1)
      (comp_esem' (encap_prim U sk_prim1)
         (semantics_embed (comp_semantics' (L2 @ U) L1 sk1)) sk)
      (comp_esem' (semantics_embed L2)
         (comp_esem' (encap_prim U sk_prim2) (semantics_embed L1) sk2) sk).
  Proof.
    intros SK1 SK2.
    etransitivity. 2: apply encap_assoc2.
    etransitivity.
    { eapply encap_fsim_lcomp_sk; eauto.
      - reflexivity.
      - apply encap_comp_embed2. }
    etransitivity. apply encap_assoc1.
    eapply encap_fsim_lcomp_sk.
    - apply encap_comp_prim.
    - reflexivity.
    - apply H1.
    - eauto.
  Qed.

  Lemma bq_refine:
    E.forward_simulation
      (&1) (&1) abs_bq_espec (comp_esem' bq_espec rb_espec rb_bq_skel).
  Proof.
    etransitivity.
    instantiate (1 := bq_rb_espec).
    - eapply encap_fsim_lcomp_sk.
      instantiate (1 := &abs_bq_cc).
      + apply bq_refine1.
      + apply encap_fsim_embed.
        apply bq_refine2.
      + apply linkorder_refl.
      + apply linkorder_refl.
    - apply spec_assoc. apply linkorder_refl.
      apply linkorder_erase. apply rb_linkorder.
      apply linkorder_refl.
      apply linkorder_erase. apply rb_linkorder.
  Qed.

  Lemma rb_bq_correct:
    E.forward_simulation
      (&1) (&1) abs_bq_espec
      (comp_esem' (eclightp bq_program) (eclightp rb_program) rb_bq_skel).
  Proof.
    rewrite (ccref_left_unit1 (&1)) at 2.
    rewrite <- ccref_left_unit2 at 1.
    eapply encap_fsim_vcomp.
    - apply bq_refine.
    - eapply encap_fsim_lcomp_sk.
      + apply bq_correct.
      + apply rb_correct.
      + apply linkorder_erase. apply bq_linkorder.
      + apply linkorder_erase. apply rb_linkorder.
  Qed.

  Context tbq trb (HT1: transl_program bq_program = Errors.OK tbq)
              (HT2: transl_program rb_program = Errors.OK trb).
  Let vars := vars_of_program bq_program ++ vars_of_program rb_program.
  Let ce := PTree.empty composite.

  Lemma rb_bq_correct_clight:
    E.forward_simulation
      (ST.cc_compose (&1) unp_out)
      (ST.cc_compose (&1) (unp_in ce vars))
      abs_bq_espec
      (comp_esem' (semantics_embed (semantics2 tbq))
         (semantics_embed (semantics2 trb)) rb_bq_skel).
  Proof.
    eapply encap_fsim_vcomp. apply rb_bq_correct.
    apply clightp_comp; eauto.
    cbn. intros x y [].
    unfold rb_bq_prog. destruct rb_bq_linking.
    apply e.
  Qed.

End REFINE.

Module BQ.
  Import Clight.

  (**
<<
    void enq(int v) {
      int i = inc2();
      set(i, v);
    }
>>
   *)
  Definition bq_enq_body : Clight.statement :=
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

  Program Definition bq_program : program :=
    {|
      Ctypes.prog_defs :=
        PTree.elements (
            PTree.set set_id (Gfun set_ext)
              (PTree.set get_id (Gfun get_ext)
                 (PTree.set inc2_id (Gfun inc2_ext)
                    (PTree.set inc1_id (Gfun inc1_ext)
                       (PTree.set deq_id (Gfun (Internal bq_deq))
                          (PTree.set enq_id (Gfun (Internal bq_enq)) (PTree.empty (globdef fundef type))))))));
        (* [(enq_id, Gfun (Internal bq_enq)); *)
        (*  (deq_id, Gfun (Internal bq_deq)); *)
        (*  (inc1_id, Gfun inc1_ext); *)
        (*  (inc2_id, Gfun inc2_ext); *)
        (*  (get_id, Gfun get_ext); *)
        (*  (set_id, Gfun set_ext)]; *)
      (* for linking purpose, external functions have to be public *)
      Ctypes.prog_public := [enq_id; deq_id; inc1_id; inc2_id; get_id; set_id];
      Ctypes.prog_main := Some 999%positive;
      Ctypes.prog_types := [];
      Ctypes.prog_comp_env := (PTree.empty _);
    |}.

Inductive bq_ms se: bq_internal_state -> state -> Prop :=
| bq_ms_enq:
  forall vf m v,
    Mem.alloc_flag m = true ->
    Cop.val_casted v tint ->
    Genv.find_funct (Genv.globalenv se bq_program) vf = Some (Internal bq_enq) ->
    bq_ms se (bq_init enq [v] m) (Callstate vf [v] Kstop m)
| bq_ms_deq:
  forall vf m,
    Mem.alloc_flag m = true ->
    Genv.find_funct (Genv.globalenv se bq_program) vf = Some (Internal bq_deq) ->
    bq_ms se (bq_init deq [] m) (Callstate vf [] Kstop m)
| bq_ms_call_inc1:
  forall vf k m b,
    Mem.alloc_flag m = true ->
    vf = Vptr b Integers.Ptrofs.zero ->
    Genv.find_symbol se inc1_id = Some b ->
    k = (Kcall (Some bq_deq_tmp1) bq_deq empty_env
          (PTree.Node (PTree.Node PTree.Empty (Some Vundef) PTree.Empty) (Some Vundef) PTree.Empty)
          (Kseq
             (Ssequence
                (Scall (Some bq_deq_tmp2) (Evar get_id (Tfunction (Tcons tint Tnil) tint cc_default))
                   [Etempvar bq_deq_tmp1 tint]) (Sreturn (Some (Etempvar bq_deq_tmp2 tint)))) Kstop)) ->
    bq_ms se (bq_call inc1 [] m) (Callstate vf [] k m)
| bq_ms_call_inc2:
  forall vf k m v b,
    Mem.alloc_flag m = true ->
    Cop.val_casted v tint ->
    vf = Vptr b Integers.Ptrofs.zero ->
    Genv.find_symbol se inc2_id = Some b ->
    k = (Kcall (Some bq_enq_tmp) bq_enq empty_env
          (PTree.Node (PTree.Node PTree.Empty (Some Vundef) PTree.Empty) (Some v) PTree.Empty)
          (Kseq
             (Ssequence
                (Scall None (Evar set_id (Tfunction (Tcons tint (Tcons tint Tnil)) tvoid cc_default))
                   [Etempvar bq_enq_tmp tint; Etempvar enq_arg_id tint]) (Sreturn None)) Kstop)) ->
    bq_ms se (bq_call inc2 [v] m) (Callstate vf [] k m)

| bq_ms_mid_enq:
  forall m v1 v2 k,
    Mem.alloc_flag m = true ->
    Cop.val_casted v1 tint ->
    Cop.val_casted v2 tint ->
    k = (Kcall (Some bq_enq_tmp) bq_enq empty_env
          (PTree.Node (PTree.Node PTree.Empty (Some Vundef) PTree.Empty) (Some v2) PTree.Empty)
          (Kseq
             (Ssequence
                (Scall None (Evar set_id (Tfunction (Tcons tint (Tcons tint Tnil)) tvoid cc_default))
                   [Etempvar bq_enq_tmp tint; Etempvar enq_arg_id tint]) (Sreturn None)) Kstop)) ->
    bq_ms se (bq_middle enq [v1; v2] m) (Returnstate v1 k m)
| bq_ms_mid_deq:
  forall m v k,
    Mem.alloc_flag m = true ->
    Cop.val_casted v tint ->
    k = (Kcall (Some bq_deq_tmp1) bq_deq empty_env
          (PTree.Node (PTree.Node PTree.Empty (Some Vundef) PTree.Empty) (Some Vundef) PTree.Empty)
          (Kseq
             (Ssequence
                (Scall (Some bq_deq_tmp2) (Evar get_id (Tfunction (Tcons tint Tnil) tint cc_default))
                   [Etempvar bq_deq_tmp1 tint]) (Sreturn (Some (Etempvar bq_deq_tmp2 tint)))) Kstop)) ->
    bq_ms se (bq_middle deq [v] m) (Returnstate v k m)

| bq_ms_call_get:
  forall vf k m v b,
    Mem.alloc_flag m = true ->
    vf = Vptr b Integers.Ptrofs.zero ->
    Genv.find_symbol se get_id = Some b ->
    Cop.val_casted v tint ->
    k = (Kcall (Some bq_deq_tmp2) bq_deq empty_env
          (PTree.Node (PTree.Node PTree.Empty (Some Vundef) PTree.Empty) (Some v) PTree.Empty)
          (Kseq (Sreturn (Some (Etempvar bq_deq_tmp2 tint))) Kstop)) ->
    bq_ms se (bq_call geti [v] m) (Callstate vf [v] k m)
| bq_ms_call_set:
  forall vf k m v1 v2 b,
    Mem.alloc_flag m = true ->
    vf = Vptr b Integers.Ptrofs.zero ->
    Genv.find_symbol se set_id = Some b ->
    Cop.val_casted v1 tint ->
    Cop.val_casted v2 tint ->
    k = (Kcall None bq_enq empty_env (PTree.Node (PTree.Node PTree.Empty (Some v1) PTree.Empty) (Some v2) PTree.Empty) (Kseq (Sreturn None) Kstop)) ->
    bq_ms se (bq_call seti [v1; v2] m) (Callstate vf [v1; v2] k m)

| bq_ms_midx_enq:
  forall m v k le,
    Mem.alloc_flag m = true ->
    k = (Kcall None bq_enq empty_env le (Kseq (Sreturn None) Kstop)) ->
    bq_ms se (bq_middlex enq v m) (Returnstate v k m)
| bq_ms_midx_deq:
  forall m v rv k,
    Mem.alloc_flag m = true ->
    Cop.val_casted rv tint ->
    Cop.val_casted v tint ->
    k = (Kcall (Some bq_deq_tmp2) bq_deq empty_env
          (PTree.Node (PTree.Node PTree.Empty (Some Vundef) PTree.Empty) (Some v) PTree.Empty)
          (Kseq (Sreturn (Some (Etempvar bq_deq_tmp2 tint))) Kstop)) ->
    bq_ms se (bq_middlex deq rv m) (Returnstate rv k m)

| bq_ms_final:
  forall rv m,
    Mem.alloc_flag m = true ->
    bq_ms se (bq_final rv m) (Returnstate rv Kstop m).

Lemma genv_funct_symbol se id b f (p: program):
  Genv.find_symbol se id = Some b ->
  (prog_defmap p) ! id = Some (Gfun f) ->
  Genv.find_funct (Clight.globalenv se p) (Vptr b Ptrofs.zero) = Some f.
Proof.
  intros H1 H2.
  unfold Genv.find_funct, Genv.find_funct_ptr.
  destruct Ptrofs.eq_dec; try congruence.
  apply Genv.find_invert_symbol in H1. cbn.
  rewrite Genv.find_def_spec. rewrite H1.
  rewrite H2. reflexivity.
Qed.

Lemma inc2_block se:
  Genv.valid_for (AST.erase_program bq_program) se ->
  exists b, Genv.find_symbol (globalenv se bq_program) inc2_id = Some b /\
         Genv.find_funct (globalenv se bq_program) (Vptr b zero) = Some inc2_ext.
Proof.
  intros Hse.
  edestruct (@Genv.find_def_symbol _ _ se bq_program inc2_id) as [(b & Hb1 & Hb2) ?]; eauto.
  reflexivity. exists b. split; eauto. eapply genv_funct_symbol; eauto.
Qed.

Lemma set_block se:
  Genv.valid_for (AST.erase_program bq_program) se ->
  exists b, Genv.find_symbol (globalenv se bq_program) set_id = Some b /\
         Genv.find_funct (globalenv se bq_program) (Vptr b zero) = Some set_ext.
Proof.
  intros Hse.
  edestruct (@Genv.find_def_symbol _ _ se bq_program set_id) as [(b & Hb1 & Hb2) ?]; eauto.
  reflexivity. exists b. split; eauto. eapply genv_funct_symbol; eauto.
Qed.

Lemma inc1_block se:
  Genv.valid_for (AST.erase_program bq_program) se ->
  exists b, Genv.find_symbol (globalenv se bq_program) inc1_id = Some b /\
         Genv.find_funct (globalenv se bq_program) (Vptr b zero) = Some inc1_ext.
Proof.
  intros Hse.
  edestruct (@Genv.find_def_symbol _ _ se bq_program inc1_id) as [(b & Hb1 & Hb2) ?]; eauto.
  reflexivity. exists b. split; eauto. eapply genv_funct_symbol; eauto.
Qed.

Lemma get_block se:
  Genv.valid_for (AST.erase_program bq_program) se ->
  exists b, Genv.find_symbol (globalenv se bq_program) get_id = Some b /\
         Genv.find_funct (globalenv se bq_program) (Vptr b zero) = Some get_ext.
Proof.
  intros Hse.
  edestruct (@Genv.find_def_symbol _ _ se bq_program get_id) as [(b & Hb1 & Hb2) ?]; eauto.
  reflexivity. exists b. split; eauto. eapply genv_funct_symbol; eauto.
Qed.

Ltac crush_eval_expr :=
  cbn;
  lazymatch goal with
  | [ |- eval_expr _ _ _ _ (Etempvar _ _) _ ] => apply eval_Etempvar; reflexivity
  | [ |- eval_expr _ _ _ _ (Econst_int _ _) _ ] => apply eval_Econst_int
  | [ |- eval_expr _ _ _ _ (Ebinop _ _ _ _) _ ] => eapply eval_Ebinop
  | [ |- eval_expr _ _ _ _ (Evar _ _) _ ] => eapply eval_Elvalue
  | [ |- eval_expr _ _ _ _ (Ederef _ _) _ ] => eapply eval_Elvalue
  end.
Ltac crush_eval_lvalue :=
  cbn;
  lazymatch goal with
  | [ |- eval_lvalue _ _ _ _ (Evar _ _) _ _ _ ] =>
      solve [ apply eval_Evar_local; reflexivity
            | apply eval_Evar_global; [ reflexivity | eassumption ] ]
  | _ => constructor
  end.

Ltac crush_expr :=
  repeat (cbn;
    match goal with
    | [ |- eval_expr _ _ _ _ _ _  ] => crush_eval_expr
    | [ |- eval_lvalue _ _ _ _ _ _ _ _  ] => crush_eval_lvalue
    | [ |- eval_exprlist _ _ _ _ _ _ _  ] => econstructor
    | [ |- deref_loc _ _ _ _ _ _ ] => crush_deref
    | [ |- Cop.sem_binary_operation _ _ _ _ _ _ _ = Some _] => try reflexivity
    | [ |- Cop.sem_cast _ ?ty ?ty _ = Some _ ] =>
        apply Cop.cast_val_casted; eauto
    | [ |- assign_loc _ (Tint _ _ _) _ _ _ _ _ _ ] =>
        eapply assign_loc_value; [ reflexivity | ]
    | _ => try solve [ easy | eassumption ]
    end).

Ltac crush_step := cbn;
  match goal with
  | [ |- Step _ (Callstate _ _ _ _) _ _ ] =>
      eapply step_internal_function;
      [ eauto | constructor; cbn;
        [ solve_list_norepet
        | solve_list_norepet
        | solve_list_disjoint
        | repeat (econstructor; simpl; auto)
        | reflexivity | eauto ] ]
  | [ |- Step _ (State _ (Ssequence _ _) _ _ _ _) _ _ ] => apply step_seq
  | [ |- Step _ (State _ (Sset _ _) _ _ _ _) _ _ ] => apply step_set
  | [ |- Step _ (State _ (Scall _ _ _) _ _ _ _) _ _ ] => eapply step_call
  | [ |- Step _ (Returnstate _ _ _) _ _ ] => eapply step_returnstate
  | [ |- Step _ (State _ Sskip (Kseq _ _) _ _ _) _ _ ] => apply step_skip_seq
  | [ |- Step _ (State _ (Sassign _ _) _ _ _ _) _ _ ] => eapply step_assign
  | [ |- Step _ (State _ (Sreturn None) _ _ _ _) _ _ ] => eapply step_return_0
  | [ |- Step _ (State _ (Sreturn (Some _)) _ _ _ _) _ _ ] => eapply step_return_1
  | [ |- Step _ (State _ ?s _ _ _ _) _ _ ] => is_const s; unfold s; crush_step
  end.

Ltac lts_step := eapply star_left with (t1 := E0) (t2 := E0); [ | | reflexivity ].

  Lemma bq_correct0: forward_simulation 1 1 bq_spec (semantics2 bq_program).
  Proof.
    constructor. econstructor.
    { cbn. unfold clightp_erase_program, erase_program. f_equal. }
    {
      intros. cbn. unfold footprint_of_program.
      setoid_rewrite PTree_Properties.of_list_elements. cbn.
      destruct (peq i set_id). subst. rewrite !PTree.gss. reflexivity.
      rewrite PTree.gso; eauto. symmetry. rewrite PTree.gso; eauto.
      destruct (peq i get_id). subst. rewrite !PTree.gss. reflexivity.
      rewrite PTree.gso; eauto. symmetry. rewrite PTree.gso; eauto.
      destruct (peq i inc2_id). subst. rewrite !PTree.gss. reflexivity.
      rewrite PTree.gso; eauto. symmetry. rewrite PTree.gso; eauto.
      destruct (peq i inc1_id). subst. rewrite !PTree.gss. reflexivity.
      rewrite PTree.gso; eauto. symmetry. rewrite PTree.gso; eauto.
      destruct (peq i deq_id). subst. rewrite !PTree.gss. reflexivity.
      rewrite PTree.gso; eauto. symmetry. rewrite PTree.gso; eauto.
      destruct (peq i enq_id). subst. rewrite !PTree.gss. reflexivity.
      rewrite PTree.gso; eauto. symmetry. rewrite PTree.gso; eauto.
      rewrite !PTree.gempty. reflexivity.
    }
    Local Opaque semantics2.
    intros. instantiate (1 := fun _ _ _ => _). cbn beta.
    destruct H.
    eapply forward_simulation_plus with (match_states := bq_ms se1).
    - intros. cbn in *. eprod_crush. inv H1.
      + eexists. split.
        * econstructor; eauto.
          eapply genv_funct_symbol; eauto. reflexivity.
          unfold type_of_function. f_equal; cbn.
          constructor; eauto. constructor.
        * constructor; eauto. eapply genv_funct_symbol; eauto.
      + eexists. split.
        * econstructor; eauto.
          eapply genv_funct_symbol; eauto. reflexivity.
          unfold type_of_function. f_equal; cbn.
          constructor; eauto.
        * constructor; eauto. eapply genv_funct_symbol; eauto.
    - intros. inv H1. inv H.
      eexists. split. constructor. constructor; eauto.
    - intros. inv H1; inv H.
      (* inc1 *)
      + eexists tt, _.  split. 2: split.
        * econstructor; eauto.
          eapply genv_funct_symbol; eauto. reflexivity.
        * assert (b = b0). cbn in *. congruence.
          subst. constructor; eauto.
        * split. constructor. intros. inv H. inv H1.
          eexists. split; constructor; eauto.
      (* inc2 *)
      + eexists tt, _.  split. 2: split.
        * econstructor; eauto.
          eapply genv_funct_symbol; eauto. reflexivity.
        * assert (b = b0).  cbn in *. congruence.
          subst. constructor; eauto.
        * split. constructor. intros. inv H. inv H1.
          eexists. split; constructor; eauto.
      (* get *)
      + eexists tt, _.  split. 2: split.
        * econstructor; eauto.
          eapply genv_funct_symbol; eauto. reflexivity.
        * assert (b = b0). cbn in *. congruence.
          subst. constructor; eauto.
        * split. constructor. intros. inv H. inv H1.
          eexists. split. econstructor; eauto.
          econstructor. 4: reflexivity. all: eauto.
      (* set *)
      + eexists tt, _.  split. 2: split.
        * econstructor; eauto.
          eapply genv_funct_symbol; eauto. reflexivity.
        * assert (b = b0). cbn in *. congruence.
          subst. constructor; eauto.
        * split. constructor. intros. inv H. inv H1.
          eexists. split. econstructor; eauto.
          econstructor; eauto.
    - intros. inv H1; inv H.
      (* enq: from initial to call inc2 *)
      + exploit inc2_block; eauto. intros (b1 & A & B).
        eexists. split.
        * eapply plus_left. constructor; eauto.
          {
            constructor; repeat constructor.
            intros x. inv x. solve_list_disjoint. eauto.
          }
          lts_step. crush_step.
          lts_step. crush_step; crush_expr.
          apply star_refl. reflexivity.
        * econstructor; eauto.
      (* deq: from initial to call inc1 *)
      + exploit inc1_block; eauto. intros (b1 & A & B).
        eexists. split.
        * eapply plus_left. constructor; eauto.
          { constructor; repeat constructor. solve_list_disjoint. eauto. }
          lts_step. crush_step.
          lts_step. crush_step; crush_expr.
          apply star_refl. reflexivity.
        * econstructor; eauto.
      (* enq: after inc2, call set *)
      + exploit set_block; eauto. intros (b1 & A & B).
        eexists. split.
        * eapply plus_left. constructor; eauto.
          lts_step. crush_step.
          lts_step. crush_step.
          lts_step. crush_step; crush_expr.
          apply star_refl. reflexivity.
        * econstructor; eauto.
      (* deq: after inc1, call get *)
      + exploit get_block; eauto. intros (b1 & A & B).
        eexists. split.
        * eapply plus_left. constructor; eauto.
          lts_step. crush_step.
          lts_step. crush_step.
          lts_step. crush_step; crush_expr.
          apply star_refl. reflexivity.
        * econstructor; eauto.
      (* enq: to final state *)
      + eexists. split.
        * eapply plus_left. constructor.
          lts_step. crush_step.
          lts_step. crush_step; crush_expr.
          apply star_refl. reflexivity.
        * constructor. eauto.
      (* deq: to final state *)
      + eexists. split.
        * eapply plus_left. constructor.
          lts_step. crush_step.
          lts_step. crush_step; crush_expr.
          apply star_refl. reflexivity.
        * constructor. eauto.
    - apply well_founded_ltof.
  Qed.

End BQ.

Inductive join_query : query (Lifting.lifted_li Mem.mem li_c) -> query li_c -> Prop :=
| join_query_intro vf sg vargs m msrc mtgt
    (MJOIN: Join.join m msrc mtgt):
  join_query (cq vf sg vargs msrc, m) (cq vf sg vargs mtgt).

Inductive join_reply: reply (Lifting.lifted_li Mem.mem li_c) -> reply li_c -> Prop :=
| join_reply_intro rv m msrc mtgt
    (MJOIN: Join.join m msrc mtgt):
  join_reply (cr rv msrc, m) (cr rv mtgt).

Program Definition join_cc : callconv (Lifting.lifted_li Mem.mem li_c) li_c :=
  {|
    ccworld := unit;
    match_senv _ se1 se2 := se1 = se2;
    match_query _ := join_query;
    match_reply _ := join_reply;
  |}.
Next Obligation. reflexivity. Qed.
Next Obligation. inv H0. reflexivity. Qed.
Next Obligation. inv H. reflexivity. Qed.

Section FRAME.
  Import Clight.
  Import Join.
  Context (p: program).
  Inductive join_ms : state * mem -> state -> Prop :=
  | clightp_ms_State:
    forall f s k e le mx m1 m2 (HJ: join mx m1 m2),
      join_ms (State f s k e le m1, mx) (State f s k e le m2)
  | join_ms_Callstate:
    forall vf args k mx m1 m2 (HJ: join mx m1 m2),
      join_ms (Callstate vf args k m1, mx) (Callstate vf args k m2)
  | join_ms_Returnstate:
    forall rv k mx m1 m2 (HJ: join mx m1 m2),
      join_ms (Returnstate rv k m1, mx) (Returnstate rv k m2).

  Lemma join_step ge mx:
    forall s1 t s1',
    Clight.step2 ge s1 t s1' ->
    forall s2, join_ms (s1, mx) s2 ->
    exists s2', Clight.step2 ge s2 t s2' /\
    join_ms (s1', mx) s2'.
  Proof with (eexists _; split; econstructor; eauto).
    induction 1; intros S1 HS; inv HS;
      try solve [ eexists _; split; econstructor; eauto ].
    - exploit clight_lvalue_join; eauto. intros A.
      exploit clight_expr_join; eauto. intros B.
      exploit sem_cast_join; eauto.
      rewrite H1. intros C. inv C.
      exploit assign_loc_join; eauto. intros (? & D & E)...
    - exploit clight_expr_join; eauto. intros A...
    - exploit clight_expr_join; eauto. intros A.
      exploit clight_exprlist_join; eauto; intros B...
    - exploit clight_exprlist_join; eauto. intros A.
      exploit ClightP.external_call_join; eauto. intros (? & B & C)...
    - exploit clight_expr_join; eauto. intros A.
      exploit bool_val_join; eauto.
      rewrite H0. intros B. inv B...
    - exploit free_list_join; eauto.
      rewrite H. intros A. inv A...
    - exploit clight_expr_join; eauto. intros A.
      exploit sem_cast_join; eauto.
      rewrite H0. intros B. inv B.
      exploit free_list_join; eauto.
      rewrite H1. intros C. inv C...
    - exploit free_list_join; eauto.
      rewrite H0. intros A. inv A...
    - exploit clight_expr_join; eauto. intros A...
    - exploit clight_function_entry_join; eauto. intros (? & A & B)...
    - exploit ClightP.external_call_join; eauto. intros (? & A & B)...
  Qed.

  Lemma fp :
    forward_simulation join_cc join_cc ((semantics2 p) @ mem) (semantics2 p).
  Proof.
    constructor. econstructor. reflexivity. firstorder.
    instantiate (1 := fun _ _ _ => _). cbn beta.
    intros se1 se2 w Hse Hse1. cbn -[semantics2] in *. subst se2.
    rename w into mx.
    eapply forward_simulation_step with (match_states := join_ms).
    - intros [q1 mq] q2 [s1 ms] Hq Hi. cbn in *. eprod_crush.
      inv Hq. inv H.
      eexists. split; econstructor; eauto.
      apply mjoin_nextblock in MJOIN.
      rewrite MJOIN. unfold Ple in *.
      etransitivity; eauto.
      apply Pos.le_max_r.
    - intros [s1 ms1] s2 [r1 mr1] Hjoin Hf.
      inv Hf. cbn in *. subst. inv H. inv Hjoin.
      eexists. split; constructor; eauto.
    - intros [s1 ms1] s2 [q1 mq1] Hjoin He.
      inv He. cbn in *. subst. inv H. inv Hjoin.
      eexists tt, _. repeat apply conj; eauto.
      + econstructor; eauto.
      + constructor; eauto.
      + intros [r1 mr1] r2 [s1' ms1'] Hjoin Hr.
        eprod_crush. inv H. inv Hjoin.
        eexists. split; constructor; eauto.
    - intros [s1 ms1] t [s1' ms1'] [HS <-] s2 Hjoin.
      eapply join_step; eauto.
    - apply well_founded_ltof.
  Qed.

End FRAME.

