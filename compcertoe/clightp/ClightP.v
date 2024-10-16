From compcert Require Import
     AST Coqlib Maps Values Integers Errors Events
     LanguageInterface Smallstep Globalenvs Memory Floats.
Require Import Ctypes Cop Clight.
Require Import Lia.
Require Import Join.
From compcert.clightp Require Import Lifting AbRel PEnv.

(** ------------------------------------------------------------------------- *)
Hypothesis external_call_join:
  forall ge m ef vargs m1 m2 t vres m1',
    join m m1 m2 ->
    external_call ef ge vargs m1 t vres m1' ->
    exists m2', external_call ef ge vargs m2 t vres m2' /\ join m m1' m2'.

(** ------------------------------------------------------------------------- *)
(** PTree properties *)
Lemma ptree_of_list1 {A} k l m:
  In k (map fst l) ->
  (fold_left (fun m k_v => PTree.set (fst k_v) (snd k_v) m) l m) ! k =
    (fold_left (fun m k_v => PTree.set (fst k_v) (snd k_v) m) l (PTree.empty A)) ! k.
Proof.
  revert k l m. induction l as [ | [k1 v1] l]; simpl; intros. inv H.
  destruct H; subst.
  + destruct (ListDec.In_dec PTree.elt_eq k (map fst l)).
    * rewrite (IHl (PTree.set k v1 (PTree.empty A))); eauto.
    * rewrite !PTree_Properties.of_list_unchanged; eauto.
      rewrite !PTree.gss. reflexivity.
  + rewrite (IHl (PTree.set k1 v1 (PTree.empty A))); eauto.
Qed.

Lemma ptree_of_list2 {A} k l (m: PTree.tree A):
  ~In k (map fst l) ->
  (fold_left (fun m k_v => PTree.set (fst k_v) (snd k_v) m) l m) ! k = m ! k.
Proof.
  revert k l m. induction l as [ | [k1 v1] l]; simpl; intros. reflexivity.
  apply Classical_Prop.not_or_and in H as [H1 H2].
  rewrite IHl; eauto. rewrite PTree.gso; eauto.
Qed.

Lemma ptree_of_list_app {A} xs ys i (v: A):
  (PTree_Properties.of_list ys) ! i = Some v ->
  (PTree_Properties.of_list (xs ++ ys)) ! i = Some v.
Proof.
  intros H.
  exploit PTree_Properties.in_of_list; eauto. intros HIN.
  rewrite <- H.
  unfold PTree_Properties.of_list.
  rewrite fold_left_app.
  rewrite ptree_of_list1. reflexivity.
  apply in_map_iff. exists (i, v). split; eauto.
Qed.

Lemma ptree_of_list_app_none {A} (xs: list (PTree.elt * A)) ys i:
  (PTree_Properties.of_list ys) ! i = None ->
  (PTree_Properties.of_list (xs ++ ys)) ! i = (PTree_Properties.of_list xs) ! i.
Proof.
  intros H.
  assert (~ In i (map fst ys)).
  {
    intros contra. apply PTree_Properties.of_list_dom in contra.
    destruct contra as (v & Hv). congruence.
  }
  unfold PTree_Properties.of_list.
  rewrite fold_left_app.
  rewrite ptree_of_list2; eauto.
Qed.

Lemma ptree_of_list_map {A B} (xs: list (ident * A)) (f: A -> B) id:
  (PTree_Properties.of_list (map (fun '(id, x) => (id, f x)) xs)) ! id =
    (option_map f ((PTree_Properties.of_list xs) ! id)).
Proof.
  induction xs. reflexivity. destruct a as (i & a).
  destruct (ListDec.In_dec peq id (map fst xs)).
  - cbn. setoid_rewrite ptree_of_list1; eauto.
    apply in_map_iff in i0 as ((ix & v) & Hv1 & Hv2).
    apply in_map_iff. eexists (_, _). split; eauto.
    apply in_map_iff. eexists (_, _). split; eauto.
  - cbn. setoid_rewrite ptree_of_list2; eauto.
    + destruct (peq id i).
      * subst. rewrite !PTree.gss. reflexivity.
      * rewrite !PTree.gso; eauto.
    + intros x. apply n.
      apply in_map_iff in x as ((j & v) & Hv1 & Hv2).
      apply in_map_iff in Hv2 as ((k & u) & Hu1 & Hu2).
      subst. inv Hu1. cbn.
      apply in_map_iff. eexists (_, _). split; eauto. reflexivity.
Qed.

Lemma ptree_elements_map {A B} (xs: list (ident * A)) (f: A -> B):
  map (fun '(id, x) => (id, f x))
    (PTree.elements (PTree_Properties.of_list xs)) =
    (PTree.elements
       (PTree_Properties.of_list
          (map (fun '(id, x) => (id, f x)) xs))).
Proof.
  set (R := fun a b => f a = b).
  remember (PTree_Properties.of_list xs) as t1.
  remember (PTree_Properties.of_list
                           (map (fun '(id, x) => (id, f x)) xs)) as t2.
  assert (list_forall2
            (fun (i_x : positive * A) (i_y : positive * B) =>
               fst i_x = fst i_y /\ R (snd i_x) (snd i_y))
            (PTree.elements t1) (PTree.elements t2)).
  {
    apply PTree.elements_canonical_order'.
    intros id.
    destruct (t1 ! id) eqn: Ht1; destruct (t2 ! id) eqn: Ht2;
      subst R; subst; cbn in *.
    - constructor. rewrite ptree_of_list_map in Ht2.
      rewrite Ht1 in Ht2. cbn in Ht2. congruence.
    - exfalso. rewrite ptree_of_list_map in Ht2.
      rewrite Ht1 in Ht2. cbn in Ht2. congruence.
    - exfalso. rewrite ptree_of_list_map in Ht2.
      rewrite Ht1 in Ht2. cbn in Ht2. congruence.
    - constructor.
  }
  remember (PTree.elements t1) as l1.
  remember (PTree.elements t2) as l2.
  clear Heqt1 Heqt2 Heql1 Heql2.
  induction H. reflexivity.
  destruct a1 as (i1, a1). cbn in *.
  destruct H. subst. f_equal.
  subst R. cbn in H1. destruct b1. f_equal. easy.
Qed.

Lemma of_list_not_in {A} (xs : list (ident * A)) k:
  ~In k (map fst xs) -> (PTree_Properties.of_list xs) ! k = None.
Proof.
  intros H.
  destruct (lift_option ((PTree_Properties.of_list xs) ! k))
    as [[s Hs]|].
  - exfalso. apply PTree_Properties.in_of_list in Hs.
    apply H. apply in_map_iff.
    eexists (k, _). split; eauto.
  - eauto.
Qed.

(** ------------------------------------------------------------------------- *)
(** ** ClightP semantics *)
Module ClightP.

  Hypothesis val_init_data: val -> list init_data.

  Inductive expr : Type :=
  | Econst_int: int -> type -> expr       (**r integer literal *)
  | Econst_float: float -> type -> expr   (**r double float literal *)
  | Econst_single: float32 -> type -> expr (**r single float literal *)
  | Econst_long: int64 -> type -> expr    (**r long integer literal *)
  | Evar: ident -> type -> expr           (**r variable *)
  | Etempvar: ident -> type -> expr       (**r temporary variable *)
  | Ederef: expr -> type -> expr          (**r pointer dereference (unary [*]) *)
  | Eaddrof: expr -> type -> expr         (**r address-of operator ([&]) *)
  | Eunop: unary_operation -> expr -> type -> expr  (**r unary operation *)
  | Ebinop: binary_operation -> expr -> expr -> type -> expr (**r binary operation *)
  | Ecast: expr -> type -> expr   (**r type cast ([(ty) e]) *)
  | Efield: expr -> ident -> type -> expr (**r access to a member of a struct or union *)
  | Esizeof: type -> type -> expr         (**r size of a type *)
  | Ealignof: type -> type -> expr        (**r alignment of a type *)
  (* new cases for persistent data and struct and array *)
  | Epvar: ident -> type -> expr
  | Eindex: expr -> expr -> type -> expr
  | Epfield: expr -> ident -> type -> expr.

  Definition typeof (e: expr) : type :=
    match e with
    | Econst_int _ ty => ty
    | Econst_float _ ty => ty
    | Econst_single _ ty => ty
    | Econst_long _ ty => ty
    | Evar _ ty => ty
    | Etempvar _ ty => ty
    | Ederef _ ty => ty
    | Eaddrof _ ty => ty
    | Eunop _ _ ty => ty
    | Ebinop _ _ _ ty => ty
    | Ecast _ ty => ty
    | Efield _ _ ty => ty
    | Esizeof _ ty => ty
    | Ealignof _ ty => ty
    | Epvar _ ty => ty
    | Eindex _ _ ty => ty
    | Epfield _ _ ty => ty
    end.

  Inductive statement : Type :=
  | Sskip : statement                   (**r do nothing *)
  | Sassign : expr -> expr -> statement (**r assignment [lvalue = rvalue] *)
  | Sset : ident -> expr -> statement   (**r assignment [tempvar = rvalue] *)
  | Scall: option ident -> expr -> list expr -> statement (**r function call *)
  | Sbuiltin: option ident -> external_function -> typelist -> list expr -> statement (**r builtin invocation *)
  | Ssequence : statement -> statement -> statement  (**r sequence *)
  | Sifthenelse : expr  -> statement -> statement -> statement (**r conditional *)
  | Sloop: statement -> statement -> statement (**r infinite loop *)
  | Sbreak : statement                      (**r [break] statement *)
  | Scontinue : statement                   (**r [continue] statement *)
  | Sreturn : option expr -> statement      (**r [return] statement *)
  | Sswitch : expr -> labeled_statements -> statement  (**r [switch] statement *)
  | Slabel : label -> statement -> statement
  | Sgoto : label -> statement

  | Supdate : expr -> expr -> statement

  with labeled_statements : Type :=            (**r cases of a [switch] *)
  | LSnil: labeled_statements
  | LScons: option Z -> statement -> labeled_statements -> labeled_statements.
  (**r [None] is [default], [Some x] is [case x] *)

  Fixpoint select_switch_default (sl: labeled_statements): labeled_statements :=
    match sl with
    | LSnil => sl
    | LScons None s sl' => sl
    | LScons (Some i) s sl' => select_switch_default sl'
    end.

  Fixpoint select_switch_case (n: Z) (sl: labeled_statements): option labeled_statements :=
    match sl with
    | LSnil => None
    | LScons None s sl' => select_switch_case n sl'
    | LScons (Some c) s sl' => if zeq c n then Some sl else select_switch_case n sl'
    end.

  Definition select_switch (n: Z) (sl: labeled_statements): labeled_statements :=
    match select_switch_case n sl with
    | Some sl' => sl'
    | None => select_switch_default sl
    end.

  (** Turn a labeled statement into a sequence *)

  Fixpoint seq_of_labeled_statement (sl: labeled_statements) : statement :=
    match sl with
    | LSnil => Sskip
    | LScons _ s sl' => Ssequence s (seq_of_labeled_statement sl')
    end.

  Record function : Type :=
    mkfunction {
        fn_return: type;
        fn_callconv: calling_convention;
        fn_params: list (ident * type);
        fn_vars: list (ident * type);
        fn_temps: list (ident * type);
        fn_body: statement
      }.
  Definition fundef := Ctypes.fundef function.
  Definition type_of_function (f: function) : type :=
    Tfunction (type_of_params (fn_params f)) (fn_return f) (fn_callconv f).

  Definition type_of_fundef (f: fundef) : type :=
    match f with
    | Internal fd => type_of_function fd
    | External id args res cc => Tfunction args res cc
    end.

  Record program : Type := {
      prog_defs: list (ident * globdef fundef type);
      prog_private: list (ident * privvar);
      prog_public: list ident;
      prog_main: option ident;
      prog_types: list composite_definition;
      prog_comp_env: composite_env;
      prog_comp_env_eq: build_composite_env prog_types = OK prog_comp_env;
      (* for the purpose of making linking properties easier *)
      prog_norepet:
        list_norepet (map fst prog_private ++ map fst prog_defs);
      prog_priv_ok:
        pvars_ok prog_comp_env prog_private;
    }.

  Definition program_of_program (p: program) : AST.program fundef type :=
    {|
      AST.prog_defs := p.(prog_defs);
      AST.prog_public := p.(prog_public);
      AST.prog_main := p.(prog_main); |}.
  Coercion program_of_program: program >-> AST.program.

  Record genv := { genv_genv :> Genv.t fundef type;
                   genv_cenv :> composite_env }.

  Definition globalenv (se: Genv.symtbl) (p: program) :=
    {| genv_genv := Genv.globalenv se p; genv_cenv := p.(prog_comp_env) |}.

  Section SEM.
    Open Scope Z_scope.

    Variable ce: composite_env.
    Variable ge: genv.

    Inductive alloc_variables: env -> mem ->
                               list (ident * type) ->
                               env -> mem -> Prop :=
    | alloc_variables_nil:
      forall e m,
        alloc_variables e m nil e m
    | alloc_variables_cons:
      forall e m id ty vars m1 b1 m2 e2,
        Mem.alloc m 0 (sizeof ge ty) = Some (m1, b1) ->
        alloc_variables (PTree.set id (b1, ty) e) m1 vars e2 m2 ->
        alloc_variables e m ((id, ty) :: vars) e2 m2.

    Inductive bind_parameters (e: env):
                               mem ->
                               list (ident * type) -> list Values.val ->
                               mem -> Prop :=
    | bind_parameters_nil:
      forall m,
        bind_parameters e m nil nil m
    | bind_parameters_cons:
      forall m id ty params v1 vl b m1 m2,
        PTree.get id e = Some(b, ty) ->
        assign_loc ge ty m b Ptrofs.zero Full v1 m1 ->
        bind_parameters e m1 params vl m2 ->
        bind_parameters e m ((id, ty) :: params) (v1 :: vl) m2.

    Section EXPR.

      Variable e: env.
      Variable le: temp_env.
      Variable pe: penv.
      Variable m: mem.

      Inductive eval_expr: expr -> Values.val -> Prop :=
      | eval_Econst_int:   forall i ty,
          eval_expr (Econst_int i ty) (Vint i)
      | eval_Econst_float:   forall f ty,
          eval_expr (Econst_float f ty) (Vfloat f)
      | eval_Econst_single:   forall f ty,
          eval_expr (Econst_single f ty) (Vsingle f)
      | eval_Econst_long:   forall i ty,
          eval_expr (Econst_long i ty) (Vlong i)
      | eval_Etempvar:  forall id ty v,
          le!id = Some v ->
          eval_expr (Etempvar id ty) v
      | eval_Eaddrof: forall a ty loc ofs,
          eval_lvalue a loc ofs Full ->
          eval_expr (Eaddrof a ty) (Vptr loc ofs)
      | eval_Eunop:  forall op a ty v1 v,
          eval_expr a v1 ->
          sem_unary_operation op v1 (typeof a) m = Some v ->
          eval_expr (Eunop op a ty)  v
      | eval_Ebinop: forall op a1 a2 ty v1 v2 v,
          eval_expr a1 v1 ->
          eval_expr a2 v2 ->
          sem_binary_operation ge op v1 (typeof a1) v2 (typeof a2) m = Some v ->
          eval_expr (Ebinop op a1 a2 ty) v
      | eval_Ecast:   forall a ty v1 v,
          eval_expr a v1 ->
          sem_cast v1 (typeof a) ty m = Some v ->
          eval_expr (Ecast a ty) v
      | eval_Esizeof: forall ty1 ty,
          eval_expr (Esizeof ty1 ty) (Vptrofs (Ptrofs.repr (sizeof ge ty1)))
      | eval_Ealignof: forall ty1 ty,
          eval_expr (Ealignof ty1 ty) (Vptrofs (Ptrofs.repr (alignof ge ty1)))
      | eval_Elvalue: forall a loc ofs v bf,
          eval_lvalue a loc ofs bf ->
          deref_loc (typeof a) m loc ofs bf  v ->
          eval_expr a v
      (* the new case *)
      | eval_Eloc: forall e id l v ty,
          eval_loc e id l ->
          pread ce pe id l v ty ->
          ty = typeof e ->
          eval_expr e v

      with eval_lvalue: expr -> block -> ptrofs -> bitfield -> Prop :=
      | eval_Evar_local:   forall id l ty,
          e!id = Some(l, ty) ->
          eval_lvalue (Evar id ty) l Ptrofs.zero Full
      | eval_Evar_global: forall id l ty,
          e!id = None ->
          Genv.find_symbol ge id = Some l ->
          eval_lvalue (Evar id ty) l Ptrofs.zero Full
      | eval_Ederef: forall a ty l ofs,
          eval_expr a (Vptr l ofs)  ->
          eval_lvalue (Ederef a ty) l ofs Full
      | eval_Efield_struct:   forall a i ty l ofs id co att delta bf,
          eval_expr a (Vptr l ofs)  ->
          typeof a = Tstruct id att ->
          ge.(genv_cenv)!id = Some co ->
          Ctypes.field_offset ge i (co_members co) = OK (delta, bf) ->
          eval_lvalue (Efield a i ty) l (Ptrofs.add ofs (Ptrofs.repr delta)) bf
      | eval_Efield_union:   forall a i ty l ofs id co att delta bf,
          eval_expr a (Vptr l ofs)  ->
          typeof a = Tunion id att ->
          ge.(genv_cenv)!id = Some co ->
          union_field_offset ge i (co_members co) = OK (delta, bf) ->
          eval_lvalue (Efield a i ty) l (Ptrofs.add ofs (Ptrofs.repr delta)) bf

      with eval_loc: expr -> ident -> loc -> Prop :=
      | eval_Epvar: forall id ty v,
          e!id = None ->
          PTree.get id pe = Some v ->
          eval_loc (Epvar id ty) id (Loc ty nil)
      | eval_Eindex: forall earr ei i ty_prev ty_elem id l n l'
          (TARR: typeof earr = Tarray ty_elem n noattr)
          (TI: typeof ei = Tint I32 Unsigned noattr)
          (TPREV: ty_prev = typeof earr)
          (ELOC: eval_loc earr id (Loc ty_prev l))
          (EINT: eval_expr ei (Vint i))
          (NEXT_LOC: l' = l ++ (Index (Int.unsigned i) ty_elem :: nil))
          (* this condition might be superfluous but we need it to solve some
             overflow puzzles *)
          (BOUND: 0 <= Int.unsigned i < n),
          eval_loc (Eindex earr ei ty_elem) id (Loc ty_elem l')
      | eval_Efield: forall estruct f tid l l' ty_field ty_prev id co ofs
        (TSTRUCT: typeof estruct = Tstruct tid noattr)
        (TPREV: ty_prev = typeof estruct)
        (ELOC: eval_loc estruct id (Loc ty_prev l))
        (NEXT_LOC: l' = l ++ (Field f tid :: nil))
        (HCO: ce!tid = Some co)
        (HTY: field_type f (co_members co) = OK ty_field)
        (HSU: co_su co = Ctypes.Struct)
        (HF: Ctypes.field_offset ce f (co_members co) = OK (ofs, Full)),
        eval_loc (Epfield estruct f ty_field) id (Loc ty_field l').
      Scheme eval_expr_ind2 := Minimality for eval_expr Sort Prop
          with eval_lvalue_ind2 := Minimality for eval_lvalue Sort Prop
          with eval_loc_ind2 := Minimality for eval_loc Sort Prop.
      Combined Scheme eval_expr_lvalue_loc_ind from eval_expr_ind2, eval_lvalue_ind2, eval_loc_ind2.

      Inductive eval_exprlist: list expr -> typelist -> list Values.val -> Prop :=
      | eval_Enil:
        eval_exprlist nil Tnil nil
      | eval_Econs:   forall a bl ty tyl v1 v2 vl,
          eval_expr a v1 ->
          sem_cast v1 (typeof a) ty m = Some v2 ->
          eval_exprlist bl tyl vl ->
          eval_exprlist (a :: bl) (Tcons ty tyl) (v2 :: vl).

    End EXPR.

    Definition block_of_binding (id_b_ty: ident * (block * type)) :=
      match id_b_ty with (id, (b, ty)) => (b, 0, sizeof ge ty) end.

    Definition blocks_of_env (e: env) : list (block * Z * Z) :=
      List.map block_of_binding (PTree.elements e).

    (** Transition relation *)

    Inductive cont: Type :=
    | Kstop: cont
    | Kseq: statement -> cont -> cont
    | Kloop1: statement -> statement -> cont -> cont
    | Kloop2: statement -> statement -> cont -> cont
    | Kswitch: cont -> cont
    | Kcall: option ident -> function -> env -> temp_env -> cont -> cont.

    Fixpoint call_cont (k: cont) : cont :=
      match k with
      | Kseq s k => call_cont k
      | Kloop1 s1 s2 k => call_cont k
      | Kloop2 s1 s2 k => call_cont k
      | Kswitch k => call_cont k
      | _ => k
      end.

    Definition is_call_cont (k: cont) : Prop :=
      match k with
      | Kstop => True
      | Kcall _ _ _ _ _ => True
      | _ => False
      end.

    Inductive state: Type :=
    | State (f: function) (s: statement) (k: cont)
            (e: env) (le: temp_env) (m: mem) : state
    | Callstate (vf: Values.val) (args: list Values.val)
                (k: cont) (m: mem) : state
    | Returnstate (res: Values.val) (k: cont) (m: mem) : state.

    Fixpoint find_label (lbl: label) (s: statement) (k: cont)
             {struct s}: option (statement * cont) :=
      match s with
      | Ssequence s1 s2 =>
          match find_label lbl s1 (Kseq s2 k) with
          | Some sk => Some sk
          | None => find_label lbl s2 k
          end
      | Sifthenelse a s1 s2 =>
          match find_label lbl s1 k with
          | Some sk => Some sk
          | None => find_label lbl s2 k
          end
      | Sloop s1 s2 =>
          match find_label lbl s1 (Kloop1 s1 s2 k) with
          | Some sk => Some sk
          | None => find_label lbl s2 (Kloop2 s1 s2 k)
          end
      | Sswitch e sl =>
          find_label_ls lbl sl (Kswitch k)
      | Slabel lbl' s' =>
          if ident_eq lbl lbl' then Some(s', k) else find_label lbl s' k
      | _ => None
      end

    with find_label_ls (lbl: label) (sl: labeled_statements) (k: cont)
                       {struct sl}: option (statement * cont) :=
           match sl with
           | LSnil => None
           | LScons _ s sl' =>
               match find_label lbl s (Kseq (seq_of_labeled_statement sl') k) with
               | Some sk => Some sk
               | None => find_label_ls lbl sl' k
               end
           end.

    Variable function_entry:
      function -> list Values.val -> mem -> env -> temp_env -> mem -> Prop.

    Inductive step: state * penv -> trace -> state * penv -> Prop :=

    | step_assign:   forall f a1 a2 k e le pe m loc ofs bf v2 v m',
        eval_lvalue e le pe m a1 loc ofs bf ->
        eval_expr e le pe m a2 v2 ->
        sem_cast v2 (typeof a2) (typeof a1) m = Some v ->
        assign_loc ge (typeof a1) m loc ofs bf v m' ->
        step (State f (Sassign a1 a2) k e le m, pe)
             E0 (State f Sskip k e le m', pe)

    | step_set:   forall f id a k e le pe m v,
        eval_expr e le pe m a v ->
        step (State f (Sset id a) k e le m, pe)
             E0 (State f Sskip k e (PTree.set id v le) m, pe)

    (* By_value update *)
    | step_update: forall f a1 a2 k e le l pe pe' m id new_v,
        eval_loc e le pe m a1 id l ->
        eval_expr e le pe m a2 new_v ->
        pwrite ce pe id l new_v pe' (typeof a2) ->
        (* maybe we could implement [sem_cast] like in Sassign *)
        typeof a2 = typeof a1 ->
        val_casted new_v (typeof a1) ->
        step (State f (Supdate a1 a2) k e le m, pe)
             E0 (State f Sskip k e le m, pe')

    | step_call:   forall f optid a al k e le pe m tyargs tyres cconv vf vargs fd ,
        classify_fun (typeof a) = fun_case_f tyargs tyres cconv ->
        eval_expr e le pe m a vf ->
        eval_exprlist e le pe m al tyargs vargs ->
        Genv.find_funct ge vf = Some fd ->
        type_of_fundef fd = Tfunction tyargs tyres cconv ->
        step (State f (Scall optid a al) k e le m, pe)
             E0 (Callstate vf vargs (Kcall optid f e le k) m, pe)

    | step_builtin:   forall f optid ef tyargs al k e le pe m vargs t vres m',
        eval_exprlist e le pe m al tyargs vargs ->
        external_call ef ge vargs m t vres m' ->
        step (State f (Sbuiltin optid ef tyargs al) k e le m, pe)
             t (State f Sskip k e (set_opttemp optid vres le) m', pe)

    | step_seq:  forall f s1 s2 k e le pe m,
        step (State f (Ssequence s1 s2) k e le m, pe)
             E0 (State f s1 (Kseq s2 k) e le m, pe)
    | step_skip_seq: forall f s k e le pe m,
        step (State f Sskip (Kseq s k) e le m, pe)
             E0 (State f s k e le m, pe)
    | step_continue_seq: forall f s k e le pe m,
        step (State f Scontinue (Kseq s k) e le m, pe)
             E0 (State f Scontinue k e le m, pe)
    | step_break_seq: forall f s k e le pe m,
        step (State f Sbreak (Kseq s k) e le m, pe)
             E0 (State f Sbreak k e le m, pe)

    | step_ifthenelse:  forall f a s1 s2 k e le pe m v1 b,
        eval_expr e le pe m a v1 ->
        bool_val v1 (typeof a) m = Some b ->
        step (State f (Sifthenelse a s1 s2) k e le m, pe)
             E0 (State f (if b then s1 else s2) k e le m, pe)

    | step_loop: forall f s1 s2 k e le pe m,
        step (State f (Sloop s1 s2) k e le m, pe)
             E0 (State f s1 (Kloop1 s1 s2 k) e le m, pe)
    | step_skip_or_continue_loop1:  forall f s1 s2 k e le pe m x,
        x = Sskip \/ x = Scontinue ->
        step (State f x (Kloop1 s1 s2 k) e le m, pe)
             E0 (State f s2 (Kloop2 s1 s2 k) e le m, pe)
    | step_break_loop1:  forall f s1 s2 k e le pe m,
        step (State f Sbreak (Kloop1 s1 s2 k) e le m, pe)
             E0 (State f Sskip k e le m, pe)
    | step_skip_loop2: forall f s1 s2 k e le pe m,
        step (State f Sskip (Kloop2 s1 s2 k) e le m, pe)
             E0 (State f (Sloop s1 s2) k e le m, pe)
    | step_break_loop2: forall f s1 s2 k e le pe m,
        step (State f Sbreak (Kloop2 s1 s2 k) e le m, pe)
             E0 (State f Sskip k e le m, pe)

    | step_return_0: forall f k e le pe m m',
        Mem.free_list m (blocks_of_env e) = Some m' ->
        step (State f (Sreturn None) k e le m, pe)
             E0 (Returnstate Vundef (call_cont k) m', pe)
    | step_return_1: forall f a k e le pe m v v' m',
        eval_expr e le pe m a v ->
        sem_cast v (typeof a) f.(fn_return) m = Some v' ->
        Mem.free_list m (blocks_of_env e) = Some m' ->
        step (State f (Sreturn (Some a)) k e le m, pe)
             E0 (Returnstate v' (call_cont k) m', pe)
    | step_skip_call: forall f k e le pe m m',
        is_call_cont k ->
        Mem.free_list m (blocks_of_env e) = Some m' ->
        step (State f Sskip k e le m, pe)
             E0 (Returnstate Vundef k m', pe)

    | step_switch: forall f a sl k e le pe m v n,
        eval_expr e le pe m a v ->
        sem_switch_arg v (typeof a) = Some n ->
        step (State f (Sswitch a sl) k e le m, pe)
             E0 (State f (seq_of_labeled_statement (select_switch n sl)) (Kswitch k) e le m, pe)
    | step_skip_break_switch: forall f x k e le pe m,
        x = Sskip \/ x = Sbreak ->
        step (State f x (Kswitch k) e le m, pe)
             E0 (State f Sskip k e le m, pe)
    | step_continue_switch: forall f k e le pe m,
        step (State f Scontinue (Kswitch k) e le m, pe)
             E0 (State f Scontinue k e le m, pe)

    | step_label: forall f lbl s k e le pe m,
        step (State f (Slabel lbl s) k e le m, pe)
             E0 (State f s k e le m, pe)

    | step_goto: forall f lbl k e le pe m s' k',
        find_label lbl f.(fn_body) (call_cont k) = Some (s', k') ->
        step (State f (Sgoto lbl) k e le m, pe)
             E0 (State f s' k' e le m, pe)

    | step_internal_function: forall vf f vargs k m e le pe m1,
      forall FIND: Genv.find_funct ge vf = Some (Internal f),
        function_entry f vargs m e le m1 ->
        step (Callstate vf vargs k m, pe)
             E0 (State f f.(fn_body) k e le m1, pe)

    | step_external_function: forall vf ef targs tres cconv vargs k m vres t m' pe,
      forall FIND: Genv.find_funct ge vf = Some (External ef targs tres cconv),
        external_call ef ge vargs m t vres m' ->
        step (Callstate vf vargs k m, pe)
             t (Returnstate vres k m', pe)

    | step_returnstate: forall v optid f e le pe k m,
        step (Returnstate v (Kcall optid f e le k) m, pe)
             E0 (State f Sskip k e (set_opttemp optid v le) m, pe).

    Inductive initial_state: c_query * penv -> state * penv -> Prop :=
    | initial_state_intro: forall vf f targs tres tcc vargs m pe,
        Genv.find_funct ge vf = Some (Internal f) ->
        type_of_function f = Tfunction targs tres tcc ->
        val_casted_list vargs targs ->
        Ple (Genv.genv_next ge) (Mem.nextblock m) ->
        initial_state
          (cq vf (signature_of_type targs tres tcc) vargs m, pe)
          (Callstate vf vargs Kstop m, pe).

    Inductive at_external: state * penv -> c_query -> Prop :=
    | at_external_intro name sg targs tres cconv vf vargs k m pe:
      let f := External (EF_external name sg) targs tres cconv in
      Genv.find_funct ge vf = Some f ->
      at_external
        (Callstate vf vargs k m, pe)
        (cq vf sg vargs m).

    Inductive after_external: state * penv -> c_reply -> state * penv -> Prop :=
    | after_external_intro vf vargs k m pe vres m':
      after_external
        (Callstate vf vargs k m, pe)
        (cr vres m')
        (Returnstate vres k m', pe).

    Inductive final_state: state * penv -> c_reply * penv -> Prop :=
    | final_state_intro: forall r m pe,
        final_state
          (Returnstate r Kstop m, pe)
          (cr r m, pe).

  End SEM.

  Inductive function_entry1 (ge: genv) (f: function) (vargs: list Values.val) (m: mem) (e: env) (le: temp_env) (m': mem) : Prop :=
  | function_entry1_intro: forall m1,
      list_norepet (var_names f.(fn_params) ++ var_names f.(fn_vars)) ->
      alloc_variables ge empty_env m (f.(fn_params) ++ f.(fn_vars)) e m1 ->
      bind_parameters ge e m1 f.(fn_params) vargs m' ->
      le = create_undef_temps f.(fn_temps) ->
      Mem.alloc_flag m = true ->
      function_entry1 ge f vargs m e le m'.

  Definition step1 ce (ge: genv) := step ce ge (function_entry1 ge).

  (** Second, parameters as temporaries. *)

  Inductive function_entry2 (ge: genv)  (f: function) (vargs: list Values.val) (m: mem) (e: env) (le: temp_env) (m': mem) : Prop :=
  | function_entry2_intro:
    list_norepet (var_names f.(fn_vars)) ->
    list_norepet (var_names f.(fn_params)) ->
    list_disjoint (var_names f.(fn_params)) (var_names f.(fn_temps)) ->
    alloc_variables ge empty_env m f.(fn_vars) e m' ->
    bind_parameter_temps f.(fn_params) vargs (create_undef_temps f.(fn_temps)) = Some le ->
    Mem.alloc_flag m = true ->
    function_entry2 ge f vargs m e le m'.

  Definition step2 ce (ge: genv) := step ce ge (function_entry2 ge).

  Definition add_private (pe: penv) (x: ident * privvar) : penv :=
    match x with
      (i, v) => PTree.set i (pvar_init v) pe
    end.

  Definition empty_penv : penv := PTree.empty val.

  Definition add_privates (pe: penv) (x: list (ident * privvar)) : penv :=
    List.fold_left add_private x pe.

  Program Definition clightp_erase_privvar (v: privvar) : globdef unit unit :=
    Gvar {|
        gvar_info := tt;
        gvar_init := val_init_data (pvar_init v);
        gvar_readonly := false;
        gvar_volatile := false;
      |}.

  Definition priv_glob_combine
    (p1: option privvar) (p2: option (globdef fundef type)) :=
    match p1, p2 with
    | Some v, None => Some (clightp_erase_privvar v)
    | None, Some v => Some (erase_globdef v)
    | _, _ => None
    end.

  Definition clightp_erase_program (p: program) : AST.program unit unit :=
    let priv := PTree_Properties.of_list p.(prog_private) in
    let glob := prog_defmap p in
    mkprogram
      (PTree.elements (PTree.combine priv_glob_combine priv glob))
      p.(prog_public) p.(prog_main).

  Program Definition clightp1 (p : program) : semantics _ (li_c@penv) :=
    {|
      skel := clightp_erase_program p;
      activate se :=
        let ge := globalenv se p in
        {|
          Smallstep.step := step1 (prog_comp_env p);
          Smallstep.initial_state := initial_state ge;
          Smallstep.at_external := at_external ge;
          Smallstep.after_external := after_external;
          Smallstep.final_state := final_state;
          Smallstep.globalenv := ge;
        |};
      footprint := AST.footprint_of_program p;
    |}.

  Program Definition clightp2 (p : program) : semantics _ (li_c@penv) :=
    {|
      skel := clightp_erase_program p;
      activate se :=
        let ge := globalenv se p in
        {|
          Smallstep.step := step2 (prog_comp_env p);
          Smallstep.initial_state := initial_state ge;
          Smallstep.at_external := at_external ge;
          Smallstep.after_external := after_external;
          Smallstep.final_state := final_state;
          Smallstep.globalenv := ge;
        |};
      footprint := AST.footprint_of_program p;
    |}.

End ClightP.

(** ------------------------------------------------------------------------- *)

(** ** Compile ClightP to Clight *)

Section TRANSF.
  Open Scope Z_scope.
  Open Scope error_monad_scope.
  Import ClightP.

  Section WITH_CE.
  Variable (ce: composite_env).
  Fixpoint transl_expr (a: expr) : res Clight.expr :=
    match a with
    | Econst_int i ty => OK (Clight.Econst_int i ty)
    | Econst_float f ty => OK (Clight.Econst_float f ty)
    | Econst_single s ty => OK (Clight.Econst_single s ty)
    | Econst_long l ty => OK (Clight.Econst_long l ty)
    | Evar i ty => OK (Clight.Evar i ty)
    | Etempvar i ty => OK (Clight.Etempvar i ty)
    | Ederef e ty =>
        do te <- transl_expr e;
        OK (Clight.Ederef te ty)
    | Eaddrof e ty =>
        do te <- transl_expr e;
        OK (Clight.Eaddrof te ty)
    | Eunop op e ty =>
        do te <- transl_expr e;
        OK (Clight.Eunop op te ty)
    | Ebinop op e1 e2 ty =>
        do te1 <- transl_expr e1;
        do te2 <- transl_expr e2;
        OK (Clight.Ebinop op te1 te2 ty)
    | Ecast e ty =>
        do te <- transl_expr e;
        OK (Clight.Ecast te ty)
    | Efield e f ty =>
        do te <- transl_expr e;
        OK (Clight.Efield te f ty)
    | Esizeof t ty => OK (Clight.Esizeof t ty)
    | Ealignof t ty => OK (Clight.Ealignof t ty)
    | Epvar i ty =>
        assertion (zlt (sizeof ce ty) Ptrofs.max_unsigned);
        OK (Clight.Evar i ty)
    | Eindex ea ei ty =>
        do tea <- transl_expr ea;
        do tei <- transl_expr ei;
        OK (Clight.Ederef
              (Clight.Ebinop Oadd tea tei (Tpointer ty noattr)) ty)
    | Epfield estruct f ty =>
        do testruct <- transl_expr estruct;
        OK (Clight.Efield testruct f ty)
    end.

  Fixpoint transl_exprlist (xs: list expr): res (list Clight.expr) :=
    match xs with
    | nil => OK nil
    | e :: es =>
        do te <- transl_expr e;
        do tes <- transl_exprlist es;
        OK (te :: tes)
    end.

  Definition transl_arglist := transl_exprlist.

  Fixpoint transl_statement (s: statement) : res Clight.statement :=
    match s with
    | Sskip => OK Clight.Sskip
    | Sassign b c =>
        do tb <- transl_expr b;
        do tc <- transl_expr c;
        OK (Clight.Sassign tb tc)
    | Sset x b =>
        do tb <- transl_expr b;
        OK (Clight.Sset x tb)
    | Scall x b cl =>
        do tb <- transl_expr b;
        do tcl <- transl_arglist cl;
        OK (Clight.Scall x tb tcl)
    | Sbuiltin x ef tyargs bl =>
        do tbl <- transl_arglist bl;
        OK (Clight.Sbuiltin x ef tyargs tbl)
    | Ssequence s1 s2 =>
        do ts1 <- transl_statement s1;
        do ts2 <- transl_statement s2;
        OK (Clight.Ssequence ts1 ts2)
    | Sifthenelse e s1 s2 =>
        do te <- transl_expr e;
        do ts1 <- transl_statement s1;
        do ts2 <- transl_statement s2;
        OK (Clight.Sifthenelse te ts1 ts2)
    | Sloop s1 s2 =>
        do ts1 <- transl_statement s1;
        do ts2 <- transl_statement s2;
        OK (Clight.Sloop ts1 ts2)
    | Sbreak => OK (Clight.Sbreak)
    | Scontinue => OK (Clight.Scontinue)
    | Sreturn (Some e) =>
        do te <- transl_expr e;
        OK (Clight.Sreturn (Some te))
    | Sreturn None => OK (Clight.Sreturn None)
    | Sswitch a sl =>
        do ta <- transl_expr a;
        do tsl <- transl_lbl_stmt sl;
        OK (Clight.Sswitch ta tsl)
    | Slabel lbl s =>
        do ts <- transl_statement s;
        OK (Clight.Slabel lbl ts)
    | Sgoto lbl => OK (Clight.Sgoto lbl)
    | Supdate b c =>
        do tb <- transl_expr b;
        do tc <- transl_expr c;
        OK (Clight.Sassign tb tc)
    end
  with transl_lbl_stmt (sl: labeled_statements) :=
         match sl with
         | LSnil => OK Clight.LSnil
         | LScons n s sl' =>
             do ts <- transl_statement s;
             do tsl' <- transl_lbl_stmt sl';
             OK (Clight.LScons n ts tsl')
         end.

  Definition transl_function (f: function) : res Clight.function :=
    do tbody <- transl_statement (fn_body f);
    OK ({|
           Clight.fn_return := fn_return f;
           Clight.fn_callconv := fn_callconv f;
           Clight.fn_params := fn_params f;
           Clight.fn_vars := fn_vars f;
           Clight.fn_temps := fn_temps f;
           Clight.fn_body := tbody
        |}).

  Definition transl_fundef (id: ident) (f: fundef) : res Clight.fundef :=
    match f with
    | Internal g =>
        do tg <- transl_function g;
        OK (Internal tg)
    | External ef args res cconv => OK (External ef args res cconv)
    end.
  End WITH_CE.

  Definition transl_globvar (id: ident) (ty: type) := OK ty.

  Definition transl_privvar (v: privvar) :=
    {|
      gvar_info := type_of_pv v;
      gvar_init := ClightP.val_init_data (pvar_init v);
      gvar_volatile := false;
      gvar_readonly := false;
    |}.

  Definition transl_privvars {F} (l: list (ident * privvar)) :=
    List.map (fun '(id, pv) => (id, Gvar (F:=F) (transl_privvar pv))) l.

  Definition transl_program (p: program) : res Clight.program :=
    do tgl <- transf_globdefs (transl_fundef p.(prog_comp_env)) transl_globvar p.(prog_defs);
    let tgv := transl_privvars (prog_private p) in
    OK ({|
           Ctypes.prog_defs := PTree.elements (PTree_Properties.of_list (tgv ++ tgl));
           Ctypes.prog_public := prog_public p;
           Ctypes.prog_main := prog_main p;
           Ctypes.prog_types := prog_types p;
           Ctypes.prog_comp_env := prog_comp_env p;
           Ctypes.prog_comp_env_eq := prog_comp_env_eq p |}).

End TRANSF.

(** ------------------------------------------------------------------------- *)
(** Preservation *)

Section PRESERVATION.

  Variable prog: ClightP.program.
  Variable tprog: Clight.program.
  Hypothesis TRANSL: transl_program prog = OK tprog.
  (* match_senv is defined as equal. For now, we require the source and target
     symbol tables to be the same and both carry the module static variables *)
  Variable se: Genv.symtbl.
  Let ge : ClightP.genv := ClightP.globalenv se prog.
  Let tge : Clight.genv := Clight.globalenv se tprog.
  Let ce : composite_env := ClightP.prog_comp_env prog.

  Lemma Hconsistent: composite_env_consistent ce.
  Proof.
    eapply build_composite_env_consistent.
    subst ce. eapply ClightP.prog_comp_env_eq.
  Qed.

  Inductive pmatch_cont: (ClightP.cont * penv) -> Clight.cont -> Prop :=
  | pmatch_Kstop: forall pe, pmatch_cont (ClightP.Kstop, pe) Clight.Kstop
  | pmatch_Kseq: forall s t k tk pe,
      transl_statement ce s = OK t ->
      pmatch_cont (k, pe) tk ->
      pmatch_cont (ClightP.Kseq s k, pe) (Clight.Kseq t tk)
  | pmatch_Kloop1: forall s1 s2 ts1 ts2 k tk pe,
      transl_statement ce s1 = OK ts1 ->
      transl_statement ce s2 = OK ts2 ->
      pmatch_cont (k, pe) tk ->
      pmatch_cont (ClightP.Kloop1 s1 s2 k, pe) (Clight.Kloop1 ts1 ts2 tk)
  | pmatch_Kloop2: forall s1 s2 ts1 ts2 k tk pe,
      transl_statement ce s1 = OK ts1 ->
      transl_statement ce s2 = OK ts2 ->
      pmatch_cont (k, pe) tk ->
      pmatch_cont (ClightP.Kloop2 s1 s2 k, pe) (Clight.Kloop2 ts1 ts2 tk)
  | pmatch_Kswitch: forall k tk pe,
      pmatch_cont (k, pe) tk -> pmatch_cont (ClightP.Kswitch k, pe) (Clight.Kswitch tk)
  | pmatch_Kcall: forall fid f tf e le k tk pe,
      transl_function ce f = OK tf ->
      pmatch_cont (k, pe) tk ->
      pmatch_cont (ClightP.Kcall fid f e le k, pe) (Clight.Kcall fid tf e le tk).

  Inductive pmatch_state: Genv.symtbl -> ClightP.state * penv -> Clight.state -> Prop :=
  | pmatch_State: forall se fs ss ks e le ms pe ft st kt mt
      (TRF: transl_function ce fs = OK ft)
      (TRS: transl_statement ce ss = OK st)
      (MK: pmatch_cont (ks, pe) kt)
      (MP: penv_match ce se (pe, ms) mt),
      pmatch_state se (ClightP.State fs ss ks e le ms, pe) (Clight.State ft st kt e le mt)
  | pmatch_Callstate: forall se vf args ks kt ms mt pe
      (MK: pmatch_cont (ks, pe) kt)
      (MP: penv_match ce se (pe, ms) mt),
      pmatch_state se (ClightP.Callstate vf args ks ms, pe) (Clight.Callstate vf args kt mt)
  | pmatch_Returnstate: forall se rv ks kt ms mt pe
      (MK: pmatch_cont (ks, pe) kt)
      (MP: penv_match ce se (pe, ms) mt),
      pmatch_state se (ClightP.Returnstate rv ks ms, pe) (Clight.Returnstate rv kt mt).

  Definition transl_expr_typeof e te:
    transl_expr ce e = OK te -> ClightP.typeof e = typeof te.
  Proof.
    intros TE; destruct e; monadInv TE; cbn in *; eauto.
  Qed.

(** ------------------------------------------------------------------------- *)
(** Correctness of [eval_expr] *)

  Lemma eval_expr_lvalue_correct :
    forall e le m tm pe,
      penv_match ce se (pe, m) tm ->
      (forall expr v,
          ClightP.eval_expr ce ge e le pe m expr v ->
          forall texpr (TR: transl_expr ce expr = OK texpr),
            Clight.eval_expr tge e le tm texpr v)
      /\
      (forall expr b ofs bf,
         ClightP.eval_lvalue ce ge e le pe m expr b ofs bf ->
         forall texpr (TR: transl_expr ce expr = OK texpr),
           Clight.eval_lvalue tge e le tm texpr b ofs bf)
      /\
      (forall expr id l,
        ClightP.eval_loc ce ge e le pe m expr id l ->
        forall texpr (TR: transl_expr ce expr = OK texpr),
        exists b ofs, Clight.eval_lvalue tge e le tm texpr b (Ptrofs.repr ofs) Full
                 /\ Genv.find_symbol se id = Some b
                 /\ match_loc ce l ofs
                 /\ ofs + sizeof ce (ClightP.typeof expr) < Ptrofs.max_unsigned).
  Proof.
    intros e le t tm pe HP.
    apply ClightP.eval_expr_lvalue_loc_ind.
    - intros. monadInv TR. constructor.
    - intros. monadInv TR. constructor.
    - intros. monadInv TR. constructor.
    - intros. monadInv TR. constructor.
    - intros. monadInv TR. constructor. eauto.
    - intros. monadInv TR.
      constructor. apply H0. apply EQ.
    - intros. monadInv TR. econstructor; eauto.
      erewrite <- transl_expr_typeof; eauto. inv HP.
      exploit sem_unary_operation_join. apply MJOIN.
      intros A. rewrite H1 in A. inv A. reflexivity.
    - intros. monadInv TR. econstructor; eauto.
      erewrite <- !transl_expr_typeof; eauto. inv HP.
      exploit sem_binary_operation_join. apply MJOIN.
      intros A. rewrite H3 in A. inv A.
      monadInv TRANSL.  cbn in *. congruence.
    - intros. monadInv TR. econstructor; eauto.
      erewrite <- transl_expr_typeof; eauto. inv HP.
      exploit sem_cast_join. apply MJOIN.
      intros A. rewrite H1 in A. inv A. reflexivity.
    - intros. monadInv TR.
      replace (ClightP.genv_cenv ge) with (genv_cenv tge).
      constructor. cbn. monadInv TRANSL. reflexivity.
    - intros. monadInv TR.
      replace (ClightP.genv_cenv ge) with (genv_cenv tge).
      constructor. cbn. monadInv TRANSL. reflexivity.
    - intros. specialize (H0 _ TR).
      econstructor; eauto. cbn.
      erewrite <- transl_expr_typeof; eauto.
      inv HP. exploit deref_loc_join.
      apply MJOIN. apply H1. easy.
    - intros. specialize (H0 _ TR) as (b & ofs & A & B & C & D).
      eapply eval_Elvalue. apply A.
      inv H1. inv HP. specialize (MVALUE _ _ H0) as (b' & Hb & Hv).
      assert (b = b') by congruence. subst b'.
      erewrite <- transl_expr_typeof; eauto.
      eapply pread_val_correct; eauto.
      eapply pvalue_match_join; eauto.
      eapply join_commutative; eauto.
      pose proof (sizeof_pos ce (ClightP.typeof e0)). lia.
    - intros. monadInv TR.
      eapply eval_Evar_local; eauto.
    - intros. monadInv TR.
      apply eval_Evar_global; eauto.
    - intros. monadInv TR. constructor. eauto.
    - intros. monadInv TR. monadInv TRANSL. econstructor; eauto.
      erewrite <- transl_expr_typeof; eauto.
    - intros. monadInv TR. monadInv TRANSL.
      eapply eval_Efield_union; eauto.
      erewrite <- transl_expr_typeof; eauto.
    - intros. monadInv TR. inv HP.
      specialize (MVALUE _ _ H0) as (b & Hb & Hv).
      exists b, 0. repeat split.
      + apply Clight.eval_Evar_global; eauto.
      + eauto.
      + constructor.
      (* add condition to the compilation *)
      + apply l.
    - intros. monadInv TR.
      specialize (H _ EQ) as (b & ofs & A & B & C & D).
      specialize (H0 _ EQ1).
      eexists b, _. split.
      (* eval_lvalue *)
      + constructor. econstructor.
        * eapply Clight.eval_Elvalue. apply A.
          apply deref_loc_reference.
          erewrite <- transl_expr_typeof; eauto.
          rewrite TARR. reflexivity.
        * apply H0.
        * erewrite <- !transl_expr_typeof; eauto.
          rewrite TARR. rewrite TI. reflexivity.
      + split; eauto.
        assert (0 <= ofs <= Ptrofs.max_unsigned) as X.
        {
          split.
          - apply Z.ge_le. eapply match_loc_pos; eauto.
          - pose proof (sizeof_pos ce (ClightP.typeof earr)). lia.
        }
        assert (0 <= sizeof ce ty_elem <= Ptrofs.max_unsigned) as Y.
        {
          split. apply Z.ge_le. apply sizeof_pos.
          transitivity (sizeof ce (ClightP.typeof earr)); try lia.
          rewrite TARR. cbn. rewrite Z.max_r; try lia.
          transitivity (sizeof ce ty_elem * 1). lia.
          apply Z.mul_le_mono_nonneg_l; try lia.
          apply Z.ge_le. apply sizeof_pos.
        }
        assert (0 <= Int.intval i <= Ptrofs.max_unsigned) as Z.
        {
          pose proof (Int.intrange i). split; try lia.
          pose proof int_max_le_ptrofs_max. lia.
        }
        replace (Ptrofs.unsigned (Ptrofs.repr ofs) +
                   Ptrofs.unsigned (Ptrofs.mul (Ptrofs.repr (sizeof tge ty_elem))
                                      (ptrofs_of_int Unsigned i)))
          with (ofs + sizeof ce ty_elem * (Int.intval i)).
        2: {
          rewrite Ptrofs.unsigned_repr; eauto.
          f_equal.
          replace (sizeof tge ty_elem) with (sizeof ce ty_elem).
          2: { unfold ce, tge. cbn. monadInv TRANSL. reflexivity. }
          remember (sizeof ce ty_elem) as z in *.
          cbn. unfold Ptrofs.of_intu. unfold Ptrofs.of_int.
          unfold Int.unsigned.
          unfold Ptrofs.mul. rewrite !Ptrofs.unsigned_repr; eauto.
          rewrite !Ptrofs.unsigned_repr; eauto.
          split. apply Z.mul_nonneg_nonneg; lia.
          transitivity (sizeof ce (ClightP.typeof earr)); try lia.
          rewrite TARR. cbn. rewrite Z.max_r; try lia.
          rewrite <- Heqz.
          apply Z.mul_le_mono_nonneg_l; try lia.
          unfold Int.unsigned in BOUND. lia.
        }
        split.
        (* match_loc *)
        * eapply match_loc_app_index; eauto. apply Z.mul_comm.
        (* max_unsigned *)
        * eapply Z.le_lt_trans with (m := (ofs + sizeof ce (ClightP.typeof earr))); eauto.
          rewrite <- Z.add_assoc.
          apply Z.add_le_mono_l. cbn.
          rewrite TARR. cbn.
          revert Y. generalize (sizeof ce ty_elem). intros z Y.
          rewrite Z.max_r by lia.
          transitivity (z * (Int.intval i + 1)); try lia.
          apply Zmult_le_compat_l; try lia.
          unfold Int.unsigned in BOUND. lia.
    - intros. monadInv TR.
      specialize (H _ EQ) as (b & ofs_start & A & B & C & D).
      monadInv TRANSL. eexists b, _.
      assert (ofs_start >= 0).
      { eapply match_loc_pos; eauto. }
      assert (sizeof ce ty_field >= 0).
      { eapply sizeof_pos. }
      assert (sizeof ce (ClightP.typeof estruct) >= 0).
      { eapply sizeof_pos. }
      repeat apply conj; eauto.
      (* eval_lvalue *)
      + econstructor; eauto.
        * eapply Clight.eval_Elvalue. apply A.
          apply deref_loc_copy.
          erewrite <- transl_expr_typeof; eauto.
          rewrite TSTRUCT. reflexivity.
        * erewrite <- !transl_expr_typeof; eauto.
      (* match_loc *)
      + rewrite !Ptrofs.unsigned_repr; eauto.
        * eapply match_loc_app_field; eauto. apply Hconsistent.
        * edestruct Ctypes.field_offset_in_range as [X Y]; eauto.
          eapply field_offset_size with (attr := noattr) in HF; eauto.
          split; eauto. rewrite TSTRUCT in D. lia. apply Hconsistent.
        * split; lia.
      + rewrite !Ptrofs.unsigned_repr; eauto.
        * cut (ofs + sizeof ce ty_field <= sizeof ce (ClightP.typeof estruct)).
          cbn in *. lia. rewrite TSTRUCT. eapply field_offset_size; eauto.
          apply Hconsistent.
        * edestruct Ctypes.field_offset_in_range as [X Y]; eauto.
          eapply field_offset_size with (attr := noattr) in HF; eauto.
          split; eauto. rewrite TSTRUCT in D. lia.
          apply Hconsistent.
        * split; lia.
  Qed.

  Lemma eval_expr_correct:
    forall e le m tm pe,
      penv_match ce se (pe, m) tm ->
      forall expr v,
          ClightP.eval_expr ce ge e le pe m expr v ->
          forall texpr (TR: transl_expr ce expr = OK texpr),
            Clight.eval_expr tge e le tm texpr v.
  Proof. apply eval_expr_lvalue_correct. Qed.

  Lemma eval_lvalue_correct:
    forall e le m tm pe,
      penv_match ce se (pe, m) tm ->
      forall expr b ofs bf,
        ClightP.eval_lvalue ce ge e le pe m expr b ofs bf ->
        forall texpr (TR: transl_expr ce expr = OK texpr),
          Clight.eval_lvalue tge e le tm texpr b ofs bf.
  Proof. apply eval_expr_lvalue_correct. Qed.

  Lemma eval_loc_correct:
    forall e le m tm pe,
      penv_match ce se (pe, m) tm ->
      forall expr id l,
        ClightP.eval_loc ce ge e le pe m expr id l ->
        forall texpr (TR: transl_expr ce expr = OK texpr),
        exists b ofs, Clight.eval_lvalue tge e le tm texpr b (Ptrofs.repr ofs) Full
                 /\ Genv.find_symbol se id = Some b
                 /\ match_loc ce l ofs
                 /\ ofs + sizeof ce (ClightP.typeof expr) < Ptrofs.max_unsigned.
  Proof. apply eval_expr_lvalue_correct. Qed.

  Lemma eval_exprlist_correct:
    forall e le m tm pe,
      penv_match ce se (pe, m) tm ->
      forall es tys vs,
          ClightP.eval_exprlist ce ge e le pe m es tys vs ->
          forall tes (TR: transl_exprlist ce es = OK tes),
            Clight.eval_exprlist tge e le tm tes tys vs.
  Proof.
    intros until es. induction es.
    - intros. monadInv TR. inv H0. constructor.
    - intros * HEV * HTR.
      monadInv HTR. inv HEV. inv H.
      exploit sem_cast_join. apply MJOIN.
      intros A. rewrite H3 in A. inv A.
      econstructor; eauto.
      eapply eval_expr_correct; eauto. econstructor; eauto.
      erewrite <- transl_expr_typeof; eauto.
  Qed.

(** ------------------------------------------------------------------------- *)
(** Some properties about global definitions: because there are new global
    variables, some lemmas are not applicable  *)
  Inductive pmatch_globdef: globdef ClightP.fundef type ->
                            globdef Clight.fundef type -> Prop :=
  | pmatch_globvar i ty tty init ro vo:
    transl_globvar i ty = OK tty ->
    pmatch_globdef (Gvar (mkglobvar ty init ro vo)) (Gvar (mkglobvar tty init ro vo))
  | pmatch_globfun i f tf:
    transl_fundef ce i f = OK tf ->
    pmatch_globdef (Gfun f) (Gfun tf).

  Lemma def_translated defs tdefs:
    transf_globdefs (transl_fundef ce) transl_globvar defs = OK tdefs ->
    forall i, Coqlib.option_rel pmatch_globdef
           (PTree_Properties.of_list defs)!i
           (PTree_Properties.of_list tdefs)!i.
  Proof.
    intros H i.
    eapply PTree_Properties.of_list_related.
    revert defs tdefs H.
    induction defs.
    - intros. monadInv H. constructor.
    - intros. cbn in H. destruct a. destruct g.
      (* fundef *)
      + destruct transl_fundef eqn: TF; monadInv H.
        constructor; eauto. split; cbn; eauto.
        econstructor; eauto.
      + monadInv H. constructor; eauto.
        split; cbn; eauto. destruct v. cbn. econstructor.
        reflexivity.
        Unshelve. eauto.
  Qed.

  Lemma fundef_translated i defs tdefs fd:
    transf_globdefs (transl_fundef ce) transl_globvar defs = OK tdefs ->
    (PTree_Properties.of_list defs) ! i = Some (Gfun fd) ->
    exists tfd, (PTree_Properties.of_list tdefs) ! i = Some (Gfun tfd) /\
             (transl_fundef ce) i fd = OK tfd.
  Proof.
    intros H HF. eapply def_translated with (i:=i) in H.
    inv H. congruence. rewrite HF in H0. inv H0.
    inv H2. eexists. split; eauto.
  Qed.

  Lemma pmatch_find_def b g:
    Genv.find_def (ClightP.genv_genv ge) b = Some g ->
    exists tg, Genv.find_def tge b = Some tg /\ pmatch_globdef g tg.
  Proof.
    intros H. subst ge tge. monadInv TRANSL.
    setoid_rewrite Genv.find_def_spec in H.
    destruct (Genv.invert_symbol se b) eqn: HX; try congruence.
    eapply def_translated with (i:=i) in EQ.
    setoid_rewrite H in EQ. inv EQ. exists y.
    split.
    setoid_rewrite Genv.find_def_spec. rewrite HX.
    unfold prog_defmap. cbn - [PTree_Properties.of_list].
    rewrite PTree_Properties.of_list_elements.
    eapply ptree_of_list_app. congruence. eauto.
  Qed.

  Lemma functions_translated v fd:
    Genv.find_funct (ClightP.genv_genv ge) v = Some fd ->
    exists i tfd, Genv.find_funct tge v = Some tfd /\ transl_fundef ce i fd = OK tfd.
  Proof.
    generalize pmatch_find_def. intros MFD.
    intros H. subst ge tge. monadInv TRANSL.
    unfold Genv.find_funct in *. destruct v; try congruence.
    destruct Ptrofs.eq_dec; try congruence. subst.
    unfold Genv.find_funct_ptr in *.
    destruct Genv.find_def eqn: FD; try congruence.
    destruct g; inv H.
    specialize (MFD _ _ FD).
    destruct MFD as (tg & HT1 & HT2).
    inv HT2. eexists _, tf.
    rewrite HT1. split; eauto.
  Qed.

  Lemma type_of_fundef_preserved id fd tfd:
    transl_fundef ce id fd = OK tfd -> ClightP.type_of_fundef fd = type_of_fundef tfd.
  Proof.
    intros H. destruct fd.
    - monadInv H. cbn. destruct f. monadInv EQ. cbn. reflexivity.
    - monadInv H. reflexivity.
  Qed.

(** ------------------------------------------------------------------------- *)
(** Monotonicity *)

  Lemma external_call_match ef vargs pe m tm t vres m':
    penv_match ce se (pe, m) tm ->
    external_call ef (ClightP.genv_genv ge) vargs m t vres m' ->
    exists tm', external_call ef tge vargs tm t vres tm' /\ penv_match ce se (pe, m') tm'.
  Proof.
    intros. inv H. exploit external_call_join; eauto.
    intros (? & ? & ?). eexists; split; eauto.
    econstructor; eauto.
  Qed.

  Lemma free_list_load:
    forall chunk b l m m',
      Mem.free_list m l = Some m' ->
      (forall lo hi, In (b, lo, hi) l ->
                lo >= hi \/ size_chunk chunk <= lo \/ hi <= 0) ->
      Mem.load chunk m' b 0 = Mem.load chunk m b 0.
  Proof.
    induction l; simpl; intros.
    inv H; auto.
    destruct a. destruct p.
    destruct Mem.free as [m1|] eqn:?; try discriminate.
    transitivity (Mem.load chunk m1 b 0).
    - apply IHl. auto. eauto.
    - eapply Mem.load_free. eauto.
      destruct (peq b b0). 2: eauto. subst. right.
      apply H0. left; eauto.
  Qed.

  Lemma free_list_perm:
    forall b ofs l m m' p k,
      Mem.free_list m l = Some m' ->
      (forall lo hi, In (b, lo, hi) l -> ofs < lo \/ hi <= ofs) ->
      Mem.perm m b ofs p k -> Mem.perm m' b ofs p k.
  Proof.
    induction l; simpl; intros.
    inv H; auto.
    destruct a. destruct p0.
    destruct Mem.free as [m1|] eqn:?; try discriminate.
    eapply IHl; eauto.
    eapply Mem.perm_free_1; eauto.
      destruct (peq b b0). 2: eauto. subst. right.
      apply H0. left; eauto.
  Qed.

  Lemma free_list_match pe m bs m' tm:
    Mem.free_list m bs = Some m' -> penv_match ce se (pe, m) tm ->
    exists tm', Mem.free_list tm bs = Some tm' /\ penv_match ce se (pe, m') tm'.
  Proof.
    intros A B. inv B.
    exploit Join.free_list_join; eauto.
    intros C. rewrite A in C. inv C.
    eexists. split; eauto.
    econstructor; eauto.
  Qed.

  Lemma alloc_variables_join pm e m vs e' m' tm:
    ClightP.alloc_variables ge e m vs e' m' -> join pm m tm ->
    exists tm', alloc_variables tge e tm vs e' tm' /\ join pm m' tm'.
  Proof.
    intros H Hm. revert tm Hm. induction H.
    - intros; eexists. split; [ constructor | eauto ].
    - intros.
      exploit alloc_join; eauto.
      intros A. rewrite H in A. inv A. inv H3.
      destruct y. cbn in *. subst.
      specialize (IHalloc_variables _ H1) as (tm' & A & B).
      exists tm'. split; eauto.
      econstructor; eauto.
      replace (sizeof tge ty) with (sizeof (ClightP.genv_cenv ge) ty); eauto.
      monadInv TRANSL. subst tge. reflexivity.
  Qed.

  Lemma bind_parameters_join pm e m ps vs m' tm:
    ClightP.bind_parameters ge e m ps vs m' -> join pm m tm ->
    exists tm', bind_parameters tge e tm ps vs tm' /\ join pm m' tm'.
  Proof.
    intros H Hm. revert tm Hm. induction H.
    - intros; eexists. split; [ constructor | eauto ].
    - intros.
      exploit assign_loc_join; eauto. intros (tm' & A & B).
      specialize (IHbind_parameters _ B) as (mx & C & D).
      exists mx. split; eauto.
      econstructor; eauto.
      monadInv TRANSL. subst tge.  eauto.
  Qed.

  Lemma pmatch_function_entry1 pe m tm f tf vargs m' e le:
    penv_match ce se (pe, m) tm ->
    transl_function ce f = OK tf ->
    ClightP.function_entry1 ge f vargs m e le m' ->
    exists tm', function_entry1 tge tf vargs tm e le tm' /\
             penv_match ce se (pe, m') tm'.
  Proof.
    intros PM TR FE. inv FE. inv PM.
    edestruct alloc_variables_join as (? & ? & ?); eauto.
    edestruct bind_parameters_join as (? & ? & ?); eauto.
    eexists. split.
    - econstructor; eauto; monadInv TR; cbn; eauto.
      inv MJOIN. inv mjoin_alloc_flag; congruence.
    - econstructor; eauto.
  Qed.

  Lemma pmatch_function_entry2 pe m tm f tf vargs m' e le:
    penv_match ce se (pe, m) tm ->
    transl_function ce f = OK tf ->
    ClightP.function_entry2 ge f vargs m e le m' ->
    exists tm', function_entry2 tge tf vargs tm e le tm' /\
             penv_match ce se (pe, m') tm'.
  Proof.
    intros PM TR FE. inv FE. inv PM.
    edestruct alloc_variables_join as (? & ? & ?); eauto.
    eexists. split.
    - econstructor; eauto; monadInv TR; cbn; eauto.
      inv MJOIN. inv mjoin_alloc_flag; congruence.
    - econstructor; eauto.
  Qed.

(** ------------------------------------------------------------------------- *)
(** Simulation *)
  Lemma pmatch_call_cont pe k kt:
    pmatch_cont (k, pe) kt ->
    pmatch_cont (ClightP.call_cont k, pe) (call_cont kt).
  Proof.
    intros H.
    set (P := fun '(k, pe) kt => pmatch_cont (ClightP.call_cont k, pe) (call_cont kt)).
    eapply pmatch_cont_ind with (P := P) in H; subst P; cbn; eauto.
    constructor.
    intros. constructor; eauto.
  Qed.

  Lemma pmatch_is_call_cont pe k kt:
    pmatch_cont (k, pe) kt ->
    ClightP.is_call_cont k ->
    Clight.is_call_cont kt.
  Proof. intros. inv H; auto. Qed.

  Lemma blocks_of_env_same e:
    ClightP.blocks_of_env ge e = blocks_of_env tge e.
  Proof.
    unfold ClightP.blocks_of_env, blocks_of_env.
    f_equal.
    unfold ClightP.block_of_binding, block_of_binding.
    subst ge tge. monadInv TRANSL. cbn. reflexivity.
  Qed.

  Lemma transl_select_switch n sl tsl:
    transl_lbl_stmt ce sl = OK tsl ->
    transl_lbl_stmt ce (ClightP.select_switch n sl) = OK (select_switch n tsl).
  Proof.
    revert sl tsl.
    assert (DFL:
             forall sl tsl,
               transl_lbl_stmt ce sl = OK tsl ->
               transl_lbl_stmt ce (ClightP.select_switch_default sl) =
                 OK (select_switch_default tsl)
           ).
    {
      induction sl; simpl; intros; monadInv H; cbn; eauto.
      match goal with
      | [ H: option _ |- _] => destruct H
      end.
      eauto. cbn. rewrite EQ. cbn.
      unfold transl_lbl_stmt.
      rewrite EQ1. reflexivity.
    }
    assert (CASE:
             forall sl tsl,
               transl_lbl_stmt ce sl = OK tsl ->
               match ClightP.select_switch_case n sl with
               | None => select_switch_case n tsl = None
               | Some sl' =>
                   exists tsl', select_switch_case n tsl = Some tsl' /\
                             transl_lbl_stmt ce sl' = OK tsl'
               end
           ).
    {
      induction sl; simpl; intros; monadInv H; simpl. auto.
      match goal with
      | [ H: option _ |- _] => destruct H
      end.
      destruct (zeq z n). subst.
      eexists; split; eauto. cbn. rewrite EQ.
      unfold transl_lbl_stmt.
      rewrite EQ1; auto.
      apply IHsl; eauto. apply IHsl; eauto.
    }
    intros. unfold ClightP.select_switch, select_switch.
    specialize (CASE _ _ H).
    destruct ClightP.select_switch_case as [sl'|].
    destruct CASE as [tsl' [P Q]]. rewrite P. apply Q.
    rewrite CASE. apply DFL. eauto.
  Qed.

  Lemma transl_seq_of_labeled_statement sl tsl:
    transl_lbl_stmt ce sl = OK tsl ->
    transl_statement ce (ClightP.seq_of_labeled_statement sl) =
      OK (seq_of_labeled_statement tsl).
  Proof.
    revert sl tsl. induction sl; simpl; intros; monadInv H; simpl. auto.
    cbn. unfold transl_statement at 1. rewrite EQ; simpl.
    erewrite IHsl; eauto; cbn; eauto.
  Qed.

  Lemma pmatch_find_label':
    forall lbl s k ts tk pe,
      transl_statement ce s = OK ts ->
      pmatch_cont (k, pe) tk ->
      match ClightP.find_label lbl s k with
      | None => find_label lbl ts tk = None
      | Some(s', k') =>
          exists ts' tk',
          find_label lbl ts tk = Some(ts', tk')
          /\ transl_statement ce s' = OK ts'
          /\ pmatch_cont (k', pe) tk'
      end
  with pmatch_find_label_ls':
    forall lbl sl k tsl tk pe,
      transl_lbl_stmt ce sl = OK tsl ->
      pmatch_cont (k, pe) tk ->
      match ClightP.find_label_ls lbl sl k with
      | None =>
          find_label_ls lbl tsl tk = None
      | Some(s', k') =>
          exists ts' tk',
          find_label_ls lbl tsl tk = Some(ts', tk')
          /\ transl_statement ce s' = OK ts'
          /\ pmatch_cont (k', pe) tk'
      end.
  Proof.
    induction s; simpl; intros until pe; intros TS MC.
    (* skip *)
    - monadInv TS; eauto.
    (* var *)
    - monadInv TS; eauto.
    (* set *)
    - monadInv TS; eauto.
    (* call *)
    - monadInv TS; eauto.
    (* builtin *)
    - monadInv TS; eauto.
    (* seq *)
    - monadInv TS; eauto.
      exploit (IHs1 (ClightP.Kseq s2 k) x (Kseq x0 tk)); eauto.
      econstructor; eauto.
      destruct ClightP.find_label as [[s' k']|].
      + intros. destruct H as (?&?&?&?&?).
        eexists _, _. repeat split; eauto.
        cbn. rewrite H. reflexivity.
      + intros E. cbn. rewrite E. eapply IHs2; eauto.
    (* ifthenelse *)
    - monadInv TS. exploit (IHs1 k x0 tk); eauto.
      destruct ClightP.find_label as [[s' k']|].
      + intros. destruct H as (?&?&?&?&?).
        eexists _, _. split; eauto.
        cbn. rewrite H. reflexivity.
      + intros E. cbn. rewrite E.
        eapply IHs2; eauto.
    (* loop *)
    - monadInv TS.
      exploit (IHs1 (ClightP.Kloop1 s1 s2 k) x (Kloop1 x x0 tk)); eauto.
      constructor; eauto.
      destruct ClightP.find_label as [[s' k']|].
      + intros. destruct H as (?&?&?&?&?).
        eexists _, _. split; eauto.
        cbn. rewrite H. reflexivity.
      + intros E. cbn. rewrite E.
        apply IHs2; eauto. constructor; eauto.
    (* break *)
    - monadInv TS; eauto.
    (* continue *)
    - monadInv TS; eauto.
    (* return *)
    - match goal with
      | [ H: option _ |- _] => destruct H
      end; monadInv TS; eauto.
    (* switch *)
    - monadInv TS. cbn.
      apply pmatch_find_label_ls'; eauto.
      constructor; eauto.
    (* label *)
    - monadInv TS. cbn.
      destruct (ident_eq lbl l).
      + eexists _, _. repeat split; eauto.
      + apply IHs; eauto.
    (* goto *)
    - monadInv TS; eauto.
    - monadInv TS; eauto.

    - induction sl; cbn; intros.
      + monadInv H; eauto.
      + monadInv H; eauto.
        exploit (pmatch_find_label' lbl s
                   (ClightP.Kseq (ClightP.seq_of_labeled_statement sl) k));
          eauto. constructor. eapply transl_seq_of_labeled_statement; eauto.
        eauto.
        destruct ClightP.find_label as [[s' k']|].
        intros. destruct H as (?&?&?&?&?).
        eexists _, _.
        split; cbn; eauto. rewrite H. eauto.
        intros E. cbn. rewrite E. apply IHsl; eauto.
  Qed.

  Lemma pmatch_find_label pe s ts k tk s' k' lbl:
    transl_statement ce s = OK ts ->
    pmatch_cont (k, pe) tk ->
    ClightP.find_label lbl s (ClightP.call_cont k) = Some (s', k') ->
    exists ts' tk',
      find_label lbl ts (call_cont tk) = Some (ts', tk') /\
        transl_statement ce s' = OK ts' /\
        pmatch_cont (k', pe) tk'.
  Proof.
    intros TS MC FL.
    eapply pmatch_call_cont in MC.
    exploit pmatch_find_label'; eauto.
    rewrite FL. easy.
  Qed.

  Lemma pmatch_cont_set_pe k tk pe id v v':
    pe ! id = Some v ->
    pmatch_cont (k, pe) tk ->
    pmatch_cont (k, (PTree.set id v' pe)) tk.
  Proof.
    intros HV MC. revert HV.
    set (P := fun '(k, pe) tk => pe ! id = Some v ->
                              pmatch_cont (k, PTree.set id v' pe) tk).
    eapply pmatch_cont_ind with (P := P) in MC; subst P; cbn; eauto;
      intros; constructor; eauto.
  Qed.

  Lemma step_correct:
    forall s1 pe t s1' pe',
      ClightP.step2 ce ge (s1, pe) t (s1', pe') ->
      forall s2 : state,
        pmatch_state se (s1, pe) s2 ->
        exists s2' : state, Clight.step2 tge s2 t s2' /\ pmatch_state se (s1', pe') s2'.
  Proof.
    induction 1; intros S2 MS; inv MS.
    (* assign *)
    - monadInv TRS. pose proof H2 as HA.
      eapply eval_lvalue_correct in H; eauto.
      eapply eval_expr_correct in H0; eauto.
      inv MP. clear pe. rename pe0 into pe.
      exploit sem_cast_join. eauto.
      rewrite H1. intros X. inv X. symmetry in H4.
      exploit assign_loc_join; eauto. intros (mx & A & B).
      eexists. split.
      (* transition *)
      + econstructor; eauto.
        erewrite <- !transl_expr_typeof; eauto.
        erewrite <- !transl_expr_typeof; eauto.
        monadInv TRANSL. eauto.
      (* simulation relation *)
      + constructor; eauto. econstructor; eauto.
    (* set *)
    - monadInv TRS.
      eapply eval_expr_correct in H; eauto.
      eexists. split; constructor; eauto.
    (* update *)
    - monadInv TRS.
      eapply eval_expr_correct in H0; eauto.
      eapply eval_loc_correct in H as (b & ofs & A & X & B & Y); eauto.
      inv MP. clear pe. rename pe0 into pe.
      inv H1. exploit MVALUE. apply H. intros (bx & C & D).
      rewrite C in X. inv X.
      exploit pwrite_val_correct; eauto. apply Hconsistent.
      intros (tm' & E & F).
      apply join_commutative in MJOIN.
      exploit store_join. apply MJOIN. intros G.
      rewrite E in G. inv G.
      eexists. split.
      (* transition *)
      + econstructor; eauto.
        * erewrite <- !transl_expr_typeof; eauto. rewrite H2.
          apply cast_val_casted; eauto.
        * erewrite <- !transl_expr_typeof; eauto.
          econstructor. rewrite <- H2. eauto.
          unfold Mem.storev. rewrite Ptrofs.unsigned_repr.
          symmetry. apply H5.
          split.
          apply Z.ge_le. eapply match_loc_pos; eauto.
          pose proof (sizeof_pos ce (ClightP.typeof a1)). lia.
      (* simulation relation *)
      + constructor; eauto.
        * eapply pmatch_cont_set_pe; eauto.
        * econstructor. apply join_commutative. eauto.
          intros idx vx G. destruct (peq id idx).
          -- subst. rewrite PTree.gss in G.
             exists b. split; eauto. inv G. eauto.
          -- rewrite PTree.gso in G by congruence.
             exploit MVALUE. apply G. intros (bx & I & J).
             exists bx. split; eauto.
             assert (b <> bx) as K.
             {
               intros contra. subst.
               apply n. eapply Genv.find_symbol_injective; eauto.
             }
             clear - K E J.
             (* pvalue_match unchanged_on *)
             eapply pvalue_match_unchanged; eauto. apply Hconsistent.
             instantiate (1 := (fun bi _ => bi <> b)).
             eapply Mem.store_unchanged_on; eauto.
             intros; cbn. congruence.
    (* call *)
    - monadInv TRS. clear pe. rename pe0 into pe.
      eapply eval_expr_correct in H0; eauto.
      eapply eval_exprlist_correct in H1; eauto.
      exploit functions_translated. eauto. intros (i & tfd & HFD1 & HFD2).
      eexists. split.
      + econstructor; eauto.
        erewrite <- transl_expr_typeof; eauto.
        cbn. unfold ClightP.genv_genv in *. cbn in H2.
        exploit type_of_fundef_preserved. eauto. intros <-. eauto.
      + constructor; eauto.
        constructor; eauto.

    (* builtin *)
    - monadInv TRS.
      eapply eval_exprlist_correct in H; eauto.
      exploit external_call_match; eauto. intros (mt' & HEC & HM).
      eexists. split.
      + econstructor; eauto.
      + constructor; eauto.

    (* sequence *)
    - monadInv TRS.
      eexists. split; repeat (constructor; eauto).

    (* skip sequence *)
    - monadInv TRS. inv MK.
      eexists. split. constructor. constructor; eauto.

    (* continue sequence *)
    - monadInv TRS. inv MK.
      eexists. split. constructor. constructor; eauto.

    (* break sequence *)
    - monadInv TRS. inv MK.
      eexists. split. constructor. constructor; eauto.

    (* ifthenelse *)
    - monadInv TRS. clear pe. rename pe0 into pe.
      inv MP.
      exploit bool_val_join; eauto.
      intros A. rewrite H0 in A. inv A.
      eapply eval_expr_correct in H; eauto.
      eexists. split. econstructor; eauto.
      cbn. erewrite <- transl_expr_typeof; eauto.
      constructor; eauto. destruct y; eauto.
      all: econstructor; eauto.

    (* loop *)
    - monadInv TRS. eexists. split.
      constructor. repeat (constructor; eauto).

    (* skip-or-continue loop *)
    - inv MK. destruct H; subst; monadInv TRS;
        eexists; split; repeat (constructor; eauto).

    (* break loop1 *)
    - monadInv TRS. inv MK. eexists; split.
      eapply step_break_loop1.
      constructor; eauto.

    (* skip loop2 *)
    - monadInv TRS. inv MK. eexists; split.
      constructor. constructor; eauto.
      cbn. rewrite H4. cbn. rewrite H5. reflexivity.

    (* break loop2 *)
    - monadInv TRS. inv MK. eexists; split.
      constructor. constructor; eauto.

    (* return None *)
    - monadInv TRS.
      exploit free_list_match; eauto. intros (tm' & HFL & HM).
      eexists; split.
      constructor. rewrite <- blocks_of_env_same; eauto.
      constructor; eauto.
      apply pmatch_call_cont. auto.

    (* return Some *)
    - monadInv TRS.
      exploit eval_expr_correct; eauto. intros HEV.
      exploit free_list_match; eauto. intros (tm' & HFL & HM).
      inv MP. clear pe. rename pe0 into pe.
      exploit sem_cast_join; eauto.
      intros A. rewrite H0 in A. inv A.
      eexists. split.
      econstructor; eauto.
      erewrite <- transl_expr_typeof; eauto.
      monadInv TRF. symmetry. apply H3.
      rewrite <- blocks_of_env_same. apply HFL.
      constructor; eauto.
      apply pmatch_call_cont. eauto.

    (* skip call *)
    - monadInv TRS.
      exploit free_list_match; eauto. intros (tm' & HFL & HM).
      eexists. split.
      constructor. eapply pmatch_is_call_cont; eauto.
      rewrite <- blocks_of_env_same. eauto.
      constructor; eauto.

    (* switch *)
    - monadInv TRS.
      eapply eval_expr_correct in H; eauto. cbn in *.
      eexists; split.
      econstructor; eauto.
      erewrite <- transl_expr_typeof; eauto.
      constructor; eauto.
      apply transl_seq_of_labeled_statement. apply transl_select_switch. eauto.
      constructor. eauto.

    (* skip-break switch *)
    - inv MK. destruct H; subst;
        monadInv TRS; eexists; split; constructor; eauto.

    (* continue switch *)
    - monadInv TRS. inv MK. eexists. split.
      eapply step_continue_switch.
      constructor; eauto.

    (* label *)
    - monadInv TRS. eexists; split; constructor; eauto.

    (* goto *)
    - monadInv TRS. pose proof TRF. monadInv TRF.
      exploit pmatch_find_label; eauto.
      intros (ts' & tk' & HLB & HS & HK).
      eexists; split.
      constructor; eauto.
      constructor; eauto.

    (* internal function *)
    - exploit functions_translated; eauto. intros (i & tfd & HFD & HTF).
      monadInv HTF.
      exploit pmatch_function_entry2; eauto. intros (tm' & HFE & HM).
      eexists. split.
      constructor; eauto.
      constructor; eauto.
      monadInv EQ. cbn. eauto.

    (* external function *)
    - exploit functions_translated; eauto. intros (i & tfd & HFD & HTF).
      monadInv HTF.
      exploit external_call_match; eauto. intros (tm' & HEC & HM).
      eexists. split.
      econstructor; eauto.
      constructor; eauto.

    (* return *)
    - inv MK.
      eexists. split. constructor. constructor; eauto.
  Qed.

End PRESERVATION.

(** ------------------------------------------------------------------------- *)
(** Correctness of compilation *)

Inductive pin_query R: Memory.mem * Genv.symtbl -> query (li_c @ penv) -> query li_c -> Prop :=
| pin_query_intro se vf sg vargs m msrc mtgt pe
    (MJOIN: join m msrc mtgt)
    (MPE: R se pe m):
  pin_query R (m, se) (cq vf sg vargs msrc, pe) (cq vf sg vargs mtgt).

Inductive pin_reply R: Memory.mem * Genv.symtbl -> reply (li_c @ penv) -> reply li_c -> Prop :=
| pin_reply_intro se rv m msrc mtgt pe
    (MJOIN: join m msrc mtgt)
    (MPE: R se pe m):
  pin_reply R (m, se) (cr rv msrc, pe) (cr rv mtgt).

Program Definition pin ce: callconv (li_c @ penv) li_c :=
  {|
    (* the world is defined as the target program symbol table, which is
       supposed to contain the variables in penv *)
    ccworld := Memory.mem * Genv.symtbl;
    match_senv '(_, se) se1 se2 := se = se1 /\ se = se2;
    match_query := pin_query (penv_mem_match ce);
    match_reply '(_, se) r1 r2 := exists m, pin_reply (penv_mem_match ce) (m, se) r1 r2;
  |}.
Next Obligation. reflexivity. Qed.
Next Obligation. inv H0. reflexivity. Qed.
Next Obligation. inv H. reflexivity. Qed.

Inductive pout_query: Memory.mem -> query li_c -> query li_c -> Prop :=
| pout_query_intro vf sg vargs m msrc mtgt
    (MJOIN: join m msrc mtgt):
  pout_query m (cq vf sg vargs msrc) (cq vf sg vargs mtgt).

Inductive pout_reply: Memory.mem -> reply li_c -> reply li_c -> Prop :=
| pout_reply_intro rv m msrc mtgt
    (MJOIN: join m msrc mtgt):
  pout_reply m (cr rv msrc) (cr rv mtgt).

Program Definition pout: callconv li_c li_c :=
  {|
    ccworld := Memory.mem;
    match_senv _ se1 se2 := se1 = se2;
    match_query := pout_query;
    match_reply := pout_reply;
  |}.
Next Obligation. reflexivity. Qed.
Next Obligation. inv H0. reflexivity. Qed.
Next Obligation. inv H. reflexivity. Qed.

Lemma pairwise_implies_equal:
  forall (A : Type) (l1 l2 : list A),
    (forall i : nat, nth_error l1 i = nth_error l2 i) -> l1 = l2.
intros A l1.
  induction l1 as [| h1 t1].
  - intros l2 H.
    simpl.
    destruct l2 as [| h2 t2].
    + reflexivity.
    + specialize (H 0%nat). inv H.
  - intros l2 H.
    destruct l2 as [| h2 t2].
    + simpl in H.
      specialize (H 0%nat). inv H.
    + simpl in H. f_equal.
      * specialize (H 0%nat). cbn in *. congruence.
      * apply IHt1.
        intros i.
        specialize (H (S i)%nat). apply H.
Qed.

Section CORRECT.

  Import ClightP PTree_Properties.
  Local Opaque PTree_Properties.of_list.
  Context prog tprog (H: transl_program prog = OK tprog).
  Lemma clightp_skel_correct:
    clightp_erase_program prog = erase_program tprog.
  Proof.
    monadInv H.
    unfold clightp_erase_program, erase_program.
    f_equal. cbn.
    rewrite ptree_elements_map.
    apply PTree.elements_extensional. intros id.
    rewrite PTree.gcombine. 2: reflexivity.
    pose proof prog.(prog_norepet) as HR.
    apply list_norepet_app in HR as (HR1 & HR2 & HD).
    assert (map fst (@transl_privvars Clight.fundef (prog_private prog))
            = map fst (prog_private prog)) as Hi.
    {
      unfold transl_privvars. rewrite map_map.
      match goal with
      | [ |- (map ?f _) = _ ] =>
          replace f with (@fst ident privvar)
      end.
      2: {
        apply FunctionalExtensionality.functional_extensionality.
        intros (i, a). reflexivity.
      }
      reflexivity.
    }
    assert (map fst x = map fst (prog_defs prog)) as Hj.
    {
      revert x EQ. generalize (prog_defs prog). induction l.
      - cbn. intros. inv EQ. reflexivity.
      - destruct a. intros x Hx. cbn in Hx.
        destruct g.
        + destruct transl_fundef eqn: Hy; try congruence.
          monadInv Hx.
          cbn. f_equal. apply IHl. eauto.
        + monadInv Hx. cbn. f_equal.
          apply IHl. eauto.
    }
    assert (list_norepet
              (map fst (map (fun '(id0, x0) => (id0, erase_globdef x0))
                          (transl_privvars (prog_private prog) ++ x))))
      as Hk.
    {
      rewrite map_map.
      match goal with
      | [ |- list_norepet (map ?f _) ] =>
          replace f with
          (@fst ident (globdef (Ctypes.fundef Clight.function) type))
      end.
      2: {
        apply FunctionalExtensionality.functional_extensionality.
        intros (i, a). reflexivity.
      }
      rewrite map_app. setoid_rewrite Hi. setoid_rewrite Hj.
      apply list_norepet_app. eauto.
    }
    destruct ((prog_defmap (program_of_program prog)) ! id) eqn: Hs1;
      destruct ((of_list (prog_private prog)) ! id) eqn: Hs2.
    - exfalso. eapply HD.
      apply in_map. apply in_of_list. apply Hs2.
      apply in_map. apply in_of_list. apply Hs1.
      reflexivity.
    - setoid_rewrite PTree_Properties.of_list_norepet.
      + reflexivity.
      + apply Hk.
      + rewrite map_app. apply in_or_app. right.
        apply def_translated with (i := id) in EQ.
        inv EQ. setoid_rewrite Hs1 in H0. congruence.
        apply in_map_iff.
        eexists (id, y). split. f_equal.
        setoid_rewrite Hs1 in H. inv H. inv H1; reflexivity.
        apply in_of_list. easy.
    - setoid_rewrite PTree_Properties.of_list_norepet.
      + reflexivity.
      + apply Hk.
      + rewrite map_app. apply in_or_app. left.
        apply in_map_iff.
        eexists (id, (Gvar (ClightP.transl_privvar p))).
        split; eauto. apply in_map_iff.
        eexists (id, p). split; eauto.
        apply in_of_list; eauto.
    - rewrite of_list_not_in. reflexivity. rewrite map_map.
      match goal with
      | [ |- ~In _ (map ?f _) ] =>
          replace f with
          (@fst ident (globdef (Ctypes.fundef Clight.function) type))
      end.
      2: {
        apply FunctionalExtensionality.functional_extensionality.
        intros (i, a). reflexivity.
      }
      rewrite map_app. setoid_rewrite Hi. setoid_rewrite Hj.
      intros c. apply in_app_or in c as [H|H].
      + apply of_list_dom in H as (v & Hv). congruence.
      + apply of_list_dom in H as (v & Hv).
        setoid_rewrite Hs1 in Hv. congruence.
  Qed.

  Lemma clightp_footprint_correct:
    forall i, footprint_of_program (ClightP.program_of_program prog) i <->
           footprint_of_program tprog i.
  Proof.
    intros id. cbn. monadInv H.
    unfold footprint_of_program.
    apply def_translated with (i:=id) in EQ.
    destruct PTree.get eqn: Hx;
      match goal with
      | [ |- _ <-> match ?y with _ => _ end ] => destruct y eqn: Hy
      end; try easy.
    all: inv EQ; unfold prog_defmap in Hy; cbn in Hy;
      rewrite of_list_elements in Hy.
    - exploit @ptree_of_list_app. symmetry. apply H0.
      intros A. rewrite A in Hy. inv Hy.
      inv H1. reflexivity. destruct f; monadInv H; cbn; easy.
    - exploit @ptree_of_list_app. symmetry. apply H0.
      intros A. rewrite A in Hy. inv Hy.
    - exploit @ptree_of_list_app_none. symmetry. apply H.
      intros A. rewrite A in Hy.
      apply PTree_Properties.in_of_list in Hy.
      unfold transl_privvars in Hy.
      apply list_in_map_inv in Hy as ((a & b) & B & C). inv B.
      reflexivity.
  Qed.

  Theorem transl_program_correct:
    forward_simulation pout (pin prog.(ClightP.prog_comp_env))
      (ClightP.clightp2 prog) (Clight.semantics2 tprog).
  Proof.
    constructor. econstructor.
    apply clightp_skel_correct. apply clightp_footprint_correct.
    intros se1 se2 wb Hse Hse1. instantiate (1 := fun _ _ _ => _). cbn beta.
    eapply forward_simulation_step with (match_states := pmatch_state prog se2).
    - intros. destruct H0. inv H1. destruct Hse. subst.
      exploit functions_translated; eauto.
      intros (i & tfd & A & B). monadInv B.
      eexists. split. econstructor; eauto.
      + unfold ClightP.type_of_function in *. rewrite <- H8.
        unfold type_of_function. monadInv EQ. reflexivity.
      + cbn in *. unfold Ple in *.
        etransitivity; eauto.
        apply mjoin_nextblock in MJOIN.
        rewrite MJOIN. lia.
      + repeat constructor.
        inv MPE. econstructor; eauto.
    - cbn. intros [s1 pe1] s2 [r1 per1] HS HX. inv HX. inv HS. inv MK.
      eexists. split. constructor.
      destruct wb. inv MP.
      eexists. constructor; eauto.
      constructor. inv Hse. eauto.
    - intros * HS HX. destruct wb. destruct s1. inv Hse.
      inv HX. inv HS. inv MP.
      exploit functions_translated; eauto.
      intros (i & tfd & A & B).
      subst f. monadInv B.
      eexists mpersistent, _. split. econstructor; eauto.
      split. constructor; eauto.
      split. constructor.
      intros * HR HY. inv HR. inv HY.
      eexists. split. cbn. constructor.
      constructor; eauto.
      econstructor; eauto.
    - cbn.
      intros. destruct s1, s1'.
      eapply step_correct; eauto.
      destruct wb. destruct Hse. subst.
      eauto.
    - apply well_founded_ltof.
  Qed.

End CORRECT.
