From compcert Require Import
     AST Coqlib Maps Values Integers Errors Events
     Globalenvs Memory Floats Join Ctypes Values Cop Clight.
Require Import Lia.
Require SimplLocalsproof.

(** ------------------------------------------------------------------------- *)
(** PVal and PEnv  *)
Open Scope Z_scope.

Inductive val : Type :=
| Val : Values.val -> type -> val
| Array : Z -> ZMap.t val -> type -> val.
(* TODO: support struct *)
(* | Struct : list ident -> PMap.t val -> val. *)

Definition type_of_pv (pv: val) :=
  match pv with
  | Val _ ty | Array _ _ ty => ty
  end.

Fixpoint size_of_type (t: type): Z :=
  match t with
  | Tint I32 _ _ => 4
  | Tarray t' n _ => size_of_type t' * Z.max 0 n
  | _ => 0
  end.

Inductive init_pv: val -> Prop :=
| init_pv_int attr:
  init_pv (Val (Vint Int.zero) (Tint I32 Unsigned attr))
| init_pv_array n ty_elem attr arr:
  (forall i, 0 <= i < n -> init_pv (ZMap.get i arr)) ->
  (forall i, 0 <= i < n -> type_of_pv (ZMap.get i arr) = ty_elem) ->
  init_pv (Array n arr (Tarray ty_elem n attr)).

Record privvar : Type :=
  mkprivvar {
      pvar_init:> val;
      pvar_spec: init_pv pvar_init;
      pvar_size: size_of_type (type_of_pv pvar_init) < Int.max_unsigned;
    }.


Definition penv : Type := PTree.t val.
(** typed location: the type information is used to calculate the correct
        offset when we establish a relation between penv and CompCert memory *)
Inductive loc : Type := Loc: type -> list (Z * type) -> loc.

(** Again, the type information is used when relate [pread] with
    [deref_loc]. Consider this relation as a specification of the function of
    type [val -> loc -> Values.val * type] *)
Inductive pread_val: val -> loc -> Values.val -> type -> Prop :=
(* TODO: be more tolerent on typing *)
| pread_nil: forall v ty, pread_val (Val v ty) (Loc ty nil) v ty
| pread_cons:
  forall n arr ty ty_elem ty_v i v attr rest,
    0 <= i < n ->
    pread_val (ZMap.get i arr) (Loc ty_v rest) v ty_v ->
    ty = Tarray ty_elem n attr ->
    pread_val (Array n arr ty) (Loc ty_v ((i, ty_elem) :: rest)) v ty_v.

Inductive pread: penv -> ident -> loc -> Values.val -> type -> Prop :=
| pread_intro: forall pe id l pv v ty,
    pe!id = Some pv ->
    pread_val pv l v ty ->
    pread pe id l v ty.

Inductive pwrite_val: val -> loc -> Values.val -> val -> type -> Prop :=
| pwrite_nil: forall old_v new_v ty
                (VTY: val_casted new_v ty),
    pwrite_val (Val old_v ty) (Loc ty nil) new_v (Val new_v ty) ty
| pwrite_cons:
  forall old_arr new_arr n i ty old_pv new_pv rest new_v ty_v attr ty_elem,
    0 <= i < n ->
    old_pv = ZMap.get i old_arr ->
    pwrite_val old_pv (Loc ty_v rest) new_v new_pv ty_v ->
    new_arr = ZMap.set i new_pv old_arr ->
    ty = Tarray ty_elem n attr ->
    pwrite_val (Array n old_arr ty) (Loc ty_v ((i, ty_elem) :: rest))
      new_v (Array n new_arr ty) ty_v.

Inductive pwrite: penv -> ident -> loc -> Values.val -> penv -> type -> Prop :=
| pwrite_intro:  forall pe id l pe' v old_pv new_pv ty ch,
    pe!id = Some old_pv ->
    pwrite_val old_pv l v new_pv ty ->
    pe' =  PTree.set id new_pv pe ->
    access_mode ty = By_value ch ->
    pwrite pe id l v pe' ty.


(** ------------------------------------------------------------------------- *)
(** The relation between persistent environment and memory *)

Section WITH_CE.

  Variable (ce: composite_env).
  (** The relation between a pvalue and memory *)
  Inductive pvalue_match: block -> Z -> val -> Mem.mem -> Prop :=
  | pval_match:
    forall b ofs ty chunk v m
      (ACCESS: access_mode ty = By_value chunk)
      (LOAD: Mem.load chunk m  b ofs = Some v)
      (WRITABLE: Mem.valid_access m chunk b ofs Writable),
      pvalue_match b ofs (Val v ty) m
  | parray_match:
    forall b ofs n parr ty m attr ty_elem
      (TARRAY: ty = Tarray ty_elem n attr)
      (NO_OVERFLOW: ofs + n * sizeof ce ty_elem <= Ptrofs.max_unsigned)
      (TYPE: forall i, 0 <= i < n -> ty_elem = type_of_pv (ZMap.get i parr))
      (MATCH: forall i, 0 <= i < n ->
                   pvalue_match b (ofs + i * sizeof ce ty_elem) (ZMap.get i parr) m),
      pvalue_match b ofs (Array n parr ty) m.

  (** The relation between the penv and memory *)
  Inductive penv_match: Genv.symtbl -> (penv * Mem.mem) -> Mem.mem -> Prop :=
  | penv_match_intro:
    forall se pe m tm mpersistent
      (MJOIN: join mpersistent m tm)
      (MVALUE: forall id v, PTree.get id pe = Some v ->
                       exists b, Genv.find_symbol se id = Some b /\
                              pvalue_match b 0 v mpersistent),
      penv_match se (pe, m) tm.

  Lemma size_type_chunk ty ch:
    access_mode ty = By_value ch ->
    size_chunk ch = sizeof ce ty.
  Proof.
    intros. destruct ty; inv H; cbn in *; try easy.
    - destruct i; destruct s; inv H1; easy.
    - destruct f; inv H1; easy.
  Qed.

  Lemma pvalue_match_unchanged:
    forall P ma mb b ofs pv,
      pvalue_match b ofs pv ma ->
      Mem.unchanged_on P ma mb ->
      (forall i, ofs <= i < ofs + sizeof ce (type_of_pv pv) -> P b i) ->
      pvalue_match b ofs pv mb.
  Proof.
    intros * H HM HP. induction H.
    - cbn in *. erewrite <- size_type_chunk in HP; eauto.
      eapply pval_match; eauto.
      + exploit Mem.load_unchanged_on; eauto.
      + destruct WRITABLE as [A B].
        split; eauto.
        intros x Hx. specialize (A _ Hx).
        eapply Mem.perm_unchanged_on; eauto.
    - eapply parray_match; eauto.
      intros i Hi. apply H; eauto.
      intros x Hx. apply HP.
      subst. cbn.
      clear - Hi Hx TYPE. rewrite Z.max_r. 2: lia.
      specialize (TYPE _ Hi). subst.
      pose proof (sizeof_pos ce (type_of_pv (ZMap.get i parr))).
      revert H Hx. generalize (sizeof ce (type_of_pv (ZMap.get i parr))).
      intros z Hp Hz. split.
      + transitivity (ofs + i * z). 2: apply Hz.
        cut (0 <= i * z). lia. apply Z.mul_nonneg_nonneg; lia.
      + eapply Z.lt_le_trans. apply Hz.
        rewrite <- Z.add_assoc.
        apply Z.add_le_mono_l.
        cut (i + 1 <= n). 2: lia. intros Ha.
        transitivity (z * (i + 1)). lia.
        apply Z.mul_le_mono_nonneg_l; lia.
  Qed.

  Lemma pvalue_match_join:
    forall ma mb m b ofs pv,
      pvalue_match b ofs pv mb ->
      join ma mb m ->
      pvalue_match b ofs pv m.
  Proof.
    intros * H HJ. induction H.
    - eapply pval_match; eauto.
      + exploit load_join. apply HJ. rewrite LOAD.
        intros HO. inv HO. reflexivity.
      + destruct WRITABLE as [A B]. split; eauto.
        intros x Hx. specialize (A _ Hx).
        eapply perm_join; eauto.
    - eapply parray_match; eauto.
  Qed.

  (** The relation between location and pointer offset *)
  Inductive match_loc: loc -> Z -> Prop :=
  | match_base:
    forall ty, match_loc (Loc ty nil) 0
  | match_index:
    forall i rest ofs_start ofs_elem ty ty_v
      (BASE: match_loc (Loc ty_v rest) ofs_start)
      (OFS: ofs_elem = i * sizeof ce ty)
      (NO_OVERLAP: ofs_start + sizeof ce ty_v <= sizeof ce ty)
      (POS: i >= 0),
      match_loc (Loc ty_v ((i, ty) :: rest)) (ofs_start + ofs_elem).

  Lemma int_max_le_ptrofs_max: Int.modulus - 1 <= Ptrofs.max_unsigned.
  Proof.
    unfold Int.modulus, Ptrofs.max_unsigned, Ptrofs.modulus.
    assert (Int.wordsize <= Ptrofs.wordsize)%nat.
    unfold Ptrofs.wordsize, Int.wordsize, Wordsize_32.wordsize, Wordsize_Ptrofs.wordsize.
    destruct Archi.ptr64; lia.
    assert (two_power_nat Int.wordsize <= two_power_nat Ptrofs.wordsize).
    {
      rewrite !two_power_nat_two_p.
      apply two_p_monotone. extlia.
    }
    lia.
  Qed.

  Lemma match_loc_app:
    forall l ofs_start i ty ofs_elem ty_prev n attr,
      match_loc (Loc ty_prev l) ofs_start ->
      ofs_elem = i * sizeof ce ty ->
      ty_prev = Tarray ty n attr ->
      0 <= i < n ->
      match_loc (Loc ty (l ++ (i, ty) :: nil)) (ofs_start + ofs_elem).
  Proof.
    intros l. induction l.
    - intros * A B C D.
      inv A. cbn.
      replace (i * sizeof ce ty) with (0 + i * sizeof ce ty) by reflexivity.
      constructor; eauto. constructor. reflexivity. lia.
    - intros * A B C D. inv A. rewrite <- app_comm_cons.
      replace (ofs_start0 + i0 * sizeof ce ty0 + i * sizeof ce ty)
        with (ofs_start0 + i * sizeof ce ty + i0 * sizeof ce ty0)
        by lia.
      constructor; eauto.
      cbn in *. revert NO_OVERLAP.
      generalize (sizeof_pos ce ty).
      generalize (sizeof ce ty). intros z A B.
      transitivity (ofs_start0 + z * Z.max 0 n); eauto.
      rewrite <- Z.add_assoc.
      apply Z.add_le_mono_l.
      rewrite Z.max_r by lia.
      transitivity (z * (i + 1)); try lia.
      apply Z.mul_le_mono_nonneg_l; lia.
  Qed.

  (** Correctness of [pread] and [pwrite] *)

  (** This lemma represents the following diagram
    pv ---- loc ---->  v
    |                  |
  match                =
    |                  |
    m --- (b, ofs) --> v *)
  Lemma pread_val_correct':
    forall pv l ty ofs v tm base b,
      pread_val pv l v ty ->
      match_loc l ofs ->
      pvalue_match b base pv tm ->
      base + ofs <= Ptrofs.max_unsigned ->
      base >= 0 ->
      deref_loc ty tm b (Ptrofs.repr (ofs + base)) Full v.
  Proof.
    intros until b. intros H.
    revert base ofs.
    induction H.
    - intros. inv H. inv H0.
      eapply deref_loc_value; eauto.
      cbn.
      rewrite Ptrofs.unsigned_repr; eauto. lia.
    - intros. inv H2. inv H3. inv TARRAY.
      rewrite <- Z.add_assoc.
      apply IHpread_val; eauto.
      rewrite Z.add_comm. eauto.
      lia.
      apply Z.le_ge.
      apply Z.add_nonneg_nonneg; try lia.
      apply Z.mul_nonneg_nonneg; try lia.
      pose proof (sizeof_pos ce ty_elem0). lia.
  Qed.

  Lemma pread_val_correct:
    forall pv l ty ofs v tm b,
      pread_val pv l v ty ->
      match_loc l ofs ->
      pvalue_match b 0 pv tm ->
      ofs <= Ptrofs.max_unsigned ->
      deref_loc ty tm b (Ptrofs.repr ofs) Full v.
  Proof.
    intros. exploit pread_val_correct'; eauto.
    lia. rewrite Z.add_0_r. easy.
  Qed.

  Lemma pwrite_val_type_of_pv:
    forall pv l v pv' ty,
      pwrite_val pv l v pv' ty ->
      type_of_pv pv = type_of_pv pv'.
  Proof. intros * H. induction H; eauto. Qed.

  Lemma match_loc_pos:
    forall l ofs, match_loc l ofs -> ofs >= 0.
  Proof.
    intros * A. induction A. lia.
    subst.
    apply Z.le_ge.
    apply Z.add_nonneg_nonneg; try lia.
    apply Z.mul_nonneg_nonneg; try lia.
    pose proof (sizeof_pos ce ty). lia.
  Qed.

  (** This lemma represents the following diagram
    pv ---- loc ---->  pv'
    |                  |
  match                match
    |                  |
    m --- (b, ofs) --> m' *)
  Lemma pwrite_val_correct':
    forall pv pv' ch l ty base ofs v tm b,
      pwrite_val pv l v pv' ty ->
      match_loc l ofs ->
      pvalue_match b base pv tm ->
      access_mode ty = By_value ch ->
      exists tm', Mem.store ch tm b (base + ofs) v = Some tm'
             /\ pvalue_match b base pv' tm'.
  Proof.
    intros until b. intros H. revert ofs base.
    induction H.
    - intros. inv H. inv H0. rewrite H1 in ACCESS. inv ACCESS.
      rewrite Z.add_0_r.
      edestruct Mem.valid_access_store as (tm' & Hm). eauto.
      exists tm'. split; eauto. econstructor; eauto.
      + erewrite Mem.load_store_same; eauto. f_equal.
        eapply SimplLocalsproof.val_casted_load_result; eauto.
      + eapply Mem.store_valid_access_1; eauto.
    - intros.
      inv H4. inv H5. inv TARRAY.
      exploit MATCH; eauto. intros.
      edestruct IHpwrite_val as (tm' & A & B); eauto.
      exists tm'. split.
      + rewrite <- A. f_equal. rewrite <- Z.add_assoc. f_equal. lia.
      + econstructor; eauto.
        * intros ix Hix. destruct (zeq i ix).
          -- subst. rewrite ZMap.gss.
             erewrite <- pwrite_val_type_of_pv; eauto.
          -- rewrite ZMap.gso by congruence.
             specialize (TYPE _ Hix). eauto.
        * intros ix Hix. destruct (zeq i ix).
          -- subst. rewrite ZMap.gss. apply B.
          -- rewrite ZMap.gso by congruence.
             specialize (MATCH _ Hix).
             specialize (TYPE _ Hix). subst.
             remember (sizeof ce (type_of_pv (ZMap.get ix old_arr)))
               as elem_sz eqn: Hsz.
             eapply pvalue_match_unchanged; eauto.
             instantiate
               (1 := fun (_: block) (ofsx: Z) =>
                       ofsx < base + i * elem_sz + ofs_start
                       \/ ofsx >= base + i * elem_sz + ofs_start + size_chunk ch
               ).
             eapply Mem.store_unchanged_on; eauto.
             intros z Hz. lia.
             cbn. intros z Hz. rewrite <- Hsz in Hz.
             assert (ofs_start + size_chunk ch <= elem_sz).
             { erewrite size_type_chunk; eauto. }
             cut (i < ix \/ i > ix). 2: lia.
             intros [C | C].
             ++ right.
                cut (z >= base + (i+1) * elem_sz); try lia.
                cut (ix * elem_sz >= (i + 1) * elem_sz); try lia.
                apply Zmult_ge_compat_r; lia.
             ++ left.
                cut (ofs_start >= 0).
                cut (ix * elem_sz + elem_sz <= i * elem_sz). lia.
                rewrite Zmult_succ_l_reverse.
                apply Zmult_le_compat_r; lia.
                eapply match_loc_pos. eauto.
  Qed.

  Lemma pwrite_val_correct:
    forall pv pv' ch l ty ofs v tm b,
      pwrite_val pv l v pv' ty ->
      match_loc l ofs ->
      pvalue_match b 0 pv tm ->
      access_mode ty = By_value ch ->
      exists tm', Mem.store ch tm b ofs v = Some tm'
             /\ pvalue_match b 0 pv' tm'.
  Proof. intros. exploit pwrite_val_correct'; eauto. Qed.

End WITH_CE.

Program Definition empty_fragment (b: block) (lo hi: Z) :=
  {|
    Mem.mem_contents := PMap.init (ZMap.init Undef);
    Mem.mem_access :=
      PMap.set b
        (fun ofs k => if zle lo ofs && zlt ofs hi then Some Writable else None)
        (PMap.init (fun ofs k => None));
    Mem.nextblock := Pos.succ b;
    Mem.alloc_flag := false;
  |}.
Next Obligation. Admitted.
Next Obligation. Admitted.

Definition init_fragment' (b: block) (sz: Z) :=
  match store_zeros (empty_fragment b 0 sz) b 0 sz with
  | Some m => m
  | None => Mem.empty
  end.

Definition init_fragment (id: ident) (pv: val) (se: Genv.symtbl) :=
  match Genv.find_symbol se id with
  | Some b => init_fragment' b (size_of_type (type_of_pv pv))
  | None => Mem.empty
  end.

Lemma read_as_zero_weaken m b ofs ofs' len len':
  ofs' >= ofs -> ofs' + len' <= ofs + len ->
  Genv.read_as_zero m b ofs len ->
  Genv.read_as_zero m b ofs' len'.
Proof.
  unfold Genv.read_as_zero. intros. apply H1; eauto; lia.
Qed.

Lemma init_pv_size ce pv ty:
  init_pv pv ->
  ty = type_of_pv pv ->
  size_of_type ty = sizeof ce ty.
Admitted.

Lemma init_pvalue_match ce b pv:
  init_pv pv ->
  pvalue_match ce b 0 pv (init_fragment' b (size_of_type (type_of_pv pv))).
Proof.
  intros H. unfold init_fragment'.
  remember (size_of_type (type_of_pv pv)) as sz.
  assert (exists m, store_zeros (empty_fragment b 0 sz) b 0 sz = Some m)
    as (m & Hm).
  {
    eapply Genv.store_zeros_exists.
    admit.
  }
  rewrite Hm.
  assert (Hp: Mem.range_perm m b 0 (0 + sz) Cur Writable).
  {
    admit.
  }
  eapply Genv.store_zeros_read_as_zero in Hm.
  assert (H0: (4 | 0)). apply Z.divide_0_r.
  revert Hm. revert sz Heqsz H0 Hp. generalize 0.
  induction H; cbn; intros ofs sz Hsz Hdiv Hp Hread.
  - subst. econstructor. reflexivity.
    + specialize (Hread Mint32 ofs).
      exploit Hread; cbn; eauto; try lia.
    + split; eauto.
  - econstructor; eauto.
    + admit.
    + intros i Hi. specialize (H1 i Hi). eauto.
    + intros i Hi. specialize (H0 i Hi).
      eapply H0. reflexivity.
      * admit.
      * admit.
      * rewrite H1; eauto.
        assert (sizeof ce ty_elem >= 0).
        { apply sizeof_pos. }
        eapply read_as_zero_weaken. 3: eauto.
        -- lia.
        -- rewrite <- Z.add_assoc. apply Z.add_le_mono_l.
           rewrite Z.add_comm.
           assert (Hs: size_of_type ty_elem = sizeof ce ty_elem).
           admit.
           rewrite <- Hs. subst. remember (size_of_type ty_elem) as a.
           transitivity (a * (i + 1)). lia.
           apply Z.mul_le_mono_nonneg_l; lia.
Admitted.

Fixpoint p0  (xs: list (ident * val)) : penv :=
  match xs with
  | nil => @PTree.empty val
  | ((id, pv) :: rest) => PTree.set id pv (p0 rest)
  end.

Fixpoint m0 (xs: list (ident * val)) (se: Genv.symtbl) : mem :=
  match xs with
  | nil => Mem.empty
  | ((id, ty) :: rest) => mem_combine (init_fragment id ty se) (m0 rest se)
  end.

(* Definition vars_of_program (p: program) : list (ident * val) := *)

Inductive penv_mem_match ce: Genv.symtbl -> penv -> Mem.mem -> Prop :=
| penv_mem_match_intro se pe m
    (MPE: forall id v, PTree.get id pe = Some v ->
          exists b, Genv.find_symbol se id = Some b /\
          pvalue_match ce b 0 v m):
  penv_mem_match ce se pe m.

Fixpoint init_of_pvars (vs: list (ident * privvar)) : list (ident * val) :=
  match vs with
  | nil => nil
  | (id, v) :: rest => (id, pvar_init v) :: (init_of_pvars rest)
  end.

Lemma vars_init ce pvars se:
  penv_mem_match ce se
    (p0 (init_of_pvars pvars))
    (m0 (init_of_pvars pvars) se).
Admitted.

Variable vars_disjoint: list (ident * val) -> list (ident * val) -> Prop.
Lemma disjoint_init_mem:
  forall se vars1 vars2,
    vars_disjoint vars1 vars2 ->
    join (m0 vars1 se) (m0 vars2 se) (m0 (vars1 ++ vars2) se).
Admitted.
