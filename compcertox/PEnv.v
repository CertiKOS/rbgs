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

Definition type_size_eq ty := forall ce, size_of_type ty = sizeof ce ty.

Inductive init_pv: val -> Prop :=
| init_pv_int attr:
  init_pv (Val (Vint Int.zero) (Tint I32 Unsigned attr))
| init_pv_array n ty_elem attr arr
  (HV: forall i, 0 <= i < n -> init_pv (ZMap.get i arr))
  (HT: forall i, 0 <= i < n -> type_of_pv (ZMap.get i arr) = ty_elem)
  (HS: type_size_eq ty_elem):
  init_pv (Array n arr (Tarray ty_elem n attr)).

Record privvar : Type :=
  mkprivvar {
      pvar_init:> val;
      pvar_spec: init_pv pvar_init;
      pvar_size: size_of_type (type_of_pv pvar_init) <= Ptrofs.max_unsigned;
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
Next Obligation.
  destruct (PMap.elt_eq b b0).
  - subst. rewrite PMap.gss.
    destruct (zle lo ofs && zlt ofs hi); cbn; auto with mem.
  - rewrite PMap.gso; eauto.
    simpl. easy.
Qed.
Next Obligation.
  assert (b0 <> b). intros <-. unfold Plt in H. lia.
  rewrite PMap.gso; eauto.
Qed.

Definition init_fragment' (b: block) (sz: Z) :=
  match store_zeros (empty_fragment b 0 sz) b 0 sz with
  | Some m => m
  | None => Mem.empty_fragment
  end.

Definition init_fragment (id: ident) (pv: val) (se: Genv.symtbl) :=
  match Genv.find_symbol se id with
  | Some b => init_fragment' b (size_of_type (type_of_pv pv))
  | None => Mem.empty_fragment
  end.

Lemma read_as_zero_weaken m b ofs ofs' len len':
  ofs' >= ofs -> ofs' + len' <= ofs + len ->
  Genv.read_as_zero m b ofs len ->
  Genv.read_as_zero m b ofs' len'.
Proof.
  unfold Genv.read_as_zero. intros. apply H1; eauto; lia.
Qed.

Lemma init_pv_size_eq pv:
  init_pv pv -> type_size_eq (type_of_pv pv).
Proof.
  intros H ce. destruct H.
  - subst. reflexivity.
  - subst. cbn. erewrite HS. reflexivity.
Qed.

Lemma size_of_type_pos: forall ty, 0 <= size_of_type ty.
Proof.
  intros. induction ty; cbn; try lia.
  destruct i; lia.
Qed.

Lemma size_of_type_div4: forall ty, (4 | size_of_type ty).
Proof.
  induction ty; try apply Z.divide_0_r; cbn.
  - destruct i; try apply Z.divide_0_r. apply Z.divide_refl.
  - apply Z.divide_mul_l; eauto.
Qed.

Lemma init_pvalue_match ce b pv:
  init_pv pv ->
  size_of_type (type_of_pv pv) <= Ptrofs.max_unsigned ->
  pvalue_match ce b 0 pv (init_fragment' b (size_of_type (type_of_pv pv))).
Proof.
  intros H Hsz. unfold init_fragment'.
  remember (size_of_type (type_of_pv pv)) as sz.
  assert (Hp0: Mem.range_perm
                (empty_fragment b 0 sz) b 0 (0 + sz) Cur Writable).
  {
    intros i Hi. unfold Mem.perm. cbn.
    rewrite PMap.gss.
    destruct zle; destruct zlt; cbn; try lia.
    eauto with mem.
  }
  assert (exists m, store_zeros (empty_fragment b 0 sz) b 0 sz = Some m)
    as (m & Hm).
  { eapply Genv.store_zeros_exists; eauto. }
  rewrite Hm.
  assert (Hp: Mem.range_perm m b 0 (0 + sz) Cur Writable).
  {
    intros i Hi. specialize (Hp0 i Hi).
    eapply Genv.store_zeros_perm in Hm.
    apply Hm. eauto.
  }
  eapply Genv.store_zeros_read_as_zero in Hm.
  assert (H0: (4 | 0)). apply Z.divide_0_r.
  assert (Ha: 0 + sz <= Ptrofs.max_unsigned).
  { transitivity sz. lia. subst. eauto. }
  revert Hm. clear Hp0. clear Hsz.
  revert sz Heqsz Ha H0 Hp. generalize 0.
  induction H; cbn -[Ptrofs.max_unsigned];
    intros ofs sz Ha Hsz Hdiv Hp Hread.
  - subst. econstructor. reflexivity.
    + specialize (Hread Mint32 ofs).
      exploit Hread; cbn; eauto; try lia.
    + split; eauto.
  - econstructor; eauto.
    + transitivity (ofs + sz); eauto.
      apply Z.add_le_mono_l. subst. rewrite <- HS.
      rewrite Z.mul_comm.
      apply Z.mul_le_mono_nonneg_l.
      apply size_of_type_pos. lia.
    + intros i Hi. specialize (HT i Hi). eauto.
    + intros i Hi. specialize (HV i Hi).
      remember (size_of_type ty_elem) as a.
      assert (Hofs: ofs + i * a + a <= ofs + sz).
      {
        rewrite <- Z.add_assoc. apply Z.add_le_mono_l.
        rewrite Z.add_comm.
        transitivity (a * (i + 1)). lia.
        subst. apply Z.mul_le_mono_nonneg_l.
        apply size_of_type_pos. lia.
      }
      eapply H; eauto.
      * rewrite HT; eauto. rewrite <- HS.
        transitivity (ofs + sz); eauto.
        subst; apply Hofs.
      * rewrite <- HS.
        apply Z.divide_add_r; eauto.
        apply Z.divide_mul_r. subst. apply size_of_type_div4.
      * intros o Ho. apply Hp. rewrite <- HS in Ho. split.
        -- pose proof (size_of_type_pos ty_elem). subst. lia.
        -- rewrite HT in Ho; eauto. subst. lia.
      * rewrite HT; eauto. rewrite <- HS; eauto.
        eapply read_as_zero_weaken. 3: eauto.
        -- pose proof (size_of_type_pos ty_elem). lia.
        -- subst. apply Hofs.
Qed.

Fixpoint p0  (xs: list (ident * val)) : penv :=
  match xs with
  | nil => @PTree.empty val
  | ((id, pv) :: rest) => PTree.set id pv (p0 rest)
  end.

Fixpoint m0 (xs: list (ident * val)) (se: Genv.symtbl) : mem :=
  match xs with
  | nil => Mem.empty_fragment
  | ((id, ty) :: rest) => mem_combine (init_fragment id ty se) (m0 rest se)
  end.

Definition valid_pvars (pvars: list (ident * privvar)) se :=
  forall id p, In (id, p) pvars ->
  exists b, Genv.find_symbol se id = Some b.

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

Lemma pvalue_match_invariant ce b ofs v m m':
  type_size_eq (type_of_pv v) ->
  pvalue_match ce b ofs v m ->
  (forall i, ofs <= i < ofs + size_of_type (type_of_pv v) ->
        ZMap.get i (Mem.mem_contents m) !! b =
          ZMap.get i (Mem.mem_contents m') !! b) ->
  (forall i k p, ofs <= i < ofs + size_of_type (type_of_pv v) ->
            Mem.perm m b i k p -> Mem.perm m' b i k p) ->
  pvalue_match ce b ofs v m'.
Proof.
  intros HV H HM HP. induction H.
  - cbn in *.
    exploit size_type_chunk. eauto. intros Hc.
    erewrite <- HV in Hc; eauto.
    eapply pval_match; eauto.
    + edestruct Mem.valid_access_load with (m := m') as (v' & Hv').
      destruct WRITABLE. split; eauto.
      intros i Hi. specialize (r i Hi). instantiate (1 := b).
      apply HP. lia. eauto with mem.
      exploit Mem.load_rep; [ | apply LOAD | apply Hv' | congruence ].
      intros. apply HM. lia.
    + destruct WRITABLE as [A B].
      split; eauto.
      intros x Hx. specialize (A _ Hx).
      apply HP. lia. eauto with mem.
  - econstructor; eauto.
    intros i Hi.
    assert (HT: type_size_eq ty_elem).
    { intros ce'. subst. specialize (HV ce'). cbn in HV.
      apply Z.mul_cancel_r in HV. eauto. lia. }
    apply H; eauto.
    + erewrite TYPE in HT; eauto.
    + erewrite <- TYPE; eauto. rewrite <- HT.
      intros o Ho. apply HM. cbn.
      pose proof (size_of_type_pos ty_elem).
      remember (size_of_type ty_elem) as a.
      split. lia.
      eapply Z.lt_le_trans. apply Ho.
      rewrite <- Z.add_assoc.
      apply Z.add_le_mono_l.
      transitivity (a * (i + 1)). lia.
      subst. cbn. apply Z.mul_le_mono_nonneg_l; lia.
    + erewrite <- TYPE; eauto. rewrite <- HT.
      intros o k p Ho. apply HP. cbn.
      pose proof (size_of_type_pos ty_elem).
      remember (size_of_type ty_elem) as a.
      split. lia.
      eapply Z.lt_le_trans. apply Ho.
      rewrite <- Z.add_assoc.
      apply Z.add_le_mono_l.
      transitivity (a * (i + 1)). lia.
      subst. cbn. apply Z.mul_le_mono_nonneg_l; lia.
      Unshelve. eauto.
Qed.

Lemma pvalue_match_content ce b ofs v m:
  init_pv v -> pvalue_match ce b ofs v m ->
  (forall i, ofs <= i < ofs + size_of_type (type_of_pv v) ->
        ZMap.get i (Mem.mem_contents m) !! b <> Undef).
Proof.
  intros HPV H. induction H.
  - intros i Hi Hv. inv HPV.
    eapply Mem.load_result in LOAD.
    cbn in *. inv ACCESS. cbn in LOAD.
    replace (Pos.to_nat 4) with (4%nat) in LOAD by reflexivity.
    unfold decode_val in LOAD.
    destruct proj_bytes eqn: BYTES.
    + apply inj_proj_bytes in BYTES.
      exploit Mem.getN_in.
      replace 4 with (Z.of_nat 4) in Hi by reflexivity.
      apply Hi. rewrite Hv. intros Hx.
      unfold inj_bytes in BYTES.
      rewrite BYTES in Hx. apply list_in_map_inv in Hx.
      destruct Hx as (? & ?). easy.
    + destruct Archi.ptr64; try congruence.
      cbn [Val.load_result] in *.
      destruct proj_value eqn: Hj; try congruence.
      2: { destruct Archi.ptr64; congruence. }
      inv LOAD.
      assert (HU: In Undef (Mem.getN 4 ofs (Mem.mem_contents m) !! b)).
      { rewrite <- Hv. apply Mem.getN_in. lia. }
      eapply proj_value_undef with (q := Q32) in HU. congruence.
  - inv HPV. intros i Hi. cbn in Hi.
    assert (Z.max 0 n = n). lia. rewrite H0 in Hi. inv H3.
    remember (size_of_type ty_elem) as a.
    pose proof (size_of_type_pos ty_elem).
    assert (0 <= (i - ofs) / a < n).
    { split.
      - apply Z.div_pos; lia.
      - apply Z.div_lt_upper_bound; lia. }
    eapply H with (i := (i - ofs) / a); eauto.
    rewrite <- HS.
    rewrite <- TYPE; eauto. rewrite <- Heqa. split.
    + assert ((i - ofs) - (i - ofs) / a * a >= 0). 2: lia.
      rewrite <- Zmod_eq_full. 2: lia.
      assert (0 <= (i - ofs) mod a). 2: lia.
      apply Z.mod_pos_bound. lia.
    + assert ((i - ofs) - (i - ofs) / a * a < a). 2: lia.
      rewrite <- Zmod_eq_full. 2: lia.
      apply Z.mod_pos_bound. lia.
Qed.

Lemma pvalue_match_perm ce b ofs v m:
  init_pv v -> pvalue_match ce b ofs v m ->
  (forall i, ofs <= i < ofs + size_of_type (type_of_pv v) ->
        Mem.perm m b i Cur Writable).
Proof.
  intros HPV H. induction H.
  - intros i Hi. destruct WRITABLE as [A B]. apply A.
    erewrite size_type_chunk; eauto.
    pose proof (init_pv_size_eq (Val v ty)) as C.
    cbn in *. erewrite C in Hi; eauto.
  (* TODO: clean up the copy-paste *)
  - inv HPV. intros i Hi. cbn in Hi.
    assert (Z.max 0 n = n). lia. rewrite H0 in Hi. inv H3.
    remember (size_of_type ty_elem) as a.
    pose proof (size_of_type_pos ty_elem).
    assert (0 <= (i - ofs) / a < n).
    { split.
      - apply Z.div_pos; lia.
      - apply Z.div_lt_upper_bound; lia. }
    eapply H with (i := (i - ofs) / a); eauto.
    rewrite <- HS.
    rewrite <- TYPE; eauto. rewrite <- Heqa. split.
    + assert ((i - ofs) - (i - ofs) / a * a >= 0). 2: lia.
      rewrite <- Zmod_eq_full. 2: lia.
      assert (0 <= (i - ofs) mod a). 2: lia.
      apply Z.mod_pos_bound. lia.
    + assert ((i - ofs) - (i - ofs) / a * a < a). 2: lia.
      rewrite <- Zmod_eq_full. 2: lia.
      apply Z.mod_pos_bound. lia.
      Unshelve. eauto.
Qed.

Lemma pvalue_match_combine_l ce b ofs v m m':
  init_pv v ->
  pvalue_match ce b ofs v m ->
  pvalue_match ce b ofs v (mem_combine m m').
Proof.
  intros H HM. eapply pvalue_match_invariant; eauto.
  - eauto using init_pv_size_eq.
  - intros i Hi. rewrite mem_gcombine.
    unfold memval_combine. destruct ZMap.get eqn: Hz; try congruence.
    symmetry. eapply pvalue_match_content in Hz; eauto. easy.
  - intros i k p Hi Hp.
    apply mem_combine_perm_l. eauto.
Qed.

Lemma pvalue_match_combine_r ce b ofs v m m':
  init_pv v ->
  (forall i, ZMap.get i (Mem.mem_contents m') !! b = Undef) ->
  (forall i k p, ~Mem.perm m' b i k p) ->
  pvalue_match ce b ofs v m ->
  pvalue_match ce b ofs v (mem_combine m' m).
Proof.
  intros HV HM HP H. eapply pvalue_match_invariant; eauto.
  - eauto using init_pv_size_eq.
  - intros i Hi. rewrite mem_gcombine.
    rewrite HM. reflexivity.
  - intros. rewrite mem_combine_perm_iff_r; eauto.
Qed.

Require Import Recdef.

Lemma store_zeros_contents :
  forall m b p n m', store_zeros m b p n = Some m' ->
  forall b', b' <> b -> (Mem.mem_contents m) !! b' = (Mem.mem_contents m') !! b'.
Proof.
  intros until n. functional induction (store_zeros m b p n); intros.
  - inv H; reflexivity.
  - transitivity ((Mem.mem_contents m') !! b').
    + eapply Mem.store_mem_contents in e0. rewrite e0.
      rewrite PMap.gso; eauto.
    + apply IHo; eauto.
  - inv H.
Qed.

Lemma p0_init_pv:
  forall pvars id v,
    (p0 (init_of_pvars pvars)) ! id = Some v ->
    init_pv v.
Proof.
  intros. induction pvars as [| [id' v'] pvars].
  - inv H.
  - destruct (PMap.elt_eq id id'); cbn in *.
    + subst. rewrite PTree.gss in H. inv H. apply v'.
    + apply IHpvars.
      rewrite PTree.gso in H; eauto.
Qed.

Theorem perm_empty_fragment:
  forall b ofs k p, ~Mem.perm Mem.empty_fragment b ofs k p.
Proof.
  intros. unfold Mem.perm, Mem.empty_fragment; simpl. tauto.
Qed.

Lemma vars_init ce pvars se:
  valid_pvars pvars se ->
  penv_mem_match ce se
    (p0 (init_of_pvars pvars))
    (m0 (init_of_pvars pvars) se).
Proof.
  induction pvars as [| [id v] pvars]; cbn; constructor; intros.
  - rewrite PTree.gempty in H0. congruence.
  - edestruct H as (b & Hb). left. reflexivity.
    destruct (PMap.elt_eq id0 id).
    + subst. rewrite PTree.gss in H0. inv H0.
      exists b. split; eauto.
      apply pvalue_match_combine_l. apply v.
      unfold init_fragment. rewrite Hb.
      apply init_pvalue_match; apply v.
    + rewrite PTree.gso in H0; eauto.
      assert (Hvp: valid_pvars pvars se).
      { unfold valid_pvars in *. intros. eapply H. right. eauto. }
      specialize (IHpvars Hvp).
      inv IHpvars. specialize (MPE _ _ H0).
      destruct MPE as (b' & A & B).
      exists b'. split; eauto.
      assert (b <> b').
      { intros <-. exploit Genv.find_symbol_injective.
        apply A. apply Hb. easy. }
      apply pvalue_match_combine_r; eauto.
      * eapply p0_init_pv; eauto.
      * intros i. unfold init_fragment. rewrite Hb.
        unfold init_fragment'. destruct store_zeros eqn: Hx.
        -- eapply store_zeros_contents in Hx.
           rewrite <- Hx. cbn.
           rewrite PMap.gi. rewrite ZMap.gi. reflexivity.
           congruence.
        -- cbn. rewrite PMap.gi. rewrite ZMap.gi. reflexivity.
      * intros. unfold init_fragment. rewrite Hb.
        unfold init_fragment'. destruct store_zeros eqn: Hx.
        -- eapply Genv.store_zeros_perm in Hx.
           rewrite <- Hx.
           unfold Mem.perm. cbn. rewrite PMap.gso; eauto.
        -- apply perm_empty_fragment.
Qed.

Section DISJOINT.

  Lemma init_fragment_perm:
    forall b b' sz ofs k p,
      b <> b' -> ~Mem.perm (init_fragment' b sz) b' ofs k p.
  Proof.
    intros * Hb. unfold init_fragment'.
    destruct store_zeros eqn: Hs.
    - eapply Genv.store_zeros_perm in Hs.
      rewrite <- Hs.
      unfold Mem.perm. cbn. rewrite PMap.gso; eauto.
    - eauto with mem.
  Qed.

  Lemma init_fragment_content:
    forall b b' sz ofs,
      b <> b' -> ZMap.get ofs (PMap.get b' (init_fragment' b sz).(Mem.mem_contents)) = Undef.
  Proof.
    intros * Hb. unfold init_fragment'.
    destruct store_zeros eqn: Hs.
    - eapply store_zeros_contents with (b' := b') in Hs; eauto.
      rewrite <- Hs. cbn.
      rewrite PMap.gi. rewrite ZMap.gi. reflexivity.
    - cbn. rewrite PMap.gi. rewrite ZMap.gi. reflexivity.
  Qed.

  Lemma init_fragment_nextblock b sz:
    Mem.nextblock (init_fragment' b sz) = Pos.succ b.
  Proof.
    unfold init_fragment'. destruct store_zeros eqn: Hs.
    - erewrite Genv.store_zeros_nextblock; eauto.
      reflexivity.
    - edestruct Genv.store_zeros_exists as (m & Hm).
      2: { rewrite Hm in Hs. congruence. }
      intros o Ho.
      unfold Mem.perm. cbn.
      rewrite PMap.gss.
      destruct zle; try lia. cbn.
      destruct zlt; try lia. cbn. constructor.
  Qed.

  Lemma init_fragment_alloc_flag b sz:
    Mem.alloc_flag (init_fragment' b sz) = false.
  Proof.
    unfold init_fragment'. destruct store_zeros eqn: Hs.
    - erewrite Genv.store_zeros_alloc_flag; eauto.
      reflexivity.
    - edestruct Genv.store_zeros_exists as (m & Hm).
      2: { rewrite Hm in Hs. congruence. }
      intros o Ho.
      unfold Mem.perm. cbn.
      rewrite PMap.gss.
      destruct zle; try lia. cbn.
      destruct zlt; try lia. cbn. constructor.
  Qed.

  Lemma perm_mem_access m1 m2 b ofs k:
    (forall p, Mem.perm m1 b ofs k p <-> Mem.perm m2 b ofs k p) ->
    (Mem.mem_access m1) !! b ofs k = (Mem.mem_access m2) !! b ofs k.
  Proof.
    intros H. unfold Mem.perm, Mem.perm_order' in H.
    destruct ((Mem.mem_access m1) !! b ofs k) eqn: Hp1;
      destruct ((Mem.mem_access m2) !! b ofs k) eqn: Hp2;
      try congruence.
    - destruct p; destruct p1; try congruence.
      + specialize (H Freeable). destruct H.
        exploit H. constructor. easy.
      + specialize (H Freeable). destruct H.
        exploit H. constructor. easy.
      + specialize (H Freeable). destruct H.
        exploit H. constructor. easy.
      + specialize (H Freeable). destruct H.
        exploit H0. constructor. easy.
      + specialize (H Writable). destruct H.
        exploit H. constructor. easy.
      + specialize (H Writable). destruct H.
        exploit H. constructor. easy.
      + specialize (H Freeable). destruct H.
        exploit H0. constructor. easy.
      + specialize (H Writable). destruct H.
        exploit H0. constructor. easy.
      + specialize (H Readable). destruct H.
        exploit H. constructor. easy.
      + specialize (H Freeable). destruct H.
        exploit H0. constructor. easy.
      + specialize (H Writable). destruct H.
        exploit H0. constructor. easy.
      + specialize (H Readable). destruct H.
        exploit H0. constructor. easy.
    - specialize (H Nonempty). destruct H.
      exploit H. constructor. easy.
    - specialize (H Nonempty). destruct H.
      exploit H0. constructor. easy.
  Qed.

  Lemma join_combine_left m1 m2 m b sz:
    (forall ofs, ~Mem.perm m2 b ofs Max Nonempty) ->
    (forall ofs, ZMap.get ofs (PMap.get b m2.(Mem.mem_contents)) = Undef) ->
    Mem.alloc_flag m1 = false ->
    Mem.alloc_flag m2 = false ->
    join m1 m2 m ->
    join (mem_combine (init_fragment' b sz) m1) m2
      (mem_combine (init_fragment' b sz) m).
  Proof.
    intros Hp Hm Hf1 Hf2 H. destruct H. split.
    - intros bx ofs Hv. destruct (valid_block_dec m bx).
      + specialize (mjoin_contents _ ofs v).
        inv mjoin_contents.
        * destruct (PMap.elt_eq b bx).
          -- subst. apply contents_join_r; eauto.
             ++ intros k p.
                rewrite !mem_combine_perm_iff_l; eauto.
                reflexivity. rewrite <- H0. eauto.
             ++ cbn. rewrite !PMap_gcombine.
                rewrite !ZMap_gcombine. congruence.
             ++ unfold Mem.valid_block, Plt in *.
                cbn. rewrite init_fragment_nextblock. lia.
          -- apply contents_join_l; eauto.
             ++ rewrite mem_combine_perm_iff_r; eauto.
                apply init_fragment_perm. eauto.
             ++ intros k p. rewrite H0.
                rewrite mem_combine_perm_iff_r; eauto.
                reflexivity.
                apply init_fragment_perm. eauto.
             ++ cbn. rewrite PMap_gcombine.
                rewrite ZMap_gcombine.
                rewrite init_fragment_content; eauto.
             ++ rewrite H2. cbn. rewrite PMap_gcombine.
                rewrite ZMap_gcombine.
                rewrite init_fragment_content; eauto.
        * destruct (PMap.elt_eq b bx).
          -- subst. apply contents_join_r; eauto.
             ++ intros k p.
                exploit perm_mem_access. apply H0.
                intros Hac.
                unfold Mem.perm. cbn. rewrite !PMap_gcombine.
                rewrite Hac. reflexivity.
             ++ cbn. rewrite !PMap_gcombine.
                rewrite !ZMap_gcombine. congruence.
             ++ unfold Mem.valid_block, Plt in *.
                cbn. rewrite init_fragment_nextblock. lia.
          -- apply contents_join_r; eauto.
             ++ intros k p. rewrite !mem_combine_perm_iff_r.
                2-3: apply init_fragment_perm; eauto. eauto.
             ++ cbn. rewrite !PMap_gcombine.
                rewrite !ZMap_gcombine.
                rewrite init_fragment_content; eauto.
             ++ unfold Mem.valid_block, Plt in *.
                cbn. lia.
      + specialize (mjoin_empty_contents _ ofs n).
        inv mjoin_empty_contents. destruct (PMap.elt_eq b bx).
        * subst. apply contents_join_r; eauto.
          ++ intros k p. rewrite !mem_combine_perm_iff_l; eauto.
             reflexivity.
          ++ cbn. rewrite !PMap_gcombine.
             rewrite !ZMap_gcombine. congruence.
          ++ unfold Mem.valid_block, Plt. cbn.
             rewrite init_fragment_nextblock. lia.
        * apply contents_join_r; eauto.
          ++ intros k p. rewrite !mem_combine_perm_iff_l; eauto.
             reflexivity.
          ++ cbn. rewrite !PMap_gcombine.
             rewrite !ZMap_gcombine. congruence.
          ++ unfold Mem.valid_block, Plt in *.
             cbn in *. lia.
    - cbn. rewrite init_fragment_nextblock. lia.
    - inv mjoin_alloc_flag; try congruence.
      apply alloc_flag_join_x; eauto.
      cbn. rewrite init_fragment_alloc_flag. eauto.
      cbn. rewrite init_fragment_alloc_flag. eauto.
    - intros bx ofs Hv.
      assert (~ Mem.valid_block m bx /\ b <> bx) as (Hv' & Hb).
      {
        unfold Mem.valid_block, Plt in *. cbn in *.
        rewrite init_fragment_nextblock in Hv.
        split; lia.
      }
      specialize (mjoin_empty_contents _ ofs Hv').
      inv mjoin_empty_contents. constructor; eauto.
      1-2: rewrite mem_combine_perm_iff_l; eauto.
      1-2: apply init_fragment_perm; eauto.
      1-2: cbn; rewrite PMap_gcombine; rewrite ZMap_gcombine.
      1-2: rewrite init_fragment_content; eauto.
      unfold Mem.valid_block, Plt in *. cbn in *.
      rewrite init_fragment_nextblock in *. lia.
  Qed.

  (* the tricky thing is that [mem_combine empty_fragment m <> m]  *)
  Lemma join_combine_empty_fragment m1 m2 m:
    join m1 m2 m ->
    join (mem_combine Mem.empty_fragment m1) m2
      (mem_combine (Mem.empty_fragment) m).
  Proof.
    intros H. destruct H. constructor.
    - intros b ofs Hb.
      assert (Hvb: Mem.valid_block m b).
      { unfold Mem.valid_block, Plt in *.
        cbn in *. lia. }
      specialize (mjoin_contents _ ofs Hvb).
      inv mjoin_contents.
      + apply contents_join_l; eauto.
        * rewrite mem_combine_perm_iff_r; eauto.
        * intros. rewrite mem_combine_perm_iff_r; eauto.
        * cbn. rewrite PMap_gcombine.
          rewrite ZMap_gcombine. simpl. eauto.
        * cbn. rewrite PMap_gcombine.
          rewrite ZMap_gcombine. simpl. eauto.
      + apply contents_join_r; eauto.
        * intros. rewrite !mem_combine_perm_iff_r; eauto.
        * cbn. rewrite !PMap_gcombine.
          rewrite !ZMap_gcombine. simpl. eauto.
        * unfold Mem.valid_block, Plt in *.
          cbn in *. lia.
    - cbn. lia.
    - inv mjoin_alloc_flag.
      + apply alloc_flag_join_l; eauto.
        cbn. lia.
      + apply alloc_flag_join_r; eauto.
        cbn. lia.
      + apply alloc_flag_join_x; eauto.
    - intros.
      assert (Hvb: ~Mem.valid_block m b).
      { unfold Mem.valid_block, Plt in *.
        cbn in *. lia. }
      specialize (mjoin_empty_contents _ ofs Hvb).
      inv mjoin_empty_contents.
      constructor; eauto.
      1-2: rewrite mem_combine_perm_iff_l; eauto.
      1-2: cbn; rewrite PMap_gcombine;
      rewrite ZMap_gcombine; simpl; eauto.
      unfold Mem.valid_block, Plt in *.
      cbn in *. lia.
  Qed.

  Definition vars_disjoint (vs1 vs2: list (ident * val)) : Prop :=
    list_disjoint (map fst vs1) (map fst vs2).

  Lemma m0_invalid_block vars se b ofs:
    ~ Mem.valid_block (m0 vars se) b ->
    ZMap.get ofs (Mem.mem_contents (m0 vars se)) !! b = Undef.
  Proof.
    induction vars as [| [id a]].
    - intros. simpl. reflexivity.
    - simpl. intros H.
      assert (Hb: ~Mem.valid_block (m0 vars se) b).
      { unfold Mem.valid_block, Plt in *. cbn in *. lia. }
      specialize (IHvars Hb).
      rewrite PMap_gcombine. rewrite ZMap_gcombine.
      assert (Hm: ZMap.get ofs (Mem.mem_contents (init_fragment id a se)) !! b = Undef).
      {
        unfold init_fragment in *.
        destruct Genv.find_symbol eqn: Hs.
        - destruct (PMap.elt_eq b b0).
          + subst.
            unfold Mem.valid_block, Plt in *. cbn in *.
            rewrite init_fragment_nextblock in H. lia.
          + apply init_fragment_content. eauto.
        - reflexivity.
      }
      rewrite Hm. simpl. eauto.
  Qed.

  Lemma m0_alloc_flag vars se:
    Mem.alloc_flag (m0 vars se) = false.
  Proof.
    induction vars as [| [id a]]; eauto.
    cbn. rewrite IHvars.
    unfold init_fragment.
    destruct Genv.find_symbol.
    - rewrite init_fragment_alloc_flag. easy.
    - reflexivity.
  Qed.

  Lemma join_empty_left vars se:
    join Mem.empty_fragment (m0 vars se) (m0 vars se).
  Proof.
    constructor.
    - intros b ofs Hb.
      apply contents_join_l; eauto.
      intros. reflexivity.
    - cbn. lia.
    - apply alloc_flag_join_x; eauto using m0_alloc_flag.
    - intros.
      constructor; eauto using m0_invalid_block with mem.
      unfold Mem.valid_block, Plt in *.
      cbn. lia.
  Qed.

  Lemma m0_other_block_content vars se id ofs b:
    Genv.find_symbol se id = Some b ->
    ~In id (map fst vars) ->
    ZMap.get ofs (Mem.mem_contents (m0 vars se)) !! b = Undef.
  Proof.
    intros Hb. induction vars as [| [id' a]].
    - intros. reflexivity.
    - intros H.
      assert (id <> id') as Hid.
      { intros <-. apply H. now left. }
      assert (~ In id (map fst vars)) as Ha.
      { intros x. apply H. now right. }
      specialize (IHvars Ha).
      cbn. unfold init_fragment.
      destruct (Genv.find_symbol se id') eqn: Hs.
      + assert (b <> b0).
        { intros <-. exploit Genv.find_symbol_injective.
          apply Hb. apply Hs. easy. }
        rewrite PMap_gcombine. rewrite ZMap_gcombine.
        rewrite init_fragment_content; eauto.
      + rewrite PMap_gcombine. rewrite ZMap_gcombine.
        simpl. eauto.
  Qed.

  Lemma m0_other_block_perm vars se id ofs b:
    Genv.find_symbol se id = Some b ->
    ~In id (map fst vars) ->
    ~Mem.perm (m0 vars se) b ofs Max Nonempty.
  Proof.
    intros Hb. induction vars as [| [id' a]].
    - intros. apply perm_empty_fragment.
    - intros H.
      assert (id <> id') as Hid.
      { intros <-. apply H. now left. }
      assert (~ In id (map fst vars)) as Ha.
      { intros x. apply H. now right. }
      specialize (IHvars Ha).
      cbn. unfold init_fragment.
      destruct (Genv.find_symbol se id') eqn: Hs.
      + assert (b <> b0).
        { intros <-. exploit Genv.find_symbol_injective.
          apply Hb. apply Hs. easy. }
        rewrite mem_combine_perm_iff_l; eauto.
        apply init_fragment_perm; eauto.
      + rewrite mem_combine_perm_iff_l; eauto.
  Qed.

  Lemma disjoint_init_mem:
    forall se vars1 vars2,
      vars_disjoint vars1 vars2 ->
      join (m0 vars1 se) (m0 vars2 se) (m0 (vars1 ++ vars2) se).
  Proof.
    intros *. revert vars2.
    induction vars1 as [| [id pv] ]; intros; cbn.
    - apply join_empty_left.
    - assert (Hvs: vars_disjoint vars1 vars2).
      { unfold vars_disjoint, list_disjoint in *.
        intros x y Hx Hy. apply H; eauto.
        right. eauto. }
      unfold init_fragment.
      destruct Genv.find_symbol eqn: Hs.
      + assert (~ In id (map fst vars2)).
        { intros x.
          unfold vars_disjoint in H. cbn in *.
          unfold list_disjoint in H.
          exploit H; eauto. now left. }
        eapply join_combine_left.
        * intros ofs. eapply m0_other_block_perm; eauto.
        * intros ofs. eapply m0_other_block_content; eauto.
        * apply m0_alloc_flag.
        * apply m0_alloc_flag.
        * apply IHvars1; eauto.
      + apply join_combine_empty_fragment; eauto.
  Qed.

End DISJOINT.
