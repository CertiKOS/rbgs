From compcert Require Import
     AST Coqlib Maps Values Integers Errors Events
     Globalenvs Memory Floats Ctypes Values Cop Clight.
Require Import Lia.
Require SimplLocalsproof.
Require Import Join.

(** ------------------------------------------------------------------------- *)
(** PVal and PEnv  *)
Open Scope Z_scope.

Inductive val : Type :=
| Val : Values.val -> type -> val
| Array : Z -> ZMap.t val -> type -> val
| Struct : list (ident * val) -> type -> val.

Definition fields := list (ident * val).

Definition type_of_pv (pv: val) :=
  match pv with
  | Val _ ty | Array _ _ ty | Struct _ ty => ty
  end.

Coercion type_of_pv : val >-> type.


Definition penv : Type := PTree.t val.
(** typed location: the type information is used to calculate the correct
    offset when we establish a relation between penv and CompCert memory. *)
Inductive access : Type := Field (f: ident) (tid: ident) | Index (z: Z) (ty: type).
Inductive loc : Type := Loc: type -> list access -> loc.

(** ------------------------------------------------------------------------- *)
(** The relation between persistent environment and memory *)

Require Import Relators.

Section WITH_CE.

  Variable (ce: composite_env).
  Hypothesis (Hce: composite_env_consistent ce).

  (** ------------------------------------------------------------------------- *)
  (** Struct field and offset calculation *)
  Definition next_field (pos: Z) (ty: type): Z :=
    align pos (bitalignof ce ty) + bitsizeof ce ty.

  Definition layout_field (pos: Z) (ty: type): Z :=
    align pos (bitalignof ce ty) / 8.

  Fixpoint field_offset_rec (id: ident) (fs: fields) (pos: Z) :=
    match fs with
    | nil => None
    | (i, v) :: rest =>
        if ident_eq id i
        then Some (layout_field pos v)
        else field_offset_rec id rest (next_field pos v)
    end.

  Definition field_offset (id: ident) (fs: fields) :=
    field_offset_rec id fs 0.

  Inductive field_member_match: member -> ident * val -> Prop :=
    | fields_members_match_intro i t v:
      t = type_of_pv v ->
      field_member_match (Member_plain i t) (i, v).

  Inductive struct_type_ok: ident -> fields -> Prop :=
    struct_type_ok_intro tid fs co
      (HCE: ce!tid = Some co)
      (HSU: co_su co = Ctypes.Struct)
      (HCO: list_rel field_member_match (co_members co) fs):
      struct_type_ok tid fs.

  Lemma struct_same_offset fid fs ms ofs:
    list_rel field_member_match ms fs ->
    field_offset fid fs = Some ofs <->
    Ctypes.field_offset ce fid ms = OK (ofs, Full).
  Proof.
    unfold field_offset, Ctypes.field_offset.
    generalize 0 as base. intros * H. revert base. induction H.
    - intros; split; easy.
    - intros b. destruct y as [i v].
      inv H. cbn. destruct ident_eq; eauto.
      split; intros H; inv H; eauto.
  Qed.

  (** ------------------------------------------------------------------------- *)
  (** PEnv read and write *)

  Fixpoint find_field (fs: fields) (f: ident) :=
    match fs with
    | nil => None
    | (f', v) :: rest => if ident_eq f' f then Some v else find_field rest f
    end.

  (** Again, the type information is used when relate [pread] with
    [deref_loc]. Consider this relation as a specification of the function of
    type [val -> loc -> Values.val * type] *)
  Inductive pread_val: val -> loc -> Values.val -> type -> Prop :=
  (* TODO: be more tolerent on typing *)
  | pread_nil: forall v ty, pread_val (Val v ty) (Loc ty nil) v ty
  | pread_index:
    forall n arr ty ty_elem ty_v i v attr rest,
      0 <= i < n ->
      pread_val (ZMap.get i arr) (Loc ty_v rest) v ty_v ->
      ty = Tarray ty_elem n attr ->
      pread_val (Array n arr ty) (Loc ty_v (Index i ty_elem :: rest)) v ty_v
  | pread_field:
    forall f fv fs v ty ty_v rest tid attr,
      find_field fs f = Some fv ->
      pread_val fv (Loc ty_v rest) v ty_v ->
      ty = Tstruct tid attr ->
      struct_type_ok tid fs ->
      pread_val (Struct fs ty) (Loc ty_v (Field f tid :: rest)) v ty_v.

  Inductive pread: penv -> ident -> loc -> Values.val -> type -> Prop :=
  | pread_intro: forall pe id l pv v ty,
      pe!id = Some pv ->
      pread_val pv l v ty ->
      pread pe id l v ty.

  Fixpoint update_field (old_fs: fields) (f: ident) (v: val): option fields :=
    match old_fs with
    | (f', old_v) :: rest =>
        if ident_eq f f'
        then
          if type_eq old_v v then
          Some ((f', v) :: rest) else None
        else
          match update_field rest f v with
          | Some res => Some ((f', old_v) :: res)
          | None => None
          end
    | nil => None
    end.

  Lemma update_field_gss old_fs new_fs f v:
    update_field old_fs f v = Some new_fs ->
    find_field new_fs f = Some v.
  Proof.
    revert new_fs. induction old_fs; intros; try easy.
    destruct a. cbn in H. destruct ident_eq; cbn in H.
    - destruct type_eq; inv H.
      setoid_rewrite peq_true. reflexivity.
    - destruct update_field eqn:Hx; inv H.
      cbn. rewrite peq_false; eauto.
  Qed.

  Lemma update_field_gso old_fs new_fs f f' v:
    update_field old_fs f v = Some new_fs ->
    f <> f' -> find_field new_fs f' = find_field old_fs f'.
  Proof.
    revert new_fs. induction old_fs; intros; try easy.
    destruct a. cbn in H. destruct ident_eq.
    - destruct type_eq; inv H; cbn.
      rewrite !peq_false; eauto.
    - destruct update_field eqn:Hx; inv H; cbn.
      destruct ident_eq; eauto.
  Qed.

  Lemma update_field_offset old_fs new_fs f v:
    update_field old_fs f v = Some new_fs ->
    forall f', field_offset f' old_fs = field_offset f' new_fs.
  Proof.
    unfold field_offset. generalize 0 as base.
    revert new_fs. induction old_fs; intros; try easy.
    destruct a. cbn in H. destruct (ident_eq f i).
    - destruct type_eq; inv H; cbn.
      unfold layout_field, next_field. rewrite e0. reflexivity.
    - destruct update_field eqn:Hx; inv H; cbn.
      erewrite IHold_fs; eauto.
  Qed.

  Lemma update_field_type_ok old_fs new_fs f v tid:
    update_field old_fs f v = Some new_fs ->
    struct_type_ok tid old_fs ->
    struct_type_ok tid new_fs.
  Proof.
    intros. inv H0. econstructor; eauto. clear HCE.
    revert new_fs HCO H. generalize (co_members co) as ms.
    induction old_fs; intros; try easy.
    destruct a. cbn in H. destruct ident_eq.
    - destruct type_eq; inv H; cbn.
      inv HCO. econstructor; eauto.
      inv H2. econstructor; eauto.
    - destruct update_field eqn:Hx; inv H; cbn.
      inv HCO. econstructor; eauto.
  Qed.

  Definition field_type_tid (tid: ident) (f: ident): res type :=
    match ce!tid with
    | Some co => field_type f (co_members co)
    | None => Error (MSG "failure" :: nil)
    end.

  Inductive pwrite_val: val -> loc -> Values.val -> val -> type -> Prop :=
  | pwrite_nil: forall old_v new_v ty
                  (VTY: val_casted new_v ty),
      pwrite_val (Val old_v ty) (Loc ty nil) new_v (Val new_v ty) ty
  | pwrite_index:
    forall old_arr new_arr n i ty old_pv new_pv rest new_v ty_v attr ty_elem,
      0 <= i < n ->
      old_pv = ZMap.get i old_arr ->
      pwrite_val old_pv (Loc ty_v rest) new_v new_pv ty_v ->
      new_arr = ZMap.set i new_pv old_arr ->
      ty = Tarray ty_elem n attr ->
      pwrite_val (Array n old_arr ty) (Loc ty_v (Index i ty_elem :: rest))
        new_v (Array n new_arr ty) ty_v
  | pwrite_field:
    forall old_fs new_fs ty ty_v rest new_v f new_fv old_fv tid attr,
      find_field old_fs f = Some old_fv ->
      pwrite_val old_fv (Loc ty_v rest) new_v new_fv ty_v ->
      update_field old_fs f new_fv = Some new_fs ->
      ty = Tstruct tid attr ->
      struct_type_ok tid old_fs ->
      field_type_tid tid f = OK (type_of_pv old_fv) ->
      pwrite_val (Struct old_fs ty) (Loc ty_v (Field f tid :: rest))
        new_v (Struct new_fs ty) ty_v.

  Inductive pwrite: penv -> ident -> loc -> Values.val -> penv -> type -> Prop :=
  | pwrite_intro:  forall pe id l pe' v old_pv new_pv ty ch,
      pe!id = Some old_pv ->
      pwrite_val old_pv l v new_pv ty ->
      pe' =  PTree.set id new_pv pe ->
      access_mode ty = By_value ch ->
      pwrite pe id l v pe' ty.

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
      pvalue_match b ofs (Array n parr ty) m
  | pstruct_match:
    forall b ofs fs ty m tid attr
      (TSTRUCT: ty = Tstruct tid attr)
      (NO_OVERFLOW: ofs + sizeof ce ty <= Ptrofs.max_unsigned)
      (TYPE: struct_type_ok tid fs)
      (MATCH: forall i v ofs',
          find_field fs i = Some v -> field_offset i fs = Some ofs' ->
          pvalue_match b (ofs + ofs') v m),
    pvalue_match b ofs (Struct fs ty) m.

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

  Lemma field_type_ok f ms ofs:
    Ctypes.field_offset ce f ms = OK (ofs, Full) ->
    exists ty, Ctypes.field_type f ms = OK ty.
  Proof.
    unfold Ctypes.field_offset. generalize 0 as base.
    induction ms. intros; try easy.
    intros. cbn in H. destruct ident_eq eqn: Hx.
    - eexists. cbn. rewrite e.
      rewrite peq_true. reflexivity.
    - edestruct IHms as (ty & Hty); eauto.
      exists ty. cbn. rewrite Hty. rewrite peq_false; easy.
  Qed.

  Lemma field_type_correct fs ms f v:
    list_rel field_member_match ms fs ->
    find_field fs f = Some v ->
    Ctypes.field_type f ms = OK (type_of_pv v).
  Proof.
    revert f v fs. induction ms; intros.
    - inv H. inv H0.
    - inv H. inv H3. cbn in *.
      destruct ident_eq.
      + subst. inv H0. rewrite peq_true. reflexivity.
      + rewrite peq_false; eauto.
  Qed.

  Lemma field_offset_pos f ms ofs_field:
    Ctypes.field_offset ce f ms = OK (ofs_field, Full) ->
    ofs_field >= 0.
  Proof.
    intros. edestruct field_type_ok as (ty & Hty); eauto.
    exploit field_offset_in_range; eauto. lia.
  Qed.


  Lemma field_offset_size tid co ofs_field f ty attr:
    ce!tid = Some co ->
    Ctypes.field_offset ce f (co_members co) = OK (ofs_field, Full) ->
    field_type f (co_members co) = OK ty ->
    co_su co = Ctypes.Struct ->
    ofs_field + sizeof ce ty <= sizeof ce (Tstruct tid attr).
  Proof.
    intros. exploit Ctypes.field_offset_in_range; eauto.
    intros [Ha Hb]. cbn. rewrite H.
    cut (sizeof_struct ce (co_members co) <= co_sizeof co). lia.
    erewrite co_consistent_sizeof; eauto.
    etransitivity.
    2: {
      apply align_le.
      pose proof (co_alignof_two_p co) as (n & Hn). rewrite Hn.
      apply two_power_nat_pos. }
    unfold sizeof_composite. rewrite H2. reflexivity.
  Qed.

  Lemma field_offset_in_range fs i v base x ofs' tid attr:
    find_field fs i = Some v ->
    field_offset i fs = Some ofs' ->
    struct_type_ok tid fs ->
    base + ofs' <= x < base + ofs' + sizeof ce v ->
    base <= x < base + sizeof ce (Tstruct tid attr).
  Proof.
    intros * Hv Hf Ht Hx. inv Ht. split.
    - cut (ofs' >= 0). lia.
      eapply field_offset_pos.
      eapply struct_same_offset; eauto.
    - exploit field_type_correct; eauto. intros Ht.
      cut (ofs' + sizeof ce v <= sizeof ce (Tstruct tid attr)). lia.
      eapply field_offset_size; eauto.
      eapply struct_same_offset; eauto.
  Qed.

  Lemma pvalue_match_unchanged:
    forall P ma mb b ofs pv,
      pvalue_match b ofs pv ma ->
      Mem.unchanged_on P ma mb ->
      (forall i, ofs <= i < ofs + sizeof ce pv -> P b i) ->
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
      pose proof (sizeof_pos ce (ZMap.get i parr)).
      revert H Hx. generalize (sizeof ce (ZMap.get i parr)).
      intros z Hp Hz. split.
      + transitivity (ofs + i * z). 2: apply Hz.
        cut (0 <= i * z). lia. apply Z.mul_nonneg_nonneg; lia.
      + eapply Z.lt_le_trans. apply Hz.
        rewrite <- Z.add_assoc.
        apply Z.add_le_mono_l.
        cut (i + 1 <= n). 2: lia. intros Ha.
        transitivity (z * (i + 1)). lia.
        apply Z.mul_le_mono_nonneg_l; lia.
    - eapply pstruct_match; eauto.
      intros * Hi Hf. eapply H; eauto.
      intros x Hx. apply HP.
      cbn. clear H. clear MATCH.
      inv TYPE; eauto.
      assert (field_type i (co_members co) = OK (type_of_pv v)).
      { eapply field_type_correct; eauto. }
      eapply field_offset_in_range; eauto.
      econstructor; eauto.
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
    - eapply pstruct_match; eauto.
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
      match_loc (Loc ty_v (Index i ty :: rest))
        (ofs_start + ofs_elem)
  | match_field:
    forall f rest ofs_start ofs_field ty_field ty_v tid co
      (BASE: match_loc (Loc ty_v rest) ofs_start)
      (HCE: ce!tid = Some co)
      (OFS: Ctypes.field_offset ce f (co_members co) = OK (ofs_field, Full))
      (TY: field_type_tid tid f = OK ty_field)
      (NO_OVERLAP: ofs_start + sizeof ce ty_v <= sizeof ce ty_field),
      match_loc (Loc ty_v (Field f tid :: rest))
        (ofs_start + ofs_field).

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

  Lemma match_loc_app_index:
    forall l ofs_start i ty ofs_elem ty_prev n attr,
      match_loc (Loc ty_prev l) ofs_start ->
      ofs_elem = i * sizeof ce ty ->
      ty_prev = Tarray ty n attr ->
      0 <= i < n ->
      match_loc (Loc ty (l ++ Index i ty :: nil)) (ofs_start + ofs_elem).
  Proof.
    intros l. induction l.
    - intros * A B C D.
      inv A. cbn.
      replace (i * sizeof ce ty) with (0 + i * sizeof ce ty) by reflexivity.
      constructor; eauto. constructor. reflexivity. lia.
    - intros * A B C D. inv A.
      + rewrite <- app_comm_cons.
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
      (* TODO: cleanup the copy paste *)
      + rewrite <- app_comm_cons.
        replace (ofs_start0 + ofs_field + i * sizeof ce ty)
          with (ofs_start0 + i * sizeof ce ty + ofs_field)
          by lia.
        econstructor; eauto.
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

  Lemma match_loc_app_field:
    forall l ofs_start ty ofs_field co ty_prev f tid attr,
      match_loc (Loc ty_prev l) ofs_start ->
      ty_prev = Tstruct tid attr ->
      ce!tid = Some co ->
      Ctypes.field_offset ce f (co_members co) = OK (ofs_field, Full) ->
      field_type f (co_members co) = OK ty ->
      co_su co = Ctypes.Struct ->
      match_loc (Loc ty (l ++ Field f tid :: nil)) (ofs_start + ofs_field).
  Proof.
    intros l. induction l.
    - intros * A B C D.
      inv A. cbn.
      replace (ofs_field) with (0 + ofs_field) by reflexivity.
      econstructor; eauto.
      + constructor.
      + unfold field_type_tid. rewrite C; eauto.
      + lia.
    - intros * A B C D E F. inv A.
      + rewrite <- app_comm_cons.
        replace (ofs_start0 + i * sizeof ce ty0 + ofs_field)
          with (ofs_start0 + ofs_field + i * sizeof ce ty0)
          by lia.
        constructor; eauto.
        cut (ofs_field + sizeof ce ty <= sizeof ce (Tstruct tid attr)). lia.
        eapply field_offset_size; eauto.
      + rewrite <- app_comm_cons.
        replace (ofs_start0 + ofs_field0 + ofs_field)
          with (ofs_start0 + ofs_field + ofs_field0) by lia.
        econstructor; eauto.
        cut (ofs_field + sizeof ce ty <= sizeof ce (Tstruct tid attr)). lia.
        eapply field_offset_size; eauto.
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
      + rewrite Z.add_comm. eauto.
      + lia.
      + apply Z.le_ge.
        apply Z.add_nonneg_nonneg; try lia.
        apply Z.mul_nonneg_nonneg; try lia.
        pose proof (sizeof_pos ce ty_elem0). lia.
    - intros * Hloc Hm Hofs Hbase.
      inv Hloc. inv Hm.
      rewrite <- Z.add_assoc.
      apply IHpread_val; eauto.
      + rewrite Z.add_comm. eapply MATCH; eauto.
        inv TSTRUCT. inv TYPE.
        eapply struct_same_offset; eauto.
        rewrite HCE in HCE0. inv HCE0. exact OFS.
      + lia.
      + apply field_offset_pos in OFS. lia.
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
    intros * A. induction A.
    - lia.
    - subst. apply Z.le_ge.
      apply Z.add_nonneg_nonneg; try lia.
      apply Z.mul_nonneg_nonneg; try lia.
      pose proof (sizeof_pos ce ty). lia.
    - apply field_offset_pos in OFS. lia.
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
             remember (sizeof ce (ZMap.get ix old_arr))
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
    - intros * Hloc Hv Hmode. inv Hloc. inv Hv. inv TSTRUCT.
      inv TYPE. rewrite HCE in HCE0. inv HCE0.
      exploit MATCH; eauto. eapply struct_same_offset; eauto.
      intros Hfv. edestruct IHpwrite_val as (tm' & A & B); eauto.
      exists tm'. split.
      + rewrite <- (Z.add_comm ofs_field ofs_start).
        rewrite Z.add_assoc. apply A.
      + econstructor; eauto.
        * eapply update_field_type_ok; eauto.
        * intros * C D. destruct (peq i f).
          -- subst.
             erewrite <- update_field_offset in D; eauto.
             eapply struct_same_offset in D; eauto.
             rewrite OFS in D. inv D.
             erewrite update_field_gss in C; eauto.
             inv C. exact B.
          -- assert (C': find_field old_fs i = Some v).
             { eapply update_field_gso in H1; eauto. congruence. }
             erewrite <- update_field_offset in D; eauto.
             specialize (MATCH _ _ _ C' D).
             eapply pvalue_match_unchanged; eauto.
             instantiate
               (1 := fun (_: block) (ofsx: Z) =>
                       ofsx < base + ofs_field + ofs_start \/
                         ofsx >= base + ofs_field + ofs_start + size_chunk ch).
             { eapply Mem.store_unchanged_on; eauto.
               intros z Hz. lia. }
             cbn. intros z Hz. clear IHpwrite_val.
             assert (ofs_start + size_chunk ch <= sizeof ce ty_field).
             { erewrite size_type_chunk; eauto. }
             exploit field_type_correct. 2: apply C'. eauto. intros Ht.
             exploit field_type_correct. 2: apply H. eauto. intros Ht'.
             exploit field_offset_no_overlap. 5: apply n. 2,4: eassumption.
             eapply struct_same_offset in D. apply D. exact HCO. exact OFS.
             cbn. intros Hx. unfold layout_start, bitsizeof in Hx.
             rewrite !Z.add_0_r in Hx. rewrite <- !Z.mul_add_distr_r in Hx.
             destruct Hx as [Hx|Hx].
             ++ left. assert (ofs_start >= 0).
                { eapply match_loc_pos; eauto. }
                cut (ofs' + sizeof ce v <= ofs_field + ofs_start). lia.
                cut (ofs' + sizeof ce v <= ofs_field). lia.
                apply Z_div_le with (c := 8) in Hx. 2: lia.
                rewrite !Z.div_mul in Hx by lia. lia.
             ++ right.
                unfold field_type_tid in TY. rewrite HCE in TY.
                rewrite TY in Ht'. inv Ht'.
                cut (z >= base + ofs_field + sizeof ce old_fv). lia.
                cut (ofs' >= ofs_field + sizeof ce old_fv). lia.
                apply Z_div_le with (c := 8) in Hx. 2: lia.
                rewrite !Z.div_mul in Hx by lia. lia.
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

(** ------------------------------------------------------------------------- *)
(** PVal initial state and properties *)

Record privvar : Type := mkprivvar { pvar_init:> val; }.

Inductive sizeof_div4 ce : val -> Prop :=
  | sizeof_div4_Val v ty:
    (4 | sizeof ce ty) ->
    sizeof_div4 ce (Val v ty)
  | sizeof_div4_Arr n vs ty:
    (forall i, 0 <= i < n -> sizeof_div4 ce (ZMap.get i vs)) ->
    (* TODO: need some well-typed property so that we can infer (4 | sizeof ce ty) *)
    (4 | sizeof ce ty) ->
    sizeof_div4 ce (Array n vs ty)
  | sizeof_div4_Struct fs tid attr co:
    (forall f v, find_field fs f = Some v -> sizeof_div4 ce v) ->
    ce!tid = Some co ->
    (* TODO: is this too strong? *)
    (forall f ofs bf,
          Ctypes.field_offset ce f (co_members co) = OK (ofs, bf) -> (4 | ofs)) ->
    (4 | co_sizeof co) ->
    sizeof_div4 ce (Struct fs (Tstruct tid attr)).

Lemma sizeof_type_div4 ce pv :
  sizeof_div4 ce pv -> (4 | sizeof ce pv).
Proof. destruct 1; eauto. cbn. rewrite H0. eauto. Qed.

(* Lemma field_offset_div4 ce f fs ofs: *)
(*   (forall f v, find_field fs f = Some v -> sizeof_div4 ce v) -> *)
(*   field_offset ce f fs = Some ofs -> (4 | ofs). *)
(* Proof. *)
(*   intros Hf. unfold field_offset. *)
(*   assert (32 | 0). apply Z.divide_0_r. *)
(*   revert H. generalize 0 as z. *)
(*   induction fs; intros; try easy. *)
(*   - cbn in H0. destruct a. *)
(*     destruct ident_eq. *)
(*     + subst. inv H0. *)
(*       specialize (Hf i v). exploit Hf. *)
(*       cbn. rewrite peq_true. reflexivity. *)
(*       intros Hv. *)
(*       unfold layout_field. unfold bitalignof. *)
(*       Search (?x | ?y / ?z). *)
(*       change 4 with (32 / 8). *)
(*       eapply Z.divide_div. lia. exists 4. lia. *)
(*       admit. *)
(*     + eapply IHfs in H0; eauto. *)
(*       * intros. destruct (peq f0 i). *)
(*         -- subst. eapply Hf. cbn. rewrite peq_true; eauto. *)

(* Admitted *)

(* This property for stablity of type size in different ce *)
Inductive pv_type_ok ce: val -> Prop :=
  | pv_int_type sign attr v:
    pv_type_ok ce (Val v (Tint I32 sign attr))
  | pv_array_type ty_elem n attr vs:
    (forall i, 0 <= i < n -> pv_type_ok ce (ZMap.get i vs)) ->
    (forall i, 0 <= i < n -> ty_elem = type_of_pv (ZMap.get i vs)) ->
    pv_type_ok ce (Array n vs (Tarray ty_elem n attr))
  | pv_struct_type tid attr fs:
    struct_type_ok ce tid fs ->
    (forall f v, In (f, v) fs -> pv_type_ok ce v) ->
    pv_type_ok ce (Struct fs (Tstruct tid attr)).

Inductive init_pv ce: val -> Prop :=
| init_pv_int attr:
  init_pv ce (Val (Vint Int.zero) (Tint I32 Unsigned attr))
| init_pv_array n ty_elem attr arr
  (HV: forall i, 0 <= i < n -> init_pv ce (ZMap.get i arr))
  (HT: forall i, 0 <= i < n -> type_of_pv (ZMap.get i arr) = ty_elem):
  init_pv ce (Array n arr (Tarray ty_elem n attr))
| init_pv_struct fs tid attr
  (HV: forall f v, find_field fs f = Some v -> init_pv ce v)
  (HT: struct_type_ok ce tid fs):
  init_pv ce (Struct fs (Tstruct tid attr)).

Definition pvar_align_ok ce (pvar: privvar): Prop := sizeof_div4 ce pvar.

Definition pvar_type_ok ce (pvar: privvar): Prop := pv_type_ok ce pvar.

Definition pvar_size_ok ce (pvar: privvar): Prop :=
  sizeof ce pvar <= Ptrofs.max_unsigned.

Record pvar_ok ce (pvar: privvar) := {
    init_ok: init_pv ce pvar;
    align_ok: pvar_align_ok ce pvar;
    size_ok: pvar_size_ok ce pvar;
    type_ok: pvar_type_ok ce pvar;
  }.

(** ------------------------------------------------------------------------- *)
(** Initial state  *)

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

Definition init_fragment ce (id: ident) (pv: val) (se: Genv.symtbl) :=
  match Genv.find_symbol se id with
  | Some b => init_fragment' b (sizeof ce pv)
  | None => Mem.empty_fragment
  end.

Lemma read_as_zero_weaken m b ofs ofs' len len':
  ofs' >= ofs -> ofs' + len' <= ofs + len ->
  Genv.read_as_zero m b ofs len ->
  Genv.read_as_zero m b ofs' len'.
Proof.
  unfold Genv.read_as_zero. intros. apply H1; eauto; lia.
Qed.

Lemma empty_fragment_perm b i sz:
  0 <= i < sz ->
  Mem.perm (empty_fragment b 0 sz) b i Cur Writable.
Proof.
  intros Hi.
  unfold empty_fragment, Mem.perm, Mem.perm_order'. cbn.
  rewrite PMap.gss.
  destruct zle; try lia. cbn.
  destruct zlt; try lia. cbn. eauto with mem.
Qed.

Lemma store_zeros_empty_fragment b sz:
  exists m, store_zeros (empty_fragment b 0 sz) b 0 sz = Some m.
Proof.
  apply Genv.store_zeros_exists. cbn.
  intros i Hi. apply empty_fragment_perm; eauto.
Qed.

Lemma init_pvalue_match ce b pv:
  (* init_pv ce pv -> *)
  (* sizeof ce pv <= Ptrofs.max_unsigned -> *)
  (* sizeof_div4 ce pv -> *)
  composite_env_consistent ce ->
  pvar_ok ce pv ->
  pvalue_match ce b 0 pv (init_fragment' b (sizeof ce pv)).
Proof.
  intros Hce [H Hd4 Hsz]. unfold pvar_align_ok, pvar_size_ok in *.
  unfold init_fragment'.
  remember (sizeof ce pv) as sz.
  edestruct store_zeros_empty_fragment as (m & Hm).
  rewrite Hm.
  assert (Hp: Mem.range_perm m b 0 (0 + sz) Cur Writable).
  {
    intros i Hi.
    eapply Genv.store_zeros_perm in Hm.
    apply Hm. apply empty_fragment_perm. eauto.
  }
  eapply Genv.store_zeros_read_as_zero in Hm.
  assert (H0: (4 | 0)). apply Z.divide_0_r.
  assert (Ha: 0 + sz <= Ptrofs.max_unsigned).
  { transitivity sz. lia. subst. eauto. }
  revert Hm. clear Hsz.
  revert sz Heqsz Ha H0 Hp. generalize 0.
  induction H; cbn -[Ptrofs.max_unsigned];
    intros ofs sz Ha Hsz Hdiv Hp Hread.
  - subst. econstructor. reflexivity.
    + specialize (Hread Mint32 ofs).
      exploit Hread; cbn; eauto; try lia.
    + split; eauto.
  - econstructor; eauto.
    + transitivity (ofs + sz); eauto.
      apply Z.add_le_mono_l. subst.
      rewrite Z.mul_comm.
      apply Z.mul_le_mono_nonneg_l.
      pose proof (sizeof_pos ce ty_elem). lia. lia.
    + intros i Hi. specialize (HT i Hi). eauto.
    + intros i Hi. specialize (HV i Hi).
      remember (sizeof ce ty_elem) as a.
      assert (Hofs: ofs + i * a + a <= ofs + sz).
      {
        rewrite <- Z.add_assoc. apply Z.add_le_mono_l.
        rewrite Z.add_comm.
        transitivity (a * (i + 1)). lia.
        subst. apply Z.mul_le_mono_nonneg_l.
        pose proof (sizeof_pos ce ty_elem). lia. lia.
      }
      eapply H; eauto.
      * inv Hd4; eauto.
      * rewrite HT; eauto.
        transitivity (ofs + sz); eauto.
        subst; apply Hofs.
      * apply Z.divide_add_r; eauto.
        apply Z.divide_mul_r. subst. inv Hd4.
        erewrite <- HT; eauto. apply sizeof_type_div4; eauto.
      * intros o Ho. apply Hp. split.
        -- pose proof (sizeof_pos ce ty_elem). subst. lia.
        -- rewrite HT in Ho; eauto. subst. lia.
      * rewrite HT; eauto. eauto.
        eapply read_as_zero_weaken. 3: eauto.
        -- pose proof (sizeof_pos ce ty_elem). lia.
        -- subst. apply Hofs.
  - econstructor; eauto.
    + inv HT. rewrite HCE in Hsz.
      cut (sizeof ce (Tstruct tid attr) <= co_sizeof co). lia.
      cbn. rewrite HCE. reflexivity.
    + intros * Hv Ho. inv HT. rewrite HCE in Hsz.
      assert (ofs' + sizeof ce v <= co_sizeof co) as Hsize1.
      {
        (* TODO: cleanup copy paste *)
        exploit field_type_correct; eauto. intros Hty.
        exploit Ctypes.field_offset_in_range. 2: eauto.
        eapply struct_same_offset; eauto.
        intros [Ha Hb].
        cut (sizeof_struct ce (co_members co) <= co_sizeof co). lia.
        erewrite co_consistent_sizeof; eauto.
        etransitivity.
        2: {
          apply align_le.
          pose proof (co_alignof_two_p co) as (n & Hn). rewrite Hn.
          apply two_power_nat_pos.
        }
        unfold sizeof_composite. rewrite HSU. reflexivity.
      }
      assert (ofs' >= 0) as Hsize2.
      { eapply field_offset_pos; eauto.
        eapply struct_same_offset; eauto. }
      eapply H; eauto.
      * inv Hd4; eauto.
      * lia.
      * apply Z.divide_add_r; eauto. inv Hd4.
        rewrite HCE in H4. inv H4.
        eapply H5; eauto.
        eapply struct_same_offset; eauto.
      * intros o Hr. apply Hp. rewrite HCE. split; lia.
      * eapply read_as_zero_weaken. 3: eauto.
        2: rewrite HCE. 1-2: lia.
Qed.

Fixpoint p0  (xs: list (ident * val)) : penv :=
  match xs with
  | nil => @PTree.empty val
  | ((id, pv) :: rest) => PTree.set id pv (p0 rest)
  end.

Fixpoint m0 ce (xs: list (ident * val)) (se: Genv.symtbl) : mem :=
  match xs with
  | nil => Mem.empty_fragment
  | ((id, ty) :: rest) => mem_combine (init_fragment ce id ty se) (m0 ce rest se)
  end.

Definition valid_pvars (pvars: list (ident * privvar)) se :=
  forall id p, In (id, p) pvars ->
  exists b, Genv.find_symbol se id = Some b.

Definition pvars_ok ce (pvars: list (ident * privvar)) :=
  forall id p, In (id, p) pvars -> pvar_ok ce p.

Inductive penv_mem_match ce: Genv.symtbl -> penv -> Mem.mem -> Prop :=
| penv_mem_match_intro se pe m
    (MPE: forall id v, PTree.get id pe = Some v ->
          exists b, Genv.find_symbol se id = Some b /\
          pvalue_match ce b 0 v m):
  penv_mem_match ce se pe m.

Definition init_of_pvars (vs: list (ident * privvar)) : list (ident * val) :=
  map (fun '(id, v) => (id, pvar_init v)) vs.

Lemma pvalue_match_invariant ce b ofs v m m':
  composite_env_consistent ce ->
  pvalue_match ce b ofs v m ->
  (forall i, ofs <= i < ofs + sizeof ce v ->
        ZMap.get i (Mem.mem_contents m) !! b =
          ZMap.get i (Mem.mem_contents m') !! b) ->
  (forall i k p, ofs <= i < ofs + sizeof ce v ->
            Mem.perm m b i k p -> Mem.perm m' b i k p) ->
  pvalue_match ce b ofs v m'.
Proof.
  intros Hce H HM HP. induction H.
  - cbn in *.
    exploit size_type_chunk. eauto.
    instantiate (1 := ce). intros Hc.
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
    intros i Hi. apply H; eauto.
    + erewrite <- TYPE; eauto.
      intros o Ho. apply HM. cbn.
      pose proof (sizeof_pos ce ty_elem).
      remember (sizeof ce ty_elem) as a.
      split. lia.
      eapply Z.lt_le_trans. apply Ho.
      rewrite <- Z.add_assoc.
      apply Z.add_le_mono_l.
      transitivity (a * (i + 1)). lia.
      subst. cbn. apply Z.mul_le_mono_nonneg_l; lia.
    + erewrite <- TYPE; eauto.
      intros o k p Ho. apply HP. cbn.
      pose proof (sizeof_pos ce ty_elem).
      remember (sizeof ce ty_elem) as a.
      split. lia.
      eapply Z.lt_le_trans. apply Ho.
      rewrite <- Z.add_assoc.
      apply Z.add_le_mono_l.
      transitivity (a * (i + 1)). lia.
      subst. cbn. apply Z.mul_le_mono_nonneg_l; lia.
  - econstructor; eauto.
    intros * Hv Hofs. eapply H; eauto; clear H.
    + intros x Hx. apply HM. subst.
      eapply field_offset_in_range; eauto.
    + intros x * Hx. apply HP. subst.
      eapply field_offset_in_range; eauto.
Qed.

Lemma pvalue_match_combine_l ce b ofs v m m':
  composite_env_consistent ce ->
  init_pv ce v ->
  pvalue_match ce b ofs v m ->
  (forall i, ofs <= i < ofs + sizeof ce v ->
        ZMap.get i (Mem.mem_contents m) !! b <> Undef) ->
  pvalue_match ce b ofs v (mem_combine m m').
Proof.
  intros Hce H HM Hdef. eapply pvalue_match_invariant; eauto.
  - intros i Hi. rewrite mem_gcombine.
    unfold memval_combine. destruct ZMap.get eqn: Hz; try congruence.
    symmetry.
    eapply Hdef in Hz; eauto. easy.
  - intros i k p Hi Hp.
    apply mem_combine_perm_l. eauto.
Qed.

Lemma pvalue_match_combine_r ce b ofs v m m':
  composite_env_consistent ce ->
  init_pv ce v ->
  (forall i, ZMap.get i (Mem.mem_contents m') !! b = Undef) ->
  (forall i k p, ~Mem.perm m' b i k p) ->
  pvalue_match ce b ofs v m ->
  pvalue_match ce b ofs v (mem_combine m' m).
Proof.
  intros Hce HV HM HP H. eapply pvalue_match_invariant; eauto.
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
  forall ce pvars id v,
    pvars_ok ce pvars ->
    (p0 (init_of_pvars pvars)) ! id = Some v ->
    init_pv ce v.
Proof.
  intros * Hok H. induction pvars as [| [id' v'] pvars].
  - inv H.
  - destruct (PMap.elt_eq id id'); cbn in *.
    + subst. rewrite PTree.gss in H. inv H.
      specialize (Hok id' v'). apply Hok. left; eauto.
    + apply IHpvars.
      * intros a b Hab. specialize (Hok a b).
        apply Hok. right; eauto.
      * rewrite PTree.gso in H; eauto.
Qed.

Theorem perm_empty_fragment:
  forall b ofs k p, ~Mem.perm Mem.empty_fragment b ofs k p.
Proof.
  intros. unfold Mem.perm, Mem.empty_fragment; simpl. tauto.
Qed.

Lemma init_fragment_defined se ce id v i b:
  0 <= i < sizeof ce (type_of_pv v) ->
  Genv.find_symbol se id = Some b ->
  ZMap.get i (Mem.mem_contents (init_fragment ce id v se)) !! b <> Undef.
Proof.
  intros Hi Hb.
  edestruct store_zeros_empty_fragment as (m & Hm).
  unfold init_fragment. rewrite Hb. unfold init_fragment'.
  rewrite Hm.
  eapply Genv.store_zeros_loadbytes in Hm.
  unfold Genv.readbytes_as_zero in Hm.
  specialize (Hm i 1%nat).
  exploit Hm. lia. cbn. lia. cbn. intros Hbytes.
  Transparent Mem.loadbytes.
  unfold Mem.loadbytes in Hbytes.
  destruct Mem.range_perm_dec; try congruence. inv Hbytes.
  congruence.
Qed.

Lemma vars_init ce pvars se:
  composite_env_consistent ce ->
  valid_pvars pvars se ->
  pvars_ok ce pvars ->
  penv_mem_match ce se
    (p0 (init_of_pvars pvars))
    (m0 ce (init_of_pvars pvars) se).
Proof.
  intros Hce.
  induction pvars as [| [id v] pvars]; cbn; constructor;
    intros * Hv.
  - rewrite PTree.gempty in Hv. congruence.
  - edestruct H as (b & Hb). left. reflexivity.
    destruct (PMap.elt_eq id0 id).
    + subst. rewrite PTree.gss in Hv. inv Hv.
      exists b. split; eauto.
      apply pvalue_match_combine_l; eauto.
      eapply H0. left; eauto.
      unfold init_fragment. rewrite Hb.
      apply init_pvalue_match; eauto. constructor.
      * eapply H0. left; eauto.
      * eapply H0. constructor. reflexivity.
      * eapply H0. constructor. reflexivity.
      * eapply H0. constructor. reflexivity.
      (* DEFINED *)
      * cbn. intros. eapply init_fragment_defined; eauto.
    + rewrite PTree.gso in Hv; eauto.
      assert (Hvp: valid_pvars pvars se).
      { unfold valid_pvars in *. intros. eapply H. right. eauto. }
      assert (Hok: pvars_ok ce pvars).
      { intros x y Hxy. eapply H0. right. eauto. }
      specialize (IHpvars Hvp Hok).
      inv IHpvars. specialize (MPE _ _ Hv).
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

  Lemma m0_invalid_block ce vars se b ofs:
    ~ Mem.valid_block (m0 ce vars se) b ->
    ZMap.get ofs (Mem.mem_contents (m0 ce vars se)) !! b = Undef.
  Proof.
    induction vars as [| [id a]].
    - intros. simpl. reflexivity.
    - simpl. intros H.
      assert (Hb: ~Mem.valid_block (m0 ce vars se) b).
      { unfold Mem.valid_block, Plt in *. cbn in *. lia. }
      specialize (IHvars Hb).
      rewrite PMap_gcombine. rewrite ZMap_gcombine.
      assert (Hm: ZMap.get ofs (Mem.mem_contents (init_fragment ce id a se)) !! b = Undef).
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

  Lemma m0_alloc_flag ce vars se:
    Mem.alloc_flag (m0 ce vars se) = false.
  Proof.
    induction vars as [| [id a]]; eauto.
    cbn. rewrite IHvars.
    unfold init_fragment.
    destruct Genv.find_symbol.
    - rewrite init_fragment_alloc_flag. easy.
    - reflexivity.
  Qed.

  Lemma join_empty_left ce vars se:
    join Mem.empty_fragment (m0 ce vars se) (m0 ce vars se).
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

  Lemma m0_other_block_content ce vars se id ofs b:
    Genv.find_symbol se id = Some b ->
    ~In id (map fst vars) ->
    ZMap.get ofs (Mem.mem_contents (m0 ce vars se)) !! b = Undef.
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

  Lemma m0_other_block_perm ce vars se id ofs b:
    Genv.find_symbol se id = Some b ->
    ~In id (map fst vars) ->
    ~Mem.perm (m0 ce vars se) b ofs Max Nonempty.
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

  Definition vars_type_ok ce (vars: list (ident * val)):=
    forall id v, In (id, v) vars -> pv_type_ok ce v.

  Lemma sizeof_vars_same ce1 ce2 v:
    (forall id co, ce1!id = Some co -> ce2!id = Some co) ->
    pv_type_ok ce1 v ->
    sizeof ce1 (type_of_pv v) = sizeof ce2 (type_of_pv v).
  Proof.
    intros Hext Hv. induction Hv.
    - reflexivity.
    - cbn.
      (* destruct on 0 < n and 0 >= n *)
      destruct (Z_lt_ge_dec 0 n).
      + (* rewrite Z.max 0 n to n *)
        rewrite Z.max_r by lia. f_equal.
        specialize (H1 0). rewrite !H1 by lia.
        eapply H0. lia.
      + (* rewrite Z.max 0 n to 0 *)
        rewrite Z.max_l by lia.
        rewrite !Z.mul_0_r. reflexivity.
    - cbn. inv H. rewrite HCE. erewrite Hext; eauto.
  Qed.

  Context (ce ce1 ce2: composite_env)
    (Hce1: forall id co, ce1!id = Some co -> ce!id = Some co)
    (Hce2: forall id co, ce2!id = Some co -> ce!id = Some co).

  Lemma disjoint_init_mem:
    forall se vars1 vars2,
      vars_disjoint vars1 vars2 ->
      vars_type_ok ce1 vars1 ->
      vars_type_ok ce2 vars2 ->
      join (m0 ce1 vars1 se) (m0 ce2 vars2 se)
        (m0 ce (vars1 ++ vars2) se).
  Proof.
    intros *. revert vars2.
    induction vars1 as [| [id pv] ]; intros; cbn.
    - assert (m0 ce2 vars2 se = m0 ce vars2 se).
      {
        clear -Hce2 H1. induction vars2. reflexivity.
        cbn. destruct a.
        rewrite IHvars2. f_equal.
        + unfold init_fragment.
          eapply sizeof_vars_same in Hce2.
          rewrite Hce2. reflexivity.
          eapply H1. left; eauto.
        + intros x y Hx. eapply H1. right; eauto.
      }
      rewrite H2. apply join_empty_left.
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
        assert (sizeof ce1 pv = sizeof ce pv).
        { apply sizeof_vars_same; eauto.
          eapply H0. left; eauto. }
        rewrite H3.
        eapply join_combine_left.
        * intros ofs. eapply m0_other_block_perm; eauto.
        * intros ofs. eapply m0_other_block_content; eauto.
        * apply m0_alloc_flag.
        * apply m0_alloc_flag.
        * apply IHvars1; eauto.
          intros x y Hx. eapply H0. right; eauto.
      + apply join_combine_empty_fragment; eauto.
        eapply IHvars1; eauto.
        intros x y Hx. eapply H0. right; eauto.
  Qed.

End DISJOINT.
