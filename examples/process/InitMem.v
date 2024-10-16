Require Import Maps Coqlib Integers List.
Require Import AST Globalenvs Memory Values.
Import ListNotations.

Section INIT_MEM.
  Context (se: Genv.symtbl).

  Program Definition empty : mem :=
    Mem.mkmem (PMap.init (ZMap.init Undef))
      (PMap.init (fun ofs k => None))
      (Genv.genv_next se) true _ _ _.

  Local Notation "a # b" := (PMap.get b a) (at level 1).

  (* like [Mem.alloc], but only changes the perm *)
  Program Definition init_perm (m: mem) (b: block) (lo hi: Z) :=
    if plt b m.(Mem.nextblock) then
      Some
        (Mem.mkmem
           m.(Mem.mem_contents)
           (PMap.set b
              (fun ofs k => if zle lo ofs && zlt ofs hi
                         then Some Freeable
                         else m.(Mem.mem_access)#b ofs k)
              m.(Mem.mem_access))
           m.(Mem.nextblock) m.(Mem.alloc_flag) _ _ _)
    else None.
  Next Obligation.
    repeat rewrite PMap.gsspec. destruct (peq b0 b).
    - subst b. destruct (zle lo ofs && zlt ofs hi); red; auto with mem.
      apply (Mem.access_max m b0 ofs).
    - apply Mem.access_max.
  Qed.
  Next Obligation.
    repeat rewrite PMap.gsspec. destruct (peq b0 b).
    - subst b. elim H0. exact H.
    - eapply Mem.nextblock_noaccess. exact H0.
  Qed.
  Next Obligation. apply Mem.contents_default. Qed.

  Lemma init_perm_1 m1 m2 lo hi b:
    init_perm m1 b lo hi = Some m2 ->
    forall ofs k, lo <= ofs < hi -> Mem.perm m2 b ofs k Freeable.
  Proof.
    intros. unfold init_perm in H. destruct plt; inv H.
    unfold Mem.perm. cbn. rewrite PMap.gss.
    destruct (zle lo ofs && zlt ofs hi) eqn: H1; try constructor.
    exfalso. destruct zle eqn: H2; try lia. destruct zlt eqn: H3; try lia.
    cbn in H1. congruence.
  Qed.

  Theorem init_perm_3 b lo hi m m':
    init_perm m b lo hi = Some m' ->
    forall b' ofs k p', b' <> b \/ ofs < lo \/ hi <= ofs -> Mem.perm m b' ofs k p' -> Mem.perm m' b' ofs k p'.
  Proof.
    intros.
    unfold init_perm in H. destruct plt; inv H.
    unfold Mem.perm; simpl. rewrite PMap.gsspec. destruct (peq b' b).
    - subst b'. destruct H0. lia.
      unfold proj_sumbool. destruct (zle lo ofs); destruct (zlt ofs hi);
        try lia; eauto.
    - apply H1.
  Qed.

  Theorem init_perm_4 b lo hi m m':
    init_perm m b lo hi = Some m' ->
    forall b' ofs k p', b' <> b \/ ofs < lo \/ hi <= ofs -> Mem.perm m' b' ofs k p' -> Mem.perm m b' ofs k p'.
  Proof.
    intros.
    unfold init_perm in H. destruct plt; inv H.
    unfold Mem.perm in *; simpl in *.
    rewrite PMap.gsspec in H1. destruct (peq b' b).
    - subst b'. destruct H0. lia.
      unfold proj_sumbool. destruct (zle lo ofs); destruct (zlt ofs hi);
        try lia; eauto.
    - apply H1.
  Qed.

  Definition init_global' (m: mem) (b: block) (g: globdef unit unit): option mem :=
    match g with
    | Gfun f =>
        match init_perm m b 0 1 with
        | Some m1 => Mem.drop_perm m1 b 0 1 Nonempty
        | None => None
        end
    | Gvar v =>
        let init := v.(gvar_init) in
        let sz := init_data_list_size init in
        match init_perm m b 0 sz with
        | Some m1 =>
            match store_zeros m1 b 0 sz with
            | None => None
            | Some m2 =>
                match Genv.store_init_data_list se m2 b 0 init with
                | None => None
                | Some m3 => Mem.drop_perm m3 b 0 sz (Genv.perm_globvar v)
                end
            end
        | None => None
        end
    end.

  Definition init_global (m: mem) (idg: ident * globdef unit unit): option mem :=
    match idg with
    | (id, g) =>
        match Genv.find_symbol se id with
        | Some b => init_global' m b g
        | None => None
        end
    end.

  Fixpoint init_globals (m: mem) (gl: list (ident * globdef unit unit)): option mem :=
    match gl with
    | [] => Some m
    | g :: gl' =>
        match init_global m g with
        | None => None
        | Some m' => init_globals m' gl'
        end
    end.

  Definition init_mem (p: AST.program unit unit) : option mem :=
    init_globals empty p.(AST.prog_defs).

  Lemma init_global_exists:
    forall m idg,
      (exists b, Genv.find_symbol se (fst idg) = Some b /\
              Plt b m.(Mem.nextblock)) ->
      match idg with
      | (id, Gfun f) => True
      | (id, Gvar v) =>
          Genv.init_data_list_aligned 0 v.(gvar_init)
          /\ forall i o, In (Init_addrof i o) v.(gvar_init) -> exists b, Genv.find_symbol se i = Some b
      end ->
      exists m', init_global m idg = Some m'.
  Proof.
    intros m [id [f|v]] [b [Hb1 Hb2]]; intros; simpl in *; rewrite Hb1.
    - destruct (init_perm m b 0 1) as [m1|] eqn:H1.
      2: { exfalso. unfold init_perm in H1. destruct plt; [ inv H1 | contradiction ]. }
      destruct (Mem.range_perm_drop_2 m1 b 0 1 Nonempty) as [m2 DROP].
      red; intros; eapply init_perm_1; eauto.
      exists m2. eauto.
    - destruct H as [P Q].
      set (sz := init_data_list_size (gvar_init v)).
      destruct (init_perm m b 0 sz) as [m1|] eqn:H1.
      2: { exfalso. unfold init_perm in H1. destruct plt; [ inv H1 | contradiction ]. }
      assert (P1: Mem.range_perm m1 b 0 sz Cur Freeable) by (red; intros; eapply init_perm_1; eauto).
      exploit (@Genv.store_zeros_exists m1 b 0 sz).
      { red; intros. apply Mem.perm_implies with Freeable; auto with mem. }
      intros [m2 ZEROS]. rewrite ZEROS.
      assert (P2: Mem.range_perm m2 b 0 sz Cur Freeable).
      { red; intros. erewrite <- Genv.store_zeros_perm by eauto. eauto. }
      exploit (@Genv.store_init_data_list_exists se b (gvar_init v) m2 0); eauto.
      { red; intros. apply Mem.perm_implies with Freeable; auto with mem. }
      intros [m3 STORE]. rewrite STORE.
      assert (P3: Mem.range_perm m3 b 0 sz Cur Freeable).
      { red; intros. erewrite <- Genv.store_init_data_list_perm by eauto. eauto. }
      destruct (Mem.range_perm_drop_2 m3 b 0 sz (Genv.perm_globvar v)) as [m4 DROP]; auto.
      exists m4; auto.
  Qed.

  Lemma init_perm_nextblock m1 m2 b lo hi:
    init_perm m1 b lo hi = Some m2 ->
    Mem.nextblock m2 = Mem.nextblock m1.
  Proof.
    intros. unfold init_perm in H. destruct plt; inv H.
    cbn. reflexivity.
  Qed.

  Lemma init_global_nextblock m1 m2 idg:
    init_global m1 idg = Some m2 ->
    Mem.nextblock m1 = Mem.nextblock m2.
  Proof.
    intros. unfold init_global in H. destruct idg as [id [f|v]]; simpl in H.
    - destruct (Genv.find_symbol se id) as [b|] eqn: H1; inv H.
      destruct (init_perm m1 b 0 1) as [m|] eqn: A1; inv H2.
      erewrite <- init_perm_nextblock; [ | eauto ].
      erewrite <- Mem.nextblock_drop; eauto.
    - destruct (Genv.find_symbol se id) as [b|] eqn: H1; inv H.
      destruct init_perm as [m3|] eqn: A1; inv H2.
      destruct store_zeros as [m4|] eqn: A2; inv H0.
      destruct Genv.store_init_data_list as [m5|] eqn: A3; inv H2.
      erewrite <- init_perm_nextblock; [ | eauto ].
      erewrite <- Genv.store_zeros_nextblock; [ | eauto ].
      erewrite <- Genv.store_init_data_list_nextblock; [ | eauto ].
      erewrite <- Mem.nextblock_drop; eauto.
  Qed.

  Lemma init_mem_exists p:
    (forall id v, In (id, Gvar v) (AST.prog_defs p) ->
             Genv.init_data_list_aligned 0 v.(gvar_init)
             /\ forall i o, In (Init_addrof i o) v.(gvar_init) -> exists b, Genv.find_symbol se i = Some b) ->
    Genv.valid_for p se ->
    exists m, init_mem p = Some m.
  Proof.
    intros. unfold init_mem.
    assert (H1: forall id g,
               In (id, g) (AST.prog_defs p) ->
               exists b, Genv.find_symbol se id = Some b
                    /\ Plt b (Mem.nextblock empty)).
    {
      intros. edestruct prog_defmap_dom as [g' Hg'].
      unfold prog_defs_names. apply in_map_iff.
      exists (id, g). split; eauto. cbn in Hg'.
      specialize (H0 _ _ Hg') as (b & ? & Hb & ? & ?).
      exists b; split; eauto.
      unfold empty. cbn. eapply Genv.genv_symb_range.
      apply Hb.
    }
    clear H0.
    revert H H1. generalize (AST.prog_defs p) empty.
    induction l as [ | idg l ]; simpl; intros.
    - exists m. reflexivity.
    - destruct (@init_global_exists m idg) as [m1 A1].
      + destruct idg as [id g]. apply (H1 id g). left; easy.
      + destruct idg as [id [f|v]]; eauto.
      + rewrite A1. edestruct (IHl m1) as [m2 IH]; eauto.
        intros. erewrite <- init_global_nextblock; eauto.
  Qed.

  Lemma init_mem_nextblock p m:
    init_mem p = Some m ->
    Mem.nextblock m = Genv.genv_next se.
  Proof.
    assert (H: Mem.nextblock empty = Genv.genv_next se) by reflexivity.
    revert H. unfold init_mem. generalize (AST.prog_defs p) empty.
    induction l as [ | idg l ]; simpl; intros.
    - inv H0. eauto.
    - destruct init_global eqn: A1; inv H0.
      erewrite <- IHl; [ eauto | | eauto ].
      rewrite <- H. symmetry.  eapply init_global_nextblock; eauto.
  Qed.

  Lemma init_global_alloc_flag m1 m2 idg:
    init_global m1 idg = Some m2 ->
    Mem.alloc_flag m2 = Mem.alloc_flag m1.
  Proof.
    intros. unfold init_global in H. destruct idg as [id [f|v]]; simpl in H.
    - destruct (Genv.find_symbol se id) as [b|] eqn: H1; inv H.
      destruct (init_perm m1 b 0 1) as [m|] eqn: A1; inv H2.
      unfold init_perm in A1. destruct plt; inv A1.
      unfold Mem.drop_perm in H0. destruct Mem.range_perm_dec; inv H0.
      cbn. reflexivity.
    - destruct (Genv.find_symbol se id) as [b|] eqn: H1; inv H.
      destruct init_perm as [m3|] eqn: A1; inv H2.
      destruct store_zeros as [m4|] eqn: A2; inv H0.
      destruct Genv.store_init_data_list as [m5|] eqn: A3; inv H2.
      apply Genv.store_zeros_alloc_flag in A2.
      apply Genv.store_init_data_list_alloc_flag in A3.
      unfold init_perm in A1. destruct plt; inv A1.
      unfold Mem.drop_perm in H0. destruct Mem.range_perm_dec; inv H0.
      cbn in *. congruence.
  Qed.

  Lemma init_mem_alloc_flag p m:
    init_mem p = Some m ->
    Mem.alloc_flag m = true.
  Proof.
    assert (Mem.alloc_flag empty = true) by reflexivity. revert H.
    unfold init_mem. generalize (AST.prog_defs p) empty.
    induction l as [ | idg l ]; simpl; intros.
    - inv H0. eauto.
    - destruct init_global eqn: A1; inv H0.
      apply init_global_alloc_flag in A1.
      rewrite <- A1 in H. eauto.
  Qed.

  Section INJ.

    Variable thr: block.
    Hypothesis THR: Ple (Genv.genv_next se) thr.

    Lemma init_perm_drop_perm_inject_neutral:
      forall m1 m2 m3 b lo hi,
        init_perm m1 b lo hi = Some m2 ->
        Mem.drop_perm m2 b lo hi Nonempty = Some m3 ->
        Mem.inject_neutral thr m1 ->
        Mem.inject_neutral thr m3.
    Proof.
      unfold Mem.inject_neutral. intros * HI HD HINJ.
      constructor; cbn.
      - intros. unfold Mem.flat_inj in H.
        destruct plt; inv H. rewrite Z.add_0_r; eauto.
      - intros. unfold Mem.flat_inj in H.
        destruct plt; inv H. apply Z.divide_0_r.
      - intros. destruct (peq b1 b); subst.
        + destruct (zle lo ofs && zlt ofs hi) eqn: H1.
          * exfalso. eapply Mem.perm_drop_2 in H0; eauto. inv H0.
            destruct zle; destruct zlt; cbn in *; try solve [lia | easy].
          * replace (Mem.mem_contents m3) with (Mem.mem_contents m1).
            2: { unfold Mem.drop_perm in HD. destruct Mem.range_perm_dec; inv HD.
                 unfold init_perm in HI. destruct plt; inv HI. reflexivity. }
            eapply HINJ; eauto.
            eapply init_perm_4; eauto. right.
            destruct zle; destruct zlt; try solve [lia | easy].
            eapply Mem.perm_drop_4; eauto.
        + replace (Mem.mem_contents m3) with (Mem.mem_contents m1).
          2: { unfold Mem.drop_perm in HD. destruct Mem.range_perm_dec; inv HD.
               unfold init_perm in HI. destruct plt; inv HI. reflexivity. }
          eapply HINJ; eauto.
          eapply init_perm_4; eauto. eapply Mem.perm_drop_4; eauto.
    Qed.

    Local Transparent Mem.loadbytes.

    Lemma store_zeros_content_1 m1 m2 b start len ofs:
      store_zeros m1 b start len = Some m2 ->
      start <= ofs < start + len ->
      ZMap.get ofs (m2.(Mem.mem_contents)#b) = Byte Byte.zero.
    Proof.
      intros. exploit Genv.store_zeros_loadbytes; eauto.
      - instantiate (1 := ofs). lia.
      - instantiate (1 := 1%nat). lia.
      - intros Hx.
        unfold Mem.loadbytes in Hx.
        destruct Mem.range_perm_dec; inv Hx. reflexivity.
    Qed.

    Lemma store_zeros_content_2 m1 m2 b b' start len ofs:
      store_zeros m1 b start len = Some m2 ->
      b' <> b \/ ofs < start \/ start + len <= ofs ->
      Mem.perm m1 b' ofs Cur Readable ->
      ZMap.get ofs (m2.(Mem.mem_contents)#b') = ZMap.get ofs (m1.(Mem.mem_contents)#b').
    Proof.
      intros.
      eapply Genv.store_zeros_unchanged with
        (P := fun b' ofs => b' <> b \/ ofs < start \/ start + len <= ofs) in H.
      2: lia.
      eapply Mem.unchanged_on_contents; eauto.
    Qed.

    Lemma init_perm_store_zeros_inject_neutral:
      forall m1 m2 m3 b sz,
        init_perm m1 b 0 sz = Some m2 ->
        store_zeros m2 b 0 sz = Some m3 ->
        Mem.inject_neutral thr m1 ->
        Mem.inject_neutral thr m3.
    Proof.
      unfold Mem.inject_neutral. intros * HI HD HINJ.
      constructor; cbn.
      - intros. unfold Mem.flat_inj in H.
        destruct plt; inv H. rewrite Z.add_0_r; eauto.
      - intros. unfold Mem.flat_inj in H.
        destruct plt; inv H. apply Z.divide_0_r.
      - intros. destruct (peq b1 b); subst.
        + destruct (zle 0 ofs && zlt ofs sz) eqn: H1.
          * destruct zle; destruct zlt; cbn in *; try solve [lia | easy].
            unfold Mem.flat_inj in H. destruct plt; inv H.
            rewrite Z.add_0_r.
            erewrite !store_zeros_content_1; eauto. constructor.
          * exploit (Mem.mi_memval _ _ _ HINJ); eauto.
            -- instantiate (1 := ofs).
               eapply init_perm_4; eauto. right.
               destruct zle; destruct zlt; try solve [lia | easy].
               eapply Genv.store_zeros_perm; eauto.
            -- unfold Mem.flat_inj in H. destruct plt; inv H.
               rewrite !Z.add_0_r. intros.
               eapply store_zeros_content_2 in HD.
               ++ rewrite HD. unfold init_perm in HI. destruct plt; inv HI. eauto.
               ++ right. destruct zle; destruct zlt; try solve [lia | easy].
               ++ eapply Genv.store_zeros_perm; eauto.
        + exploit (Mem.mi_memval _ _ _ HINJ); eauto.
          * instantiate (1 := ofs).
            eapply init_perm_4; eauto.
            eapply Genv.store_zeros_perm; eauto.
          * unfold Mem.flat_inj in H. destruct plt; inv H.
            rewrite !Z.add_0_r. intros.
            eapply store_zeros_content_2 in HD.
            -- rewrite HD. unfold init_perm in HI. destruct plt; inv HI. eauto.
            -- left. eauto.
            -- eapply Genv.store_zeros_perm; eauto.
    Qed.

    Lemma init_global_neutral:
      forall idg m m',
        init_global m idg = Some m' ->
        Mem.inject_neutral thr m ->
        Ple (Mem.nextblock m) thr ->
        Mem.inject_neutral thr m'.
    Proof.
      intros [id [f|v]] m m' H1 H2 H3; simpl in *.
      - destruct (Genv.find_symbol se id) as [b|] eqn: H4; inv H1.
        destruct (init_perm m b 0 1) as [m1|] eqn: H5; inv H0.
        eapply init_perm_drop_perm_inject_neutral; eauto.
      - destruct (Genv.find_symbol se id) as [b|] eqn: H4; inv H1.
        destruct (init_perm m b 0 (init_data_list_size (gvar_init v))) as [m1|] eqn: H5; inv H0.
        destruct store_zeros as [m2|] eqn: H6; inv H1.
        destruct Genv.store_init_data_list as [m3|] eqn: H7; inv H0.
        assert (Plt b thr).
        { unfold init_perm in H5. destruct plt; inv H5.
          eapply Plt_Ple_trans; eauto. }
        eapply Mem.drop_inject_neutral; eauto.
        eapply Genv.store_init_data_list_neutral. 3, 4: eauto.
        intros. apply Genv.genv_symb_range in H0.
        eapply Plt_Ple_trans; eauto.
        eapply init_perm_store_zeros_inject_neutral; eauto.
    Qed.

    Lemma init_globals_neutral:
      forall gl m m',
        init_globals m gl = Some m' ->
        Mem.inject_neutral thr m ->
        Ple (Mem.nextblock m) thr ->
        Mem.inject_neutral thr m'.
    Proof.
      induction gl as [ | g gl ]; simpl; intros.
      - inv H. eauto.
      - destruct init_global eqn: A1; inv H.
        eapply IHgl. eauto.
        + eapply init_global_neutral; eauto.
        + erewrite <- init_global_nextblock; eauto.
    Qed.

  End INJ.

  Lemma empty_inject:
    Mem.inject_neutral (Genv.genv_next se) empty.
  Proof.
    unfold Mem.inject_neutral. unfold Mem.flat_inj. constructor.
    - intros. inv H0.
    - intros. specialize (H0 ofs).
      exploit H0. 2: easy.
      pose proof (size_chunk_pos chunk). lia.
    - intros. inv H0.
  Qed.

  Lemma initmem_inject m p:
    init_mem p = Some m -> Mem.inject (Mem.flat_inj (Mem.nextblock m)) m m.
  Proof.
    intros. exploit init_mem_nextblock; eauto. intros NB.
    unfold init_mem.
    apply Mem.neutral_inject.
    eapply init_globals_neutral; eauto.
    - rewrite NB. reflexivity.
    - rewrite NB. apply empty_inject.
    - cbn. rewrite NB. reflexivity.
  Qed.

End INIT_MEM.

Require ValueAnalysis VAInject.

Hypothesis
  (init_mem_romatch: forall se sk m,
      init_mem se sk = Some m -> ValueAnalysis.romatch_all se (VAInject.bc_of_symtbl se) m).
