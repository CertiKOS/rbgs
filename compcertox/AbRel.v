From Coq Require Import
     Relations RelationClasses List.
From compcertox Require Import
     Lifting.
From compcert.lib Require Import
     Coqlib Maps.
From compcert.common Require Import
     LanguageInterface Events
     Globalenvs Smallstep
     Linking Memory Values
     CallconvAlgebra.
From compcert.cklr Require Import
     CKLR Extends Clightrel.
From compcert.cfrontend Require Import
     SimplLocalsproof Clight.

Fixpoint unchecked_free_list (m: mem) (l: list (block * Z * Z)): mem :=
  match l with
  | nil => m
  | (b, lo, hi) :: l' =>
      unchecked_free_list (Mem.unchecked_free m b lo hi) l'
  end.

Lemma perm_unchecked_free_3:
  forall m1 bf lo hi m2,
  Mem.unchecked_free m1 bf lo hi = m2 ->
  forall b ofs k p,
  Mem.perm m2 b ofs k p -> Mem.perm m1 b ofs k p.
Proof.
  intros until p. rewrite <- H.
  unfold Mem.perm, Mem.unchecked_free; simpl.
  rewrite PMap.gsspec. destruct (peq b bf). subst b.
  destruct (zle lo ofs); simpl.
  destruct (zlt ofs hi); simpl. tauto.
  auto. auto. auto.
Qed.

Lemma perm_unchecked_free_list_3:
  forall m1 l m2,
  unchecked_free_list m1 l = m2 ->
  forall b ofs k p,
  Mem.perm m2 b ofs k p -> Mem.perm m1 b ofs k p.
Proof.
  intros m1 l. revert m1. induction l.
  - intros * <- *. easy.
  - intros * H * HP. destruct a as [[bf lo] hi].
    exploit IHl; eauto.
    intros X. eapply perm_unchecked_free_3; eauto.
Qed.

Lemma perm_unchecked_free_2:
  forall m1 bf lo hi m2,
  Mem.unchecked_free m1 bf lo hi = m2 ->
  forall ofs k p, lo <= ofs < hi -> ~ Mem.perm m2 bf ofs k p.
Proof.
  intros. rewrite <- H. unfold Mem.perm, Mem.unchecked_free; simpl.
  rewrite PMap.gss. unfold proj_sumbool.
  rewrite zle_true. rewrite zlt_true.
  simpl. tauto. omega. omega.
Qed.

Lemma perm_unchecked_free_list_2:
  forall m1 l m2, unchecked_free_list m1 l = m2 ->
  forall bf lo hi ofs k p, In (bf, lo, hi) l -> lo <= ofs -> ofs < hi -> ~ Mem.perm m2 bf ofs k p.
Proof.
  intros m1 l. revert m1. induction l.
  - intros * <- * A B C. inv A.
  - intros * H * A B C.
    destruct a as [[bx lox] hix].
    cbn in A. elim A.
    + intros X. inv X.
      cbn. intros X. exploit perm_unchecked_free_list_3.
      2: exact X. reflexivity.
      eapply perm_unchecked_free_2. reflexivity. omega.
    + intros X. eapply IHl; eauto.
Qed.

Lemma perm_unchecked_free_1:
  forall m1 bf lo hi m2,
  Mem.unchecked_free m1 bf lo hi = m2 ->
  forall b ofs k p,
  b <> bf \/ ofs < lo \/ hi <= ofs ->
  Mem.perm m1 b ofs k p ->
  Mem.perm m2 b ofs k p.
Proof.
  intros. rewrite <- H. unfold Mem.perm, Mem.unchecked_free; simpl.
  rewrite PMap.gsspec. destruct (peq b bf). subst b.
  destruct (zle lo ofs); simpl.
  destruct (zlt ofs hi); simpl.
  elimtype False; intuition.
  auto. auto.
  auto.
Qed.

Lemma perm_unchecked_free_inv:
  forall m1 bf lo hi m2,
  Mem.unchecked_free m1 bf lo hi = m2 ->
  forall b ofs k p,
  Mem.perm m1 b ofs k p ->
  (b = bf /\ lo <= ofs < hi) \/ Mem.perm m2 b ofs k p.
Proof.
  intros. rewrite <- H. unfold Mem.perm, Mem.unchecked_free; simpl.
  rewrite PMap.gsspec. destruct (peq b bf); auto. subst b.
  destruct (zle lo ofs); simpl; auto.
  destruct (zlt ofs hi); simpl; auto.
Qed.

Lemma perm_unchecked_free_list_inv:
  forall m1 l m2,
  unchecked_free_list m1 l = m2 ->
  forall b ofs k p,
  Mem.perm m1 b ofs k p ->
  (exists '(bf, lo, hi), In (bf, lo, hi) l /\ b = bf /\ lo <= ofs < hi)
  \/ Mem.perm m2 b ofs k p.
Proof.
  intros *. revert m1 m2. induction l.
  - intros * <- * Hp. right. exact Hp.
  - intros * HF * HP. destruct a as [[bf lo] hi].
    cbn in HF.
    remember (Mem.unchecked_free m1 bf lo hi) as mx eqn: HX.
    exploit perm_unchecked_free_inv.
    symmetry. apply HX. apply HP. intros [A|A].
    + left. exists (bf, lo, hi). split; try easy. apply in_eq.
    + exploit IHl. apply HF. apply A. intros [B|B].
      * left. destruct B as (x & Hx).
        exists x. destruct x. destruct p0. split; try easy.
        apply in_cons. easy.
      * now right.
Qed.

Lemma unchecked_free_left_extends:
  forall m1 m2 b lo hi m1',
  Mem.extends m1 m2 ->
  Mem.unchecked_free m1 b lo hi = m1' ->
  Mem.extends m1' m2.
Proof.
  intros. inv H. constructor.
  - apply mext_next.
  - inversion mext_inj. constructor.
    + intros. eapply mi_perm; eauto using perm_unchecked_free_3.
    + intros. eapply mi_align with (ofs := ofs) (p := p); eauto.
      red; intros; eapply perm_unchecked_free_3; eauto.
    + intros. simpl. eauto using perm_unchecked_free_3.
  - intros. exploit mext_perm_inv; eauto. intros [A|A].
    eapply perm_unchecked_free_inv in A; eauto.
    destruct A as [[A B]|A]; auto.
    right; eapply perm_unchecked_free_2; eauto.
    rewrite A. reflexivity.
    left. apply A. intuition eauto using perm_unchecked_free_3.
Qed.

Lemma unchecked_free_right_extends:
  forall m1 m2 b lo hi m2',
  Mem.extends m1 m2 ->
  Mem.unchecked_free m2 b lo hi = m2' ->
  (forall ofs k p, Mem.perm m1 b ofs k p -> lo <= ofs < hi -> False) ->
  Mem.extends m1 m2'.
Proof.
  intros. inv H. constructor.
  - apply mext_next.
  - inversion mext_inj. constructor.
    + intros. eapply perm_unchecked_free_1; eauto.
      unfold inject_id in H. inv H.
      destruct (eq_block b2 b); auto. subst b. right.
      assert (~ (lo <= ofs < hi)).
      red; intros; eapply H1; eauto.
      omega.
    + eapply mi_align; eauto.
    + intros. simpl. eauto.
  - intros. eauto using perm_unchecked_free_3.
Qed.

Lemma unchecked_free_list_left_extends:
  forall m1 m2 l m1',
  Mem.extends m1 m2 ->
  unchecked_free_list m1 l = m1' ->
  Mem.extends m1' m2.
Proof.
  intros until l. revert m1 m2. induction l.
  - intros * EXT <-. apply EXT.
  - intros * EXT H. destruct a as [[b lo] hi].
    cbn in H. eapply Mem.extends_extends_compose.
    + eapply IHl. 2: exact H.
      exploit unchecked_free_left_extends; eauto.
    + apply Mem.extends_refl.
Qed.

Lemma unchecked_free_list_right_extends:
  forall m1 m2 l m2',
  Mem.extends m1 m2 ->
  unchecked_free_list m2 l = m2' ->
  (forall b lo hi ofs k p,
      In (b, lo, hi) l -> Mem.perm m1 b ofs k p -> lo <= ofs < hi -> False) ->
  Mem.extends m1 m2'.
Proof.
  intros until l. revert m1 m2. induction l.
  - intros * EXT <- H. apply EXT.
  - intros * EXT H1 H2. destruct a as [[b lo] hi].
    cbn in H1.
    exploit unchecked_free_right_extends. exact EXT.
    instantiate (1 := Mem.unchecked_free m2 b lo hi). reflexivity.
    intros. eapply H2; eauto. apply in_eq.
    intros X. eapply IHl. exact X. exact H1.
    intros. eapply H2. apply in_cons.
    all: eassumption.
Qed.

Lemma unchecked_free_unchanged_on P m b lo hi m':
  Mem.unchecked_free m b lo hi = m' ->
  (forall i : Z, lo <= i < hi -> ~ P b i) -> Mem.unchanged_on P m m'.
Proof.
  intros; constructor; intros.
  - subst. reflexivity.
  - split; intros.
    eapply perm_unchecked_free_1; eauto.
    destruct (eq_block b0 b); auto. destruct (zlt ofs lo); auto. destruct (zle hi ofs); auto.
    subst b0. elim (H0 ofs). omega. auto.
    eapply perm_unchecked_free_3; eauto.
  - subst. simpl. auto.
Qed.

Lemma unchecked_free_list_unchanged_on P m l m':
  unchecked_free_list m l = m' ->
  (forall b ofs lo hi, In (b, lo, hi) l -> lo <= ofs -> ofs < hi -> ~ P b ofs) ->
  Mem.unchanged_on P m m'.
Proof.
  revert m m'. induction l.
  - intros * <- H. cbn. apply Mem.unchanged_on_refl.
  - intros * H HP. destruct a as [[b lo] hi]. cbn in H.
    eapply Mem.unchanged_on_trans.
    + eapply unchecked_free_unchanged_on.
      instantiate (1 := Mem.unchecked_free m b lo hi). reflexivity.
      intros. eapply HP. apply in_eq. omega. omega.
    + apply IHl; eauto. intros.
      eapply HP. apply in_cons. all: eauto.
Qed.

Section LOCS.
  Context (se: Genv.symtbl).
  Definition locp: ident * Z -> block -> Z -> Prop :=
    fun '(name, size) b ofs =>
      Genv.find_symbol se name = Some b /\ 0 <= ofs /\ ofs < size.
  Definition locsp: list (ident * Z) -> block -> Z -> Prop :=
    fun l b ofs => Exists (fun x => locp x b ofs) l.
  Definition loc: ident * Z -> option (block * Z * Z) :=
    fun '(name, size) =>
      match Genv.find_symbol se name with
      | Some b => Some (b, 0, size)
      | None => None
      end.
  Fixpoint locs (ns: list (ident * Z)) : list (block * Z * Z) :=
    match ns with
    | n::rest =>
        match loc n with
        | Some l => l :: locs rest
        | None => locs rest
        end
    | nil => nil
    end.

  Lemma locsp_app ns1 ns2:
    forall b ofs, locsp (ns1 ++ ns2) b ofs <-> locsp ns1 b ofs \/ locsp ns2 b ofs.
  Proof.
    intros *. induction ns1.
    - cbn. split; intros.
      + now right.
      + destruct H. inv H. apply H.
    - rewrite <- app_comm_cons. split.
      + intros H. inv H.
        * left. now apply Exists_cons_hd.
        * setoid_rewrite IHns1 in H1.
          destruct H1.
          -- left. now apply Exists_cons_tl.
          -- now right.
      + intros H. destruct H.
        * inv H.
          -- now apply Exists_cons_hd.
          -- apply Exists_cons_tl.
             apply IHns1. now left.
        * apply Exists_cons_tl.
          apply IHns1. now right.
  Qed.

  Lemma loc_iff (n: ident) (s: Z):
    forall b ofs,
      locp (n,s) b ofs <->
        loc (n,s) = Some (b, 0, s) /\ 0 <= ofs /\ ofs < s.
  Proof.
    intros *. split; cbn.
    - intros (Hb & Hofs). rewrite Hb. now split.
    - intros (Hb & Hofs). destruct Genv.find_symbol; try congruence.
      inv Hb. now split.
  Qed.
  Lemma locs_iff (ns: list (ident * Z)) :
    forall b ofs,
      locsp ns b ofs <->
        exists '(bi, lo, hi), In (bi, lo, hi) (locs ns) /\
                           bi = b /\ lo <= ofs /\ ofs < hi.
  Proof.
    induction ns.
    - intros *; split; cbn.
      + unfold locsp. rewrite Exists_nil. easy.
      + intros ([[? ?] ?] & ?). easy.
    - intros *. split; cbn.
      + intros H. inv H.
        * destruct a. rewrite loc_iff in H1.
          exists (b, 0, z). destruct H1 as (Hb & Hofs).
          rewrite Hb. repeat apply conj; try easy.
          apply in_eq.
        * setoid_rewrite IHns in H1.
          destruct H1 as (bx & Hb).
          exists bx. destruct bx as [[bx lo] hi].
          split. 2: easy. destruct (loc a).
          -- apply in_cons. easy.
          -- easy.
      + intros ([[bx lo] hi] & Hin & Hb & Hlo & Hhi).
        destruct (loc a) eqn: Hloc.
        * inv Hin.
          -- apply Exists_cons_hd.
             destruct a. apply loc_iff.
             cbn in Hloc.
             destruct Genv.find_symbol eqn: Hs; try congruence.
             inv Hloc. cbn. rewrite Hs. split; easy.
          -- apply Exists_cons_tl.
             apply IHns. exists (b, lo, hi). split; easy.
        * apply Exists_cons_tl.
          apply IHns. exists (b, lo, hi). subst. split; easy.
  Qed.

End LOCS.

(** The relation Rr is parametrized by the symbol table so that we do not have
    to bind the variables being abstracted to particular blocks *)
Record abrel {Ks Kf: Type}: Type :=
  mk_abrel {
      abrel_pred (se: Genv.symtbl):> Ks -> mem * Kf -> Prop;
      (** the names of the static variables being abstracted *)
      abrel_footprint : list (ident * Z);

      (** the abstraction relation is not affected by other variables *)
      abrel_invar: forall se ks kf m m',
        abrel_pred se ks (m, kf) ->
        Mem.unchanged_on (locsp se abrel_footprint) m m' ->
        abrel_pred se ks (m', kf);
      (** the abstraction relation only focuses on valid blocks, i.e. those have
    been allocated *)
      abrel_valid: forall se ks kf m b ofs,
        abrel_pred se ks (m, kf) ->
        (locsp se abrel_footprint) b ofs ->
        Mem.valid_block m b;
      abrel_perm: forall se ks kf m b ofs,
        abrel_pred se ks (m, kf) ->
        (locsp se abrel_footprint) b ofs ->
        Mem.perm m b ofs Max Nonempty;
    }.
Arguments abrel: clear implicits.

Local Obligation Tactic := cbn.

Program Definition abrel_comp {Ks Kn Kf} (R: abrel Ks Kn) (S: abrel Kn Kf) :=
  {|
    abrel_pred (se: Genv.symtbl) ks '(m, kf) :=
      exists kn, R se ks (m, kn) /\ S se kn (m, kf);
    abrel_footprint := abrel_footprint R ++ abrel_footprint S;
  |}.
Next Obligation.
  intros * (kn & HR & HS) H. exists kn. split.
  - eapply abrel_invar; eauto.
    eapply Mem.unchanged_on_implies; eauto.
    intros. rewrite locsp_app. now left.
  - eapply abrel_invar; eauto.
    eapply Mem.unchanged_on_implies; eauto.
    intros. rewrite locsp_app. now right.
Qed.
Next Obligation.
  intros * (kn & HR & HS). rewrite locsp_app.
  intros [|].
  eapply abrel_valid. exact HR. eauto.
  eapply abrel_valid. exact HS. eauto.
Qed.
Next Obligation.
  intros * (kn & HR & HS). rewrite locsp_app.
  intros [|].
  eapply abrel_perm. exact HR. eauto.
  eapply abrel_perm. exact HS. eauto.
Qed.

Program Definition abrel_tens {Ks1 Ks2 Kf1 Kf2} (R1: abrel Ks1 Kf1) (R2: abrel Ks2 Kf2) :
  abrel (Ks1 * Ks2) (Kf1 * Kf2) :=
  {|
    abrel_pred (se: Genv.symtbl) '(ks1, ks2) '(m, (kf1, kf2)) :=
      R1 se ks1 (m, kf1) /\ R2 se ks2 (m, kf2);
    abrel_footprint := abrel_footprint R1 ++ abrel_footprint R2;
  |}.
Next Obligation.
  intros until se. intros [ks1 ks2] [kf1 kf2] *.
  intros [H1 H2] H. split.
  - eapply abrel_invar; eauto.
    eapply Mem.unchanged_on_implies; eauto.
    intros. rewrite locsp_app. now left.
  - eapply abrel_invar; eauto.
    eapply Mem.unchanged_on_implies; eauto.
    intros. rewrite locsp_app. now right.
Qed.
Next Obligation.
  intros until se. intros [ks1 ks2] [kf1 kf2] *.
  rewrite locsp_app. intros [H1 H2] [H|H].
  eapply abrel_valid. exact H1. eauto.
  eapply abrel_valid. exact H2. eauto.
Qed.
Next Obligation.
  intros until se. intros [ks1 ks2] [kf1 kf2] *.
  rewrite locsp_app. intros [H1 H2] [H|H].
  eapply abrel_perm. exact H1. eauto.
  eapply abrel_perm. exact H2. eauto.
Qed.

Lemma mext_unchanged_on ms mf k p
      (MEXT: Mem.extends ms mf)
      (MEQ: forall b ofs, Mem.perm ms b ofs Cur Readable ->
                     ZMap.get ofs (PMap.get b ms.(Mem.mem_contents)) =
                       ZMap.get ofs (PMap.get b mf.(Mem.mem_contents))):
  Mem.unchanged_on (fun b ofs => Mem.perm ms b ofs k p) ms mf.
Proof.
  constructor.
  - erewrite Mem.mext_next. reflexivity. exact MEXT.
  - intros * HB HV. split; intros HP.
    + eapply Mem.perm_extends; eauto.
    + exploit Mem.perm_extends_inv; eauto.
      intros [A|A].
      * exact A.
      * exfalso. apply A. eauto with mem.
  - intros. symmetry. eapply MEQ. eauto.
Qed.

Section ABREL_CC.

  Context {Ks Kf} (R: abrel Ks Kf).

  Inductive abrel_world :=
  | mk_aw : Genv.symtbl -> mem -> mem -> abrel_world.
  Inductive abrel_cc_query: abrel_world -> query (li_c @ Ks) -> query (li_c @ Kf) -> Prop :=
    abrel_cc_query_intro se ms mf vfs vff sg vargss vargsf ks kf
      (VF: Val.inject inject_id vfs vff)
      (VARGS: Val.inject_list inject_id vargss vargsf)
      (VDEF: vfs <> Vundef)
      (MEXT: Mem.extends ms mf)
      (MPERM: forall b ofs, locsp se (abrel_footprint R) b ofs -> loc_out_of_bounds ms b ofs)
      (MEQ: forall b ofs, Mem.perm ms b ofs Cur Readable ->
                     ZMap.get ofs (PMap.get b ms.(Mem.mem_contents)) =
                       ZMap.get ofs (PMap.get b mf.(Mem.mem_contents)))
      (ABS: R se ks (mf, kf)):
      abrel_cc_query (mk_aw se ms mf) (cq vfs sg vargss ms, ks) (cq vff sg vargsf mf, kf).
  Inductive abrel_cc_reply: abrel_world -> reply (li_c @ Ks) -> reply (li_c @ Kf) -> Prop :=
    abrel_cc_reply_intro se vress ms vresf mf ks kf
      (VRES: Val.inject inject_id vress vresf)
      (MEXT: Mem.extends ms mf)
      (MPERM: forall b ofs, locsp se (abrel_footprint R) b ofs -> loc_out_of_bounds ms b ofs)
      (MEQ: forall b ofs, Mem.perm ms b ofs Cur Readable ->
                     ZMap.get ofs (PMap.get b ms.(Mem.mem_contents)) =
                       ZMap.get ofs (PMap.get b mf.(Mem.mem_contents)))
      (ABS: R se ks (mf, kf)):
      abrel_cc_reply (mk_aw se ms mf) (cr vress ms, ks) (cr vresf mf, kf).
  Instance abrel_cc_kf: KripkeFrame unit abrel_world :=
    {| acc _ '(mk_aw se ms mf) '(mk_aw se' _ mf') :=
      let P b ofs := loc_out_of_bounds ms b ofs
                     /\ ~ locsp se (abrel_footprint R) b ofs
      in Mem.unchanged_on P mf mf' /\ se = se'; |}.

  Lemma abrel_cc_query_unchanged_on se ms mf qks qkf k p:
    abrel_cc_query (mk_aw se ms mf) qks qkf ->
    Mem.unchanged_on (fun b ofs => Mem.perm ms b ofs k p) ms mf.
  Proof. inversion 1. eapply mext_unchanged_on; eauto. Qed.

  Lemma abrel_cc_reply_unchanged_on se ms mf qks qkf k p:
    abrel_cc_reply (mk_aw se ms mf) qks qkf ->
    Mem.unchanged_on (fun b ofs => Mem.perm ms b ofs k p) ms mf.
  Proof. inversion 1. eapply mext_unchanged_on; eauto. Qed.

  Program Definition abrel_cc: callconv (li_c @ Ks) (li_c @ Kf) :=
    {|
      ccworld := abrel_world;
      match_senv '(mk_aw se _ _) := fun se1 se2 => se = se1 /\ se = se2;
      match_query := abrel_cc_query;
      match_reply := (klr_diam tt) abrel_cc_reply;
    |}.
  Next Obligation.
    intros *. destruct w. intros [-> ->]. easy.
  Qed.
  Next Obligation.
    intros *. destruct w. intros [-> ->]. easy.
  Qed.
  Next Obligation.
    intros * Hse * Hq. destruct w. destruct Hse; subst.
    inv Hq. cbn. apply val_inject_id in VF. inv VF; easy.
  Qed.
  Next Obligation.
    intros w [qs ks] [qf kf] Hq.
    inv Hq. cbn. apply val_inject_id in VF. inv VF; easy.
  Qed.
End ABREL_CC.

Lemma unchanged_on_union P Q m1 m2:
  Mem.unchanged_on P m1 m2 ->
  Mem.unchanged_on Q m1 m2 ->
  Mem.unchanged_on (fun b ofs => P b ofs \/ Q b ofs) m1 m2.
Proof.
  intros HP HQ. constructor.
  - rewrite Mem.unchanged_on_nextblock. reflexivity. eauto.
  - intros * [A|A] Hv.
    eapply Mem.unchanged_on_perm. apply HP. all: eauto.
    eapply Mem.unchanged_on_perm. apply HQ. all: eauto.
  - intros * [A|A] Hp.
    eapply Mem.unchanged_on_contents. apply HP. all: eauto.
    eapply Mem.unchanged_on_contents. apply HQ. all: eauto.
Qed.

Lemma loc_out_of_bounds_dec m b ofs:
  {loc_out_of_bounds m b ofs} + {~ loc_out_of_bounds m b ofs}.
Proof.
  unfold loc_out_of_bounds.
  edestruct Mem.perm_dec.
  - right. intros X. apply X. apply p.
  - left. apply n.
Qed.

Definition disjoint_abrel {K1 K2 K3 K4} (R: abrel K1 K2) (S: abrel K3 K4) : Prop :=
  forall se b ofs, locsp se (abrel_footprint R) b ofs -> locsp se (abrel_footprint S) b ofs -> False.


Lemma krel_comp_ref {Ks Kn Kf} (R: abrel Ks Kn) (S: abrel Kn Kf):
  disjoint_abrel R S ->
  ccref (abrel_cc (abrel_comp R S)) (abrel_cc R @ abrel_cc S)%cc.
Proof.
  intros disj.
  intros w. destruct w as [se ms mf].
  intros se1 se2 (qs & ks) (qf & kf) Hse Hq.
  inv Hse. inv Hq.
  set (mn := unchecked_free_list mf (locs se2 (abrel_footprint S))).
  exists (se2, mk_aw se2 ms mn, mk_aw se2 mn mf).
  repeat apply conj. split; easy.
  destruct ABS as (kn & HR & HS).
  - exists ((cq vfs sg vargss mn), kn). split.
    + constructor; eauto.
      * apply val_inject_id. apply Val.lessdef_refl.
      * clear. induction vargss.
        -- constructor.
        -- constructor. apply val_inject_id. apply Val.lessdef_refl.
           assumption.
      * eapply unchecked_free_list_right_extends; eauto.
        subst mn. reflexivity.
        intros. eapply MPERM.
        cbn. rewrite locsp_app. right. apply locs_iff.
        exists (b, lo, hi). split; eauto.
        eauto with mem.
      * intros. apply MPERM.
        cbn. rewrite locsp_app. now left.
      * intros * HP. erewrite MEQ; eauto.
        exploit unchecked_free_list_unchanged_on.
        instantiate (1 := mn). subst mn. reflexivity.
        instantiate (1 := fun b ofs => Mem.perm ms b ofs Max Nonempty).
        intros. cbn. eapply MPERM.
        cbn. rewrite locsp_app. right.
        apply locs_iff. exists (b0, lo, hi). repeat apply conj; eauto.
        intros X. exploit Mem.unchanged_on_contents. apply X.
        3: intros A; symmetry; apply A.
        cbn. eauto with mem.
        eapply Mem.perm_extends; eauto with mem.
      * eapply abrel_invar; eauto.
        exploit unchecked_free_list_unchanged_on.
        instantiate (1 := mn). subst mn. reflexivity.
        instantiate (1 := fun b ofs => locsp se2 (abrel_footprint R) b ofs).
        intros. intros X. unfold disjoint_abrel in disj.
        eapply disj. exact X. apply locs_iff.
        exists (b, lo, hi). split; eauto.
        intros X. exact X.
    + constructor; eauto.
      * eapply unchecked_free_list_left_extends.
        apply Mem.extends_refl. subst mn. reflexivity.
      * intros * XS X.
        eapply locs_iff in XS.
        destruct XS as ([[bi lo] hi] & A & B & C). subst.
        eapply perm_unchecked_free_list_2; eauto. all: omega.
      * intros * HP.
        exploit unchecked_free_list_unchanged_on.
        instantiate (1 := mn). subst mn. reflexivity.
        instantiate (1 := fun b ofs => Mem.perm mn b ofs Cur Readable).
        intros. intros X.
        eapply perm_unchecked_free_list_2; eauto.
        intros H. exploit Mem.unchanged_on_contents. apply H.
        apply HP.
        eapply perm_unchecked_free_list_3; eauto.
        easy.
  - intros (rs & ks') (rf & kf') ([rn kn'] & Hr1 & Hr2).
    destruct Hr1 as (w1 & Hw1 & Hr1).
    destruct Hr2 as (w2 & Hw2 & Hr2).
    destruct w1 as [x ms' mn']. destruct w2 as [y mn'' mf'].
    inv Hr1. inv Hr2.
    destruct Hw1 as [Hw1 <-]. destruct Hw2 as [Hw2 <-].
    exists (mk_aw se2 ms' mf'). split.
    + cbn. split. 2: reflexivity.
      assert
        (A: Mem.unchanged_on
              (fun (b : block) (ofs : Z) =>
                 loc_out_of_bounds ms b ofs
                 /\ ~ loc_out_of_bounds mn b ofs
                 /\ ~ locsp se2 (abrel_footprint R) b ofs) mf mf').
      {
        eapply Mem.unchanged_on_trans.
        2: eapply Mem.unchanged_on_trans.
        - instantiate (1 := mn).
          eapply Mem.unchanged_on_implies.
          eapply unchecked_free_list_unchanged_on.
          subst mn. reflexivity.
          instantiate (1 := fun b ofs => ~ loc_out_of_bounds mn b ofs).
          intros * A B C. cbn.
          intros X. apply X. clear X. intros X.
          eapply perm_unchecked_free_list_2; eauto.
          intros * (A & B & C) V. exact B.
        - eapply Mem.unchanged_on_implies. exact Hw1.
          intros * (A & B & C) V. split; eauto.
        - exploit mext_unchanged_on. exact MEXT1. exact MEQ1.
          intros X. eapply Mem.unchanged_on_implies. exact X.
          intros * (A & B & C) V.
          exploit Mem.unchanged_on_perm. exact Hw1.
          cbn. split; eauto.
          eapply Mem.perm_valid_block.
          apply Classical_Prop.NNPP. exact B.
          intros Y. apply Y.
          apply Classical_Prop.NNPP. exact B.
      }
      exploit unchanged_on_union. exact Hw2. exact A. clear Hw2. clear A.
      intros A. eapply Mem.unchanged_on_implies. apply A.
      intros * (Hperm & HRS) V.
      destruct (loc_out_of_bounds_dec mn b ofs).
      * left. split; eauto.
        intros X. apply HRS. rewrite locsp_app. now right.
      * right. repeat apply conj; eauto.
        intros X. apply HRS. rewrite locsp_app. now left.
    + constructor.
      * rewrite <- val_inject_lessdef in *.
        eapply Val.lessdef_trans; eauto.
      * eapply Mem.extends_extends_compose; eauto.
      * intros *. cbn. rewrite locsp_app.
        intros [A|A].
        -- apply MPERM0. exact A.
        -- intros B. exploit MPERM1. apply A.
           eapply Mem.perm_extends; eauto. easy.
      * intros * HP.
        erewrite <- MEQ1. eapply MEQ0. exact HP.
        eapply Mem.perm_extends; eauto.
      * exists kn'. split; eauto.
        exploit mext_unchanged_on. exact MEXT1. exact MEQ1. intros X.
        eapply abrel_invar. exact ABS0.
        eapply Mem.unchanged_on_implies. exact X.
        intros * HR V. cbn. eapply abrel_perm. exact ABS0. exact HR.
Qed.

Module KCC.

  Section CKLR.

    Context {K1 K2} (R: @krel' K2 K1).

    Inductive kworld := kw (se: Genv.symtbl) (k1: K1) (k2: K2).

    Inductive krel_mm : kworld -> mem -> mem -> Prop :=
      match_intro: forall se k1 k2 m1 m2,
          Mem.extends m1 m2 -> krel_pred R se k1 (m2, k2) ->
          (* The source program would crash if it tries to manipulate data on blocks
   defined in the footprint *)
          no_perm_on m1 (blocks se (krel_footprint R)) ->
          krel_mm (kw se k1 k2) m1 m2.
    Inductive krel_match_se: kworld -> Genv.symtbl -> Genv.symtbl -> Prop :=
      match_se_intro: forall se k1 k2, krel_match_se (kw se k1 k2) se se.

    Program Definition krel_cklr: cklr :=
      {|
        world := kworld;
        wacc := eq;
        mi w := inject_id;
        match_mem := krel_mm;
        match_stbls := krel_match_se;
      |}.
    (* mi_acc *)
    Next Obligation. repeat rstep. apply inject_incr_refl. Qed.
    (* match_stbls_acc *)
    Next Obligation. rauto. Qed.
    (* match_stbls_proj *)
    Next Obligation.
      intros se1 se2 Hse. inv Hse. apply Genv.match_stbls_id.
    Qed.
    (* match_stbls_nextblock *)
    Next Obligation.
      inv H. inv H0. erewrite <- Mem.mext_next; eauto.
    Qed.
    (* cklr_alloc *)
    Next Obligation.
      intros [ ] m1 m2 Hm lo hi. inv Hm.
      destruct (Mem.alloc m1 lo hi) as [m1' b1] eqn: Hm1.
      edestruct Mem.alloc_extends as (m2' & Hm2' & Hm'); eauto; try reflexivity.
      rewrite Hm2'.
      eexists; split; repeat rstep.
      constructor; auto.
      - eapply krel_invar; eauto.
        eapply Mem.alloc_unchanged_on; eauto.
      - unfold no_perm_on in *. intros.
        specialize (H6 _ _ H). intros Hp. apply H6.
        eapply Mem.perm_alloc_4 in Hp; eauto.
        eapply Mem.alloc_result in Hm1. subst.
        eapply krel_valid in H5; eauto.
        erewrite Mem.mext_next; eauto.
    Qed.
    (* cklr_free *)
    Next Obligation.
      intros [ ] m1 m2 Hm [[b lo] hi] r2 Hr. inv Hm.
      apply coreflexivity in Hr. subst. simpl. red.
      destruct (Mem.free m1 b lo hi) as [m1'|] eqn:Hm1'; [|constructor].
      edestruct Mem.free_parallel_extends as (m2' & Hm2' & Hm'); eauto.
      rewrite Hm2'. constructor.
      eexists; split; repeat rstep.
      constructor; auto.
      - eapply krel_invar; eauto.
        eapply Mem.free_unchanged_on; eauto.
        intros ofs Hofs Hv. specialize (H6 _ _ Hv). apply H6.
        exploit Mem.free_range_perm. apply Hm1'. eauto.
        intros Hp. eapply Mem.perm_cur_max.
        eapply Mem.perm_implies. apply Hp. constructor.
      - unfold no_perm_on in *. intros.
        specialize (H6 _ _ H). intros Hp. apply H6.
        eapply Mem.perm_free_3; eauto.
    Qed.
    (* cklr_load *)
    Next Obligation.
      intros [ ] chunk m1 m2 Hm [b ofs] p2 Hp. inv Hm.
      apply coreflexivity in Hp; subst. simpl. red.
      destruct (Mem.load chunk m1 b ofs) as [v1|] eqn:Hv1; [|constructor].
      edestruct Mem.load_extends as (v2 & Hv2 & Hv); eauto.
      rewrite Hv2. rewrite val_inject_lessdef_eqrel. rauto.
    Qed.
    (* cklr_store *)
    Next Obligation.
      intros [ ] chunk m1 m2 Hm [b ofs] p2 Hp v1 v2 Hv. inv Hm.
      apply coreflexivity in Hp; subst. simpl. red.
      destruct (Mem.store chunk m1 b ofs v1) as [m1'|] eqn:Hm1'; [|constructor].
      apply val_inject_lessdef in Hv.
      edestruct Mem.store_within_extends as (m2' & Hm2' & Hm'); eauto.
      rewrite Hm2'. constructor.
      eexists _; split; repeat rstep.
      constructor; auto.
      - eapply krel_invar; eauto.
        eapply Mem.store_unchanged_on; eauto.
        intros ofs' Hofs. intros Hp. specialize (H6 _ _ Hp). apply H6.
        exploit Mem.store_valid_access_3. apply Hm1'.
        unfold Mem.valid_access. intros [Hpr ?]. specialize (Hpr _ Hofs).
        eapply Mem.perm_cur_max. eapply Mem.perm_implies. apply Hpr. constructor.
      - unfold no_perm_on in *. intros.
        specialize (H6 _ _ H). intros Hp. apply H6.
        eapply Mem.perm_store_2; eauto.
    Qed.
    (* cklr_loadbytes *)
    Next Obligation.
      intros [ ] m1 m2 Hm [b ofs] p2 Hp sz. inv Hm.
      apply coreflexivity in Hp; subst. simpl. red.
      destruct (Mem.loadbytes m1 b ofs sz) as [v1|] eqn:Hv1; [|constructor].
      edestruct Mem.loadbytes_extends as (v2 & Hv2 & Hv); eauto.
      rewrite Hv2. rauto.
    Qed.
    (* cklr_storebytes *)
    Next Obligation.
      intros [ ] m1 m2 Hm [b1 ofs1] p2 Hp vs1 vs2 Hv. inv Hm.
      apply coreflexivity in Hp. subst. simpl. red.
      destruct (Mem.storebytes m1 b1 ofs1 vs1) as [m1'|] eqn:Hm1'; [|constructor].
      edestruct Mem.storebytes_within_extends as (m2' & Hm2' & Hm'); eauto.
      eapply list_rel_forall2. apply Hv.
      rewrite Hm2'. constructor.
      eexists _; split; repeat rstep.
      constructor; auto.
      - eapply krel_invar; eauto.
        eapply Mem.storebytes_unchanged_on; eauto.
        intros ofs' Hofs. intros Hp. specialize (H6 _ _ Hp). apply H6.
        exploit Mem.storebytes_range_perm. apply Hm1'.
        rewrite length_rel; eauto. intros.
        eapply Mem.perm_cur_max. eapply Mem.perm_implies; eauto. constructor.
      - unfold no_perm_on in *. intros.
        specialize (H6 _ _ H). intros Hp. apply H6.
        eapply Mem.perm_storebytes_2; eauto.
    Qed.
    (* cklr_perm *)
    Next Obligation.
      intros [ ] m1 m2 Hm [b1 ofs1] p2 Hp p' ? H. inv Hm.
      apply coreflexivity in Hp. subst. simpl in *.
      eapply Mem.perm_extends; eauto.
    Qed.
    (* cklr_valid_block *)
    Next Obligation.
      intros [ ] m1 m2 Hm b1 b2 Hb. inv Hm.
      apply coreflexivity in Hb. subst.
      apply Mem.valid_block_extends; eauto.
    Qed.
    (* cklr_no_overlap *)
    Next Obligation.
      intros b1 b1' delta1 b2 b2' delta2 ofs1 ofs2 Hb Hb1' Hb2' Hp1 Hp2. inv H.
      inv Hb1'. inv Hb2'. eauto.
    Qed.
    (* cklr_representable *)
    Next Obligation. xomega. Qed.
    (* cklr_aligned_area_inject *)
    Next Obligation. rewrite Z.add_0_r. assumption. Qed.
    (* cklr_disjoint_or_equal_inject *)
    Next Obligation. intuition xomega. Qed.
    (* cklr_perm_inv *)
    Next Obligation.
      inv H0. unfold inject_id in *. inv H3.
      replace (ofs1 + 0) with ofs1 in *; try omega.
      inv H. eapply Mem.perm_extends_inv; eauto.
    Qed.
    (* cklr_nextblock_incr *)
    Next Obligation.
      destruct H0 as (w' & Hw' & H'). inv Hw'.
      inv H. inv H'.
      apply Mem.mext_next in H0.
      apply Mem.mext_next in H5.
      rewrite H0. rewrite H5. reflexivity.
    Qed.

  End CKLR.

End KCC.

Section SIMULATION.
  Context {K1 K2} (R: @krel' K2 K1).

  Lemma cont_match_mr w w' k1 k2:
    cont_match (KCC.krel_cklr R) w k1 k2 ->
    cont_match (KCC.krel_cklr R) w' k1 k2.
  Proof.
    induction 1; try constructor; auto.
  Qed.

  Lemma clight_sim p: forward_simulation (krel_kcc R) (krel_kcc R) (semantics2 p @ K1) (semantics2 p @ K2).
  Proof.
    constructor. econstructor; eauto. intros i. reflexivity.
    instantiate (1 := fun _ _ _ => _). cbn beta.
    intros ? se w Hse Hse1. inv Hse. cbn -[semantics2] in *.
    pose (ms := fun '(s1, k1) '(s2, k2) =>
                  Clightrel.state_match (KCC.krel_cklr R) (KCC.kw se k1 k2) s1 s2).
    apply forward_simulation_step with (match_states := ms).
    - intros [q1 k1] [q2 k2] [s1 k1'] Hq Hs1. inv Hq. inv Hs1.
      cbn in *. subst k1'. inv H. cbn in *.
      exists (Callstate vf2 vargs2 Kstop m2, k2). split.
      + constructor; auto. cbn.
        econstructor; eauto.
        * unfold globalenv. cbn.
          exploit (@find_funct_inject p (KCC.krel_cklr R) (KCC.kw se k1 k2) (globalenv se p)).
          split; cbn; eauto.
          eapply (rel_push_rintro (fun se => globalenv se p) (fun se => globalenv se p)).
          constructor. eauto. intro Hx. apply Hx.
        * eapply val_casted_list_inject; eauto.
        * simpl. eapply match_stbls_nextblock; eauto.
          instantiate (2 := KCC.krel_cklr R). instantiate (1 := KCC.kw se k1 k2).
          constructor. constructor; auto.
      + constructor; auto. cbn.
        apply list_inject_subrel'.
        auto. constructor. constructor; auto.
    - intros [s1 k1] [s2 k2] [r1 k1'] Hs Hfinal.
      inv Hfinal. cbn in *. subst k1'. inv H. inv Hs. inv H5.
      eexists (_, k2). split. split; cbn; auto.
      + inv H4. econstructor.
      + constructor; cbn; auto.
    - intros [s1 k1] [s2 k2] [q1 k1'] Hs Hext.
      inv Hext. cbn in *. subst k1'. inv H. inv Hs. inv H8.
      eexists se, (_, _). repeat apply conj; cbn; eauto.
      + cbn. econstructor.
        exploit (@find_funct_inject p (KCC.krel_cklr R) (KCC.kw se k1 k2) (globalenv se p)).
        split; cbn; eauto.
        eapply (rel_push_rintro (fun se => globalenv se p) (fun se => globalenv se p)).
        constructor. eauto. intros Hx. subst f. apply Hx.
      + constructor; cbn; auto.
        eapply list_inject_subrel. auto.
        destruct vf; cbn in *; congruence.
      + intros [r1 kr1] [r2 kr2] [s1' k1'] Hr [Hafter H].
        inv Hafter. cbn in *. subst k1'. inv Hr. inv H.
        cbn in *. eexists (_, kr2). split. split; auto.
        cbn. econstructor.
        constructor; auto. eapply cont_match_mr. eauto.
        constructor; auto.
    - intros [s1 k1] t [s1' k1'] Hstep [s2 k2] Hs.
      inv Hstep. cbn in H.
      exploit step2_rel; eauto. unfold genv_match.
      eapply (rel_push_rintro (fun se => globalenv se p) (fun se => globalenv se p)).
      constructor. intros (s2' & Hstep' & w' & Hw' & Hs').
      exists (s2', k2). inv Hw'. split; auto.
      constructor. apply Hstep'. reflexivity.
    - apply well_founded_ltof.
  Qed.

End SIMULATION.

Lemma clight_krel {K1 K2} (R: krel K2 K1) p:
  forward_simulation R R (Clight.semantics2 p @ K1) (Clight.semantics2 p @ K2).
Proof.
  induction R; simpl.
  - apply clight_sim.
  - eapply compose_forward_simulations; eauto.
Qed.

Require Import SmallstepLinking.
Require Import compcertox.CModule.

Lemma cmodule_krel {K1 K2} (R: @krel K2 K1) M sk:
  skel_module_compatible M sk ->
  forward_simulation R R (semantics M sk @ K1) (semantics M sk @ K2).
Proof.
  intros Hsk.

  eapply open_fsim_ccref. apply cc_compose_id_left.
  unfold flip. apply cc_compose_id_left.
  eapply compose_forward_simulations.
  apply lift_horizontal_comp1.

  eapply open_fsim_ccref. apply cc_compose_id_right.
  unfold flip. apply cc_compose_id_right.
  eapply compose_forward_simulations.
  2: { apply lift_horizontal_comp2. }

  apply semantics_simulation'.
  - intros. induction M as [| p ps]; try easy.
    destruct i.
    + cbn. apply clight_krel.
    + apply IHps.
      unfold skel_module_compatible in *.
      rewrite -> Forall_forall in *.
      intros x Hx. apply Hsk. right. auto.
  - intros. induction M as [| p ps]; try easy.
    destruct i.
    + cbn. unfold skel_module_compatible in *.
      rewrite -> Forall_forall in *. apply Hsk.
      left. auto.
    + apply IHps.
      unfold skel_module_compatible in *.
      rewrite -> Forall_forall in *.
      intros x Hx. apply Hsk. right. auto.
Qed.

(* Code not used *)

Unset Asymmetric Patterns.

Inductive abrel: Type -> Type -> Type :=
| abrel_singleton {Ks Kf} : abrel' Ks Kf -> abrel Ks Kf
| abrel_compose {Ks Kn Kf} : abrel Ks Kn -> abrel Kn Kf -> abrel Ks Kf.

Program Definition abrel_id' {K}: abrel' K K :=
  {|
    abrel_pred se _ _ := True;
    abrel_footprint _ := False;
  |}.
Next Obligation. firstorder. Qed.

Definition abrel_id {K} := abrel_singleton (@abrel_id' K).

Program Definition abrel_tens' {Ks1 Ks2 Kf1 Kf2}
        (R1: abrel' Ks1 Kf1) (R2: abrel' Ks2 Kf2) : abrel' (Ks1 * Ks2) (Kf1 * Kf2) :=
  {|
    abrel_pred se '(ks1, ks2) '(m, (kf1, kf2)) :=
    abrel_pred R1 se ks1 (m, kf1) /\ abrel_pred R2 se ks2 (m, kf2);
    abrel_footprint i := abrel_footprint R1 i \/ abrel_footprint R2 i;
  |}.
Next Obligation.
  split; eapply abrel_invar; eauto; eapply Mem.unchanged_on_implies; eauto;
    intros; unfold blocks in *; cbn in *.
  - destruct H2 as [? [? ?]]. eexists; split; eauto.
  - destruct H2 as [? [? ?]]. eexists; split; eauto.
Qed.
Next Obligation.
  destruct H0 as [v [Hv Hb]].
  destruct Hv as [Hv|Hv]; [ eapply (abrel_valid R1) | eapply (abrel_valid R2) ]; eauto.
  - eexists; split; eauto.
  - eexists; split; eauto.
    Unshelve. exact ofs. exact ofs.
Qed.

Fixpoint abrel_lift_l {Ks Kf} (R: abrel Ks Kf) K : abrel (K*Ks) (K*Kf) :=
  match R with
  | abrel_singleton R' => abrel_singleton (abrel_tens' abrel_id' R')
  | abrel_compose R1 R2 => abrel_compose (abrel_lift_l R1 K) (abrel_lift_l R2 K)
  end.

Fixpoint abrel_lift_r {Ks Kf} (R: abrel Ks Kf) K : abrel (Ks*K) (Kf*K) :=
  match R with
  | abrel_singleton R' => abrel_singleton (abrel_tens' R' abrel_id')
  | abrel_compose R1 R2 => abrel_compose (abrel_lift_r R1 K) (abrel_lift_r R2 K)
  end.

Definition abrel_tens {Ks1 Ks2 Kf1 Kf2}
           (R1: abrel Ks1 Kf1) (R2: abrel Ks2 Kf2) : abrel (Ks1 * Ks2) (Kf1 * Kf2) :=
  abrel_compose (abrel_lift_r R1 Ks2) (abrel_lift_l R2 Kf1).

Inductive abrel_world :=
| mk_aw : Genv.symtbl -> mem -> mem -> abrel_world.

Section ABREL_CC.

  Context {Ks Kf} (R: abrel' Ks Kf).

  Inductive abrel_cc_query: abrel_world -> query (li_c @ Ks) -> query (li_c @ Kf) -> Prop :=
    abrel_cc_query_intro se ms mf vfs vff sg vargss vargsf ks kf:
      Val.inject inject_id vfs vff -> Val.inject_list inject_id vargss vargsf ->
      Mem.extends ms mf -> vfs <> Vundef -> no_perm_on ms (blocks se (abrel_footprint R)) ->
      abrel_pred R se ks (mf, kf) ->
      abrel_cc_query (mk_aw se ms mf) (cq vfs sg vargss ms, ks) (cq vff sg vargsf mf, kf).
  Inductive abrel_cc_reply: abrel_world -> reply (li_c @ Ks) -> reply (li_c @ Kf) -> Prop :=
    abrel_cc_reply_intro se vress ms vresf mf ks kf:
      Val.inject inject_id vress vresf ->
      Mem.extends ms mf -> no_perm_on ms (blocks se (abrel_footprint R)) ->
      abrel_pred R se ks (mf, kf) ->
      abrel_cc_reply (mk_aw se ms mf) (cr vress ms, ks) (cr vresf mf, kf).
  Instance abrel_cc_kf: KripkeFrame unit abrel_world :=
    {| acc _ '(mk_aw se ms mf) '(mk_aw _ _ mf') :=
      let P b ofs := loc_out_of_bounds ms b ofs /\ ~ blocks se (abrel_footprint R) b ofs
      in Mem.unchanged_on P mf mf'; |}.

  Program Definition abrel_cc': callconv (li_c @ Ks) (li_c @ Kf) :=
    {|
      ccworld := abrel_world;
      match_senv '(mk_aw se _ _) := fun se1 se2 => se = se1 /\ se = se2;
      match_query := abrel_cc_query;
      match_reply := (klr_diam tt) abrel_cc_reply;
    |}.
  Next Obligation.
    destruct w. destruct H; subst. reflexivity.
  Qed.
  Next Obligation.
    destruct w. destruct H; subst. reflexivity.
  Qed.
  Next Obligation.
    destruct w. destruct H; subst.
    inv H0. cbn. apply val_inject_id in H7. inv H7; easy.
  Qed.
  Next Obligation.
    destruct w.
    inv H; cbn. apply val_inject_id in H7. inv H7; easy.
  Qed.

End ABREL_CC.

Fixpoint abrel_cc {Ks Kf} (R: abrel Ks Kf): callconv (li_c @ Ks) (li_c @ Kf) :=
  match R with
  | abrel_singleton R' => abrel_cc' R'
  | abrel_compose R1 R2 => (abrel_cc R1) @ (abrel_cc R2)
  end.

(* A special form of simulation convention with explicit invariant on the world
   instead of using the Kriple frames. *)
Record invcc {li1 li2} :=
  mk_invcc {
    iworld: Type;
    world_invariant: iworld -> iworld -> Prop;
    imatch_senv: iworld -> Genv.symtbl -> Genv.symtbl -> Prop;
    imatch_query: iworld -> query li1 -> query li2 -> Prop;
    imatch_reply: iworld -> reply li1 -> reply li2 -> Prop;

    imatch_senv_public_preserved:
      forall w se1 se2,
        imatch_senv w se1 se2 ->
        forall id, Genv.public_symbol se2 id = Genv.public_symbol se1 id;
    imatch_senv_valid_for:
      forall w se1 se2 sk,
        imatch_senv w se1 se2 ->
        Genv.valid_for sk se1 <->
        Genv.valid_for sk se2;
    imatch_senv_symbol_address:
      forall w se1 se2, imatch_senv w se1 se2 ->
      forall q1 q2, imatch_query w q1 q2 ->
      forall i, Genv.symbol_address se1 i Ptrofs.zero = entry q1 <->
      Genv.symbol_address se2 i Ptrofs.zero = entry q2;
    imatch_query_defined:
      forall w q1 q2,
      imatch_query w q1 q2 ->
      entry q1 <> Vundef <-> entry q2 <> Vundef;
    }.

Arguments invcc: clear implicits.

Instance invcc_kf {li1 li2} (icc: invcc li1 li2): KripkeFrame unit (iworld icc) :=
  {| acc _ := world_invariant icc |}.

Program Definition invcc_cc {li1 li2} (icc: invcc li1 li2) : callconv li1 li2 :=
  {|
    ccworld := iworld icc;
    match_senv := imatch_senv icc;
    match_query := imatch_query icc;
    match_reply := (klr_diam tt) (imatch_reply icc);
  |}.
Next Obligation. eapply imatch_senv_public_preserved; eauto. Qed.
Next Obligation. eapply imatch_senv_valid_for; eauto. Qed.
Next Obligation. eapply imatch_senv_symbol_address; eauto. Qed.
Next Obligation. eapply imatch_query_defined; eauto. Qed.

Program Definition cc_invcc {li1 li2} (cc: callconv li1 li2) : invcc li1 li2 :=
  {|
    iworld := ccworld cc;
    world_invariant _ _ := True;
    imatch_senv := match_senv cc;
    imatch_query := match_query cc;
    imatch_reply := match_reply cc;
  |}.
Next Obligation. eapply match_senv_public_preserved; eauto. Qed.
Next Obligation. eapply match_senv_valid_for; eauto. Qed.
Next Obligation. eapply match_senv_symbol_address; eauto. Qed.
Next Obligation. eapply match_query_defined; eauto. Qed.

(* inverse *)
Lemma cc_invcc_inv {li1 li2} (cc: callconv li1 li2) :
  cceqv cc (invcc_cc (cc_invcc cc)).
Proof.
Admitted.

Coercion invcc_cc : invcc >-> callconv.
Coercion cc_invcc : callconv >-> invcc.

Require Import CallconvAlgebra.
Require Import Lia.

Section NATURAL.

  Context {Ks1 Ks2 Kf1 Kf2} (R1: abrel' Ks1 Kf1) (R2: abrel' Ks2 Kf2).
  Definition AR1 : abrel (Ks1 * Ks2) (Kf1 * Kf2) :=
    abrel_compose (abrel_lift_r (abrel_singleton R1) Ks2)
                  (abrel_lift_l (abrel_singleton R2) Kf1).
  Definition AR2 : abrel (Ks1 * Ks2) (Kf1 * Kf2) :=
    abrel_compose (abrel_lift_l (abrel_singleton R2) Ks1)
                  (abrel_lift_r (abrel_singleton R1) Kf2).
  Lemma tsen_natural: cceqv (abrel_cc AR1) (abrel_cc AR2).
  Proof.
    split.
    - intros w ses sef qs qf Hse Hq. exists w.
      destruct w as [[se w12] w23].
      destruct w12 as [sea ms mn].
      destruct w23 as [seb mn' mf].
      inv Hse. destruct H, H0. subst.
      destruct Hq as [qn [Hq1 Hq2]].
      inv Hq1. inv Hq2.
      repeat split.
      +
  Abort.

End NATURAL.

Record abrem {Ks Kf: Type}: Type :=
  mk_abmrel {
    abmrel_pred (se: Genv.symtbl) :> mem * Ks -> mem * Kf -> Prop;
    abmrel_footprint : list (ident * Z);

    abmrel_mext:
      forall se ks kf ms mf,
        abmrel_pred se (ms, ks) (mf, kf) ->
        Mem.extends ms mf /\ no_perm_on ms (locsp se abmrel_footprint);
    abmrel_invar:
      forall se ks kf ms mf ms' mf',
        abmrel_pred se (ms, ks) (mf, kf) ->
        Mem.unchanged_on (locsp se abmrel_footprint) mf mf' ->
        Mem.extends ms' mf' ->
        no_perm_on ms' (locsp se abmrel_footprint) ->
        abmrel_pred se (ms', ks) (mf', kf);
    abmrel_valid:
      forall se ks kf ms mf b ofs,
        abmrel_pred se (ms, ks) (mf, kf) ->
        locsp se abmrel_footprint b ofs ->
        Mem.valid_block mf b;
  }.
Arguments abmrel: clear implicits.

Program Definition abrel_ext {Ks Kf} (R: abrel Ks Kf) : abmrel Ks Kf :=
  {|
    abmrel_pred se '(ms, ks) '(mf, kf) :=
      Mem.extends ms mf /\
      no_perm_on ms (locsp se (abrel_footprint R)) /\
      R se ks (mf, kf);
    abmrel_footprint := abrel_footprint R
  |}.
Next Obligation.
  repeat apply conj; eauto.
  eapply abrel_invar; eauto.
Qed.
Next Obligation.
  eapply abrel_valid; eauto.
Qed.

Program Definition abmrel_comp {Ks Kn Kf}
        (R: abmrel Ks Kn) (S: abmrel Kn Kf) : abmrel Ks Kf :=
  {|
    abmrel_pred se mks mkf := exists mkn, R se mks mkn /\ S se mkn mkf;
    abmrel_footprint := abmrel_footprint R ++ abmrel_footprint S;
  |}.
Next Obligation.
  apply abmrel_mext in H0 as [Hm1 Hperm1].
  apply abmrel_mext in H1 as [Hm2 Hperm2].
  split.
  - eapply Mem.extends_extends_compose; eauto.
  - intros b ofs Hi Hp.
    rewrite locsp_app in Hi.
    destruct Hi as [Hi|Hi].
    + exploit Hperm1; eauto.
    + exploit Mem.perm_extends. apply Hm1. eauto. intros Hp'.
      exploit Hperm2; eauto.
Qed.

Lemma fsim_ccref {liA liB1 liB2} (cc cc': callconv liB1 liB2) L1 L2:
  forward_simulation (@cc_id liA) cc L1 L2 ->
  ccref cc' cc ->
  forward_simulation (@cc_id liA) cc' L1 L2.
Proof.
  intros. eapply open_fsim_ccref.
  reflexivity. apply H0. apply H.
Qed.

Lemma ext_unchanged m1 m2 m1' m2' P:
  Mem.extends m1 m2 ->
  Mem.unchanged_on P m2 m2' ->
  Mem.extends m1' m2' ->
  Mem.unchanged_on P m1 m1'.
Proof.
  intros E1 H E2.
  constructor.
  - rewrite (Mem.mext_next _ _ E1).
    rewrite (Mem.mext_next _ _ E2).
    eapply Mem.unchanged_on_nextblock; eauto.
  - intros. split; intros Hp.
    + eapply Mem.perm_extends in E1; eauto.
      erewrite (Mem.unchanged_on_perm _ _ _ H) in E1; eauto.
      (* add assumption *)
      admit.
      (* use E1 *)
      admit.
    + admit.
  - intros.
    Search Mem.unchanged_on.
Admitted.

Next Obligation.
  (* don't want to make those blocks freeable *)
  exists (unchecked_free_list mf' (locs se (abmrel_footprint S)), k).
  split; eauto.
  - eapply abmrel_invar; eauto.
    + eapply ext_unchanged.
  -



Program Definition abmrel_tens {Ks1 Kf1 Ks2 Kf2}
        (R1: abmrel Ks1 Kf1) (R2: abmrel Ks2 Kf2) : abmrel (Ks1 * Ks2) (Kf1 * Kf2) :=
  {|
    abmrel_pred se '(ms, (ks1, ks2)) '(mf, (kf1, kf2)) :=
      R1 se (ms, ks1) (mf, kf1) /\ R2 se (ms, ks2) (mf, kf2);
    abmrel_footprint i := abmrel_footprint R1 i \/ abmrel_footprint R2 i;
  |}.


Inductive abmrel_world :=
| mk_aw : Genv.symtbl -> mem -> mem -> abmrel_world.

Section ABREL_CC.

  Context {Ks Kf} (R: abmrel Ks Kf).

  Inductive abmrel_cc_query: abmrel_world -> query (li_c @ Ks) -> query (li_c @ Kf) -> Prop :=
    abmrel_cc_query_intro se ms mf vfs vff sg vargss vargsf ks kf:
      Val.inject inject_id vfs vff ->
      Val.inject_list inject_id vargss vargsf ->
      vfs <> Vundef ->
      R se (ms, ks) (mf, kf) ->
      abmrel_cc_query (mk_aw se ms mf) (cq vfs sg vargss ms, ks) (cq vff sg vargsf mf, kf).
  Inductive abmrel_cc_reply: abmrel_world -> reply (li_c @ Ks) -> reply (li_c @ Kf) -> Prop :=
    abmrel_cc_reply_intro se vress ms vresf mf ks kf:
      Val.inject inject_id vress vresf ->
      R se (ms, ks) (mf, kf) ->
      abmrel_cc_reply (mk_aw se ms mf) (cr vress ms, ks) (cr vresf mf, kf).
  Instance abmrel_cc_kf: KripkeFrame unit abmrel_world :=
    {| acc _ '(mk_aw se ms mf) '(mk_aw _ _ mf') :=
      let P b ofs := loc_out_of_bounds ms b ofs /\ ~ blocks se (abmrel_footprint R) b ofs
      in Mem.unchanged_on P mf mf'; |}.

  Program Definition abmrel_cc: callconv (li_c @ Ks) (li_c @ Kf) :=
    {|
      ccworld := abmrel_world;
      match_senv '(mk_aw se _ _) := fun se1 se2 => se = se1 /\ se = se2;
      match_query := abmrel_cc_query;
      match_reply := (klr_diam tt) abmrel_cc_reply;
    |}.
  Next Obligation.
    destruct w. destruct H; subst. reflexivity.
  Qed.
  Next Obligation.
    destruct w. destruct H; subst. reflexivity.
  Qed.
  Next Obligation.
    destruct w. destruct H; subst.
    inv H0. cbn. apply val_inject_id in H6. inv H6; easy.
  Qed.
  Next Obligation.
    destruct w.
    inv H; cbn. apply val_inject_id in H6. inv H6; easy.
  Qed.

End ABREL_CC.

Lemma abmrel_comp_compat {Ks Kn Kf} (R: abmrel Ks Kn) (S: abmrel Kn Kf):
  cceqv (abmrel_cc R @ abmrel_cc S) (abmrel_cc (abmrel_comp R S)).
Proof.
  apply antisymmetry.
  - intros [[se w12] w23].
    destruct w12 as [se1 ms mn].
    destruct w23 as [se2 mn' mf].
    intros * Hse Hq. cbn in Hse.
    destruct Hse. inv H. inv H0.
    destruct Hq as (q & Hq1 & Hq2).
    inv Hq1. inv Hq2.
    exists (mk_aw se3 ms mf).
    repeat apply conj.
    + constructor; reflexivity.
    + constructor; eauto.
      * rewrite val_inject_id in *.
        eapply Val.lessdef_trans; eauto.
      * admit.
      * exists (mn, kf). split; eauto.
    + intros * Hr. destruct Hr as (w' & Hw & Hr).
      inv Hr. destruct H0 as ((m & k) & Hk1 & Hk2).
      exists ((cr vresf m), k). split.
      * exists (mk_aw )
