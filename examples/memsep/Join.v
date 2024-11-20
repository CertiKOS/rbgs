From compcert Require Import
     AST Coqlib Maps Values Integers Errors Events
     LanguageInterface Smallstep Globalenvs Memory Floats.
Require Import Ctypes Cop Clight.

Local Notation "a # b" := (PMap.get b a) (at level 1).

Require Import LogicalRelations.
Require Import OptionRel.
Require Import Lia.

Section JOIN.

  Inductive contents_join: block -> Z -> mem -> mem -> mem -> Prop  :=
  | contents_join_l:
    forall m1 m2 m b ofs,
      ~Mem.perm m1 b ofs Max Nonempty ->
      (forall k p, Mem.perm m2 b ofs k p <-> Mem.perm m b ofs k p) ->
      ZMap.get ofs m1.(Mem.mem_contents)#b = Undef ->
      ZMap.get ofs m2.(Mem.mem_contents)#b =ZMap.get ofs m.(Mem.mem_contents)#b ->
      Mem.valid_block m2 b ->
      contents_join b ofs m1 m2 m
  | contents_join_r:
    forall m1 m2 m b ofs,
      ~Mem.perm m2 b ofs Max Nonempty ->
      (forall k p, Mem.perm m1 b ofs k p <-> Mem.perm m b ofs k p) ->
      ZMap.get ofs m2.(Mem.mem_contents)#b = Undef ->
      ZMap.get ofs m1.(Mem.mem_contents)#b =ZMap.get ofs m.(Mem.mem_contents)#b ->
      Mem.valid_block m1 b ->
      contents_join b ofs m1 m2 m.
  Inductive contents_join_empty: block -> Z -> mem -> mem -> mem -> Prop  :=
  | contents_join_x:
    forall m1 m2 m b ofs,
      ~Mem.perm m1 b ofs Max Nonempty ->
      ~Mem.perm m2 b ofs Max Nonempty ->
      ~Mem.perm m b ofs Max Nonempty ->
      ZMap.get ofs m1.(Mem.mem_contents)#b = Undef ->
      ZMap.get ofs m2.(Mem.mem_contents)#b = Undef ->
      ZMap.get ofs m.(Mem.mem_contents)#b = Undef ->
      ~Mem.valid_block m1 b ->
      ~Mem.valid_block m2 b ->
      contents_join_empty b ofs m1 m2 m.

  Inductive alloc_flag_join: mem -> mem -> mem -> Prop :=
  | alloc_flag_join_l:
    forall m m1 m2,
      Mem.alloc_flag m = false ->
      Mem.alloc_flag m1 = true ->
      Mem.alloc_flag m2 = true ->
      (Mem.nextblock m <= Mem.nextblock m1)%positive ->
      alloc_flag_join m m1 m2
  | alloc_flag_join_r:
    forall m m1 m2,
      Mem.alloc_flag m1 = true ->
      Mem.alloc_flag m = false ->
      Mem.alloc_flag m2 = true ->
      (Mem.nextblock m <= Mem.nextblock m1)%positive ->
      alloc_flag_join m1 m m2
  | alloc_flag_join_x:
    forall m1 m2 m,
      Mem.alloc_flag m1 = false ->
      Mem.alloc_flag m2 = false ->
      Mem.alloc_flag m = false ->
      alloc_flag_join m1 m2 m.

  Record join (m1 m2 m: mem) : Prop :=
    mk_join {
        mjoin_contents:
          forall b ofs, Mem.valid_block m b -> contents_join b ofs m1 m2 m;
        mjoin_nextblock:
          Mem.nextblock m = Pos.max (Mem.nextblock m1) (Mem.nextblock m2);
        mjoin_alloc_flag: alloc_flag_join m1 m2 m;
        mjoin_empty_contents:
          forall b ofs, ~Mem.valid_block m b -> contents_join_empty b ofs m1 m2 m
      }.

End JOIN.

Hint Constructors  alloc_flag_join contents_join contents_join_empty: join.

Section JOIN_PROP.

  Lemma join_commutative m1 m2 m:
    join m1 m2 m -> join m2 m1 m.
  Proof with (eauto with join).
    intros H. inv H. constructor.
    - intros. specialize (mjoin_contents0 b ofs H).
      inv mjoin_contents0...
    - now rewrite Pos.max_comm.
    - inv mjoin_alloc_flag0...
    - intros. specialize (mjoin_empty_contents0 b ofs H).
      inv mjoin_empty_contents0...
  Qed.

End JOIN_PROP.

Lemma valid_block_dec m b:
  { Mem.valid_block m b } + { ~Mem.valid_block m b}.
Proof.  apply plt. Qed.

(** * Associativity properties for [join] *)

(** In our relational approach to separation algebras, associativity
  proceeds in two steps. First, we show that three shares join one way
  if and only if they join the other way. *)

Lemma join_associative m1 m2 m3 m12 m23 m123:
  join m1 m2 m12 -> join m12 m3 m123 -> join m2 m3 m23 -> join m1 m23 m123.
Proof.
  intros [H12c H12n H12f H12e] [H123c H123n H123f H123e] [H23c H23n H23f H23e].
  assert (Hanyperm: forall m b ofs k p, Mem.perm m b ofs k p -> Mem.perm m b ofs Max Nonempty).
  { intros. eauto with mem. }
  split.
  - (* contents *)
    intros b ofs Hvb. unfold Mem.valid_block, Plt in *.
    specialize (H123c b ofs Hvb).
    rewrite H123n in Hvb. apply Pos.max_lt_iff in Hvb as [Hvb|Hvb].
    + specialize (H12c b ofs Hvb). inv H12c; inv H123c.
      (* m2 dominates m12 & m3 dominates m123 *)
      * assert (HX: Mem.valid_block m23 b).
        {
          unfold Mem.valid_block, Plt in *. rewrite H23n.
          eapply Pos.max_lt_iff. firstorder.
        }
        specialize (H23c b ofs HX). inv H23c.
        -- left; eauto; try congruence.
           intros. etransitivity; eauto. symmetry. eauto.
        -- left; eauto; try congruence.
           intros; split; intros; eauto.
           exfalso. apply H4. apply H0. apply H10. eauto with mem.
           exfalso. apply H9. apply H5. eauto with mem.
      (* m2 dominates m12 & m12 dominates m123 *)
      * assert (HX: Mem.valid_block m23 b).
        {
          unfold Mem.valid_block, Plt in *. rewrite H23n.
          eapply Pos.max_lt_iff. firstorder.
        }
        specialize (H23c b ofs HX). inv H23c.
        -- left; eauto; try congruence.
           intros; split; intros; eauto.
           exfalso. apply H4. apply H10. eauto with mem.
           exfalso. apply H9. apply H0. apply H5. eauto with mem.
        -- left; eauto; try congruence.
           intros. etransitivity; eauto.
           etransitivity; eauto. symmetry; eauto.
      (* m1 dominates m12 & m3 dominates m123 *)
      * assert (HX: Mem.valid_block m23 b).
        {
          unfold Mem.valid_block, Plt in *. rewrite H23n.
          eapply Pos.max_lt_iff. now right.
        }
        specialize (H23c b ofs HX). inv H23c.
        -- left; eauto; try congruence.
           intros x. apply H4. apply H0. eauto.
           intros. etransitivity; eauto. symmetry; eauto.
        -- left; eauto; try congruence.
           intros x. apply H4. apply H0. eauto.
           intros; split; intros; eauto.
           exfalso. apply H. apply H10. eauto with mem.
           exfalso. apply H9. apply H5. eauto with mem.
      (* m1 dominates m12 & m12 dominates m123 *)
      * destruct (valid_block_dec m23 b).
        -- specialize (H23c b ofs v). inv H23c.
           ++ right; eauto; try congruence.
              intros x. apply H4. apply H10. eauto.
              intros. etransitivity; eauto.
           ++ right; eauto; try congruence.
              intros x. apply H. apply H10. eauto.
              intros. etransitivity; eauto.
        -- specialize (H23e b ofs n). inv H23e.
           right; eauto; try congruence.
           intros. etransitivity; eauto.
    + assert (HX: Mem.valid_block m23 b).
      {
        unfold Mem.valid_block, Plt in *. rewrite H23n.
        eapply Pos.max_lt_iff. now right.
      }
      specialize (H23c b ofs HX). inv H23c; inv H123c.
      (* m3 dominates m23 & m3 dominates m123 *)
      * destruct (valid_block_dec m12 b).
        -- specialize (H12c b ofs v). inv H12c.
           ++ left; eauto; try congruence.
              intros. etransitivity; eauto. symmetry; eauto.
           ++ left; eauto; try congruence.
              intros x. apply H4. apply H10. eauto.
              intros. etransitivity; eauto. symmetry; eauto.
        -- specialize (H12e b ofs n). inv H12e.
           left; eauto; try congruence.
           intros. etransitivity; eauto. symmetry; eauto.
      (* m3 dominates m23 & m12 dominates m123 *)
      * specialize (H12c b ofs H8). inv H12c.
        -- left; eauto; try congruence.
           intros; split; intros; exfalso.
           apply H4. apply H0. eauto with mem.
           apply H. apply H10. apply H5. eauto with mem.
        -- right; eauto; try congruence.
           rewrite <- H0. eauto.
           intros. etransitivity; eauto.
      (* m2 dominates m23 & m3 dominates m123 *)
      * destruct (valid_block_dec m12 b).
        -- specialize (H12c b ofs v). inv H12c.
           ++ left; eauto; try congruence.
              intros. split; intros; exfalso.
              apply H4. apply H10. apply H0. eauto with mem.
              apply H. apply H5. eauto with mem.
           ++ left; eauto; try congruence.
              rewrite H10. eauto.
              intros. split; intros; exfalso.
              apply H9. apply H0. eauto with mem.
              apply H. apply H5. eauto with mem.
        -- specialize (H12e b ofs n). inv H12e.
           left; eauto; try congruence.
      (* m2 dominates m23 & m12 dominates m123 *)
      * specialize (H12c b ofs H8). inv H12c.
        -- left; eauto; try congruence.
           intros. etransitivity; eauto. etransitivity; eauto.
           symmetry; eauto.
        -- right; eauto; try congruence.
           rewrite <- H0. eauto.
           intros. etransitivity; eauto.
  - rewrite H123n. rewrite H12n, H23n.
    symmetry. apply Pos.max_assoc.
  - inv H12f; inv H123f; inv H23f; try congruence.
    * apply alloc_flag_join_l; eauto.
      rewrite H23n. lia.
    * apply alloc_flag_join_r; eauto.
      rewrite H23n. rewrite H12n in H6. lia.
    * apply alloc_flag_join_l; eauto.
      rewrite H23n. rewrite H12n in H5. lia.
    * apply alloc_flag_join_x; eauto.
  - intros b ofs Hvb. specialize (H123e b ofs Hvb).
    apply Pos.le_nlt in Hvb. rewrite H123n in Hvb.
    apply Pos.max_lub_iff in Hvb as [Hvb1 Hvb2]; eauto.
    rewrite H12n in Hvb1.
    apply Pos.max_lub_iff in Hvb1 as [Hvb0 Hvb1]; eauto.
    assert (~Mem.valid_block m1 b). apply Pos.le_nlt. apply Hvb0.
    assert (~Mem.valid_block m2 b). apply Pos.le_nlt. apply Hvb1.
    assert (~Mem.valid_block m3 b). apply Pos.le_nlt. apply Hvb2.
    assert (Ha: ~Mem.valid_block m12 b).
    {
      apply Pos.le_nlt. rewrite H12n.
      apply Pos.max_lub_iff; split; eauto.
    }
    assert (Hb: ~Mem.valid_block m23 b).
    {
      apply Pos.le_nlt. rewrite H23n.
      apply Pos.max_lub_iff; split; eauto.
    }
    specialize (H12e b ofs Ha).
    specialize (H23e b ofs Hb).
    inv H123e; inv H12e; inv H23e.
    constructor; eauto.
Qed.

(** Then, we prove the stronger property that if three shares join one
  way, then the intermediate share required to join them the other way
  actually exists. This property is a bit harder to establish because
  we must show how to construct this intermediate memory state [m23]
  when [m1 • m2 ≡ m12] and [m12 • m3 ≡ m123].

  One approach would be to remove from [m123] any location where [m1]
  is defined. However, because of the way [PMap] work, it is difficult
  to filter them in an index-dependent manner.

  So instead we choose to construct a combination of [m2] and [m3]
  which is an appropriate join when the premises hold.
  If [m2] and [m3] overlap (a situation which the premises prevent),
  we can just choose convenient dummy values. *)

Definition memval_combine (v1 v2: memval) :=
  match v1 with
    | Undef => v2
    | _ => v1
  end.

Definition perm_combine (p1 p2: option permission): option permission :=
  match p1, p2 with
    | None, None => None
    | Some x, None => Some x
    | None, Some x => Some x
    | Some _, Some _ => Some Freeable
  end.

Definition option_map2 {A} (f: A -> A -> A) (d1 d2: A): option A -> option A -> option A :=
  fun x1 x2 =>
    match x1, x2 with
      | None, None => None
      | Some a1, None => Some (f a1 d2)
      | None, Some a2 => Some (f d1 a2)
      | Some a1, Some a2 => Some (f a1 a2)
    end.

Definition PMap_combine {A} (f: A -> A -> A) (m1 m2: PMap.t A) :=
  (f (fst m1) (fst m2),
   PTree.combine (option_map2 f (fst m1) (fst m2)) (snd m1) (snd m2)).

Definition ZMap_combine {A} (f: A -> A -> A) (m1 m2: ZMap.t A): ZMap.t A :=
  PMap_combine f m1 m2.

(** With auxiliary combination constructions defined, we can put
  everything together and define the resulting memory state. *)

Lemma PMap_gcombine {A} (f: A -> A -> A) (m1 m2: PMap.t A) (i: positive):
  (PMap_combine f m1 m2) !! i = f (m1 !! i) (m2 !! i).
Proof.
  unfold PMap_combine, PMap.get; cbn.
  rewrite PTree.gcombine by auto.
  destruct PTree.get, PTree.get; auto.
Qed.

Lemma ZMap_gcombine {A} (f: A -> A -> A) (m1 m2: PMap.t A) (i: Z):
  ZMap.get i (ZMap_combine f m1 m2) = f (ZMap.get i m1) (ZMap.get i m2).
Proof.
  unfold ZMap_combine, ZMap.get.
  apply PMap_gcombine.
Qed.

Program Definition mem_combine (m1 m2: mem): mem :=
  {|
    Mem.mem_contents :=
      PMap_combine
        (ZMap_combine memval_combine)
        (Mem.mem_contents m1)
        (Mem.mem_contents m2);
    Mem.mem_access :=
      PMap_combine
        (fun f1 f2 ofs k => perm_combine (f1 ofs k) (f2 ofs k))
        (Mem.mem_access m1)
        (Mem.mem_access m2);
    Mem.nextblock :=
      Pos.max (Mem.nextblock m1) (Mem.nextblock m2);
    Mem.alloc_flag :=
      Mem.alloc_flag m1 || Mem.alloc_flag m2;
  |}.
Next Obligation.
  rewrite PMap_gcombine.
  pose proof (Mem.access_max m1 b ofs).
  pose proof (Mem.access_max m2 b ofs).
  destruct PMap.get, PMap.get; cbn in *; try tauto;
  destruct PMap.get, PMap.get; cbn in *; try tauto;
  constructor.
Qed.
Next Obligation.
  rewrite PMap_gcombine.
  rewrite !Mem.nextblock_noaccess by extlia.
  reflexivity.
Qed.
Next Obligation.
  rewrite PMap_gcombine. cbn.
  rewrite !Mem.contents_default.
  reflexivity.
Qed.

(** Now it just remains to establish that under the right
  circumstances, this memory state is a join. *)

Lemma mem_combine_perm_l m1 m2 b ofs k p:
  Mem.perm m1 b ofs k p -> Mem.perm (mem_combine m1 m2) b ofs k p.
Proof.
  unfold Mem.perm. cbn. rewrite PMap_gcombine.
  destruct (_ !! b ofs k); cbn; firstorder.
  destruct (_ !! b ofs k); cbn; firstorder.
  eauto with mem.
Qed.

Lemma mem_combine_perm_r m1 m2 b ofs k p:
  Mem.perm m2 b ofs k p -> Mem.perm (mem_combine m1 m2) b ofs k p.
Proof.
  unfold Mem.perm. cbn. rewrite PMap_gcombine.
  destruct (_ !! b ofs k); cbn; firstorder.
  destruct (_ !! b ofs k); cbn; firstorder.
  eauto with mem.
Qed.

Lemma mem_combine_perm_iff_l m1 m2 b ofs k p:
  ~ Mem.perm m2 b ofs Max Nonempty ->
  Mem.perm (mem_combine m1 m2) b ofs k p <-> Mem.perm m1 b ofs k p.
Proof.
  intro.
  assert (~ Mem.perm m2 b ofs k Nonempty) as Hn by eauto using Mem.perm_max.
  assert (~ Mem.perm m2 b ofs k p) as Hn' by eauto using Mem.perm_implies, perm_any_N.
  revert Hn Hn'; clear.
  unfold Mem.perm. cbn. rewrite PMap_gcombine.
  destruct ((Mem.mem_access m1) !! b ofs k) as [p1 | ],
           ((Mem.mem_access m2) !! b ofs k) as [p2 | ]; cbn; try tauto.
  intro H. elim H. constructor.
Qed.

Lemma mem_combine_perm_iff_r m1 m2 b ofs k p:
  ~ Mem.perm m1 b ofs Max Nonempty ->
  Mem.perm (mem_combine m1 m2) b ofs k p <-> Mem.perm m2 b ofs k p.
Proof.
  intro.
  assert (~ Mem.perm m1 b ofs k Nonempty) as Hn by eauto using Mem.perm_max.
  assert (~ Mem.perm m1 b ofs k p) as Hn' by eauto using Mem.perm_implies, perm_any_N.
  revert Hn Hn'; clear.
  unfold Mem.perm. cbn. rewrite PMap_gcombine.
  destruct ((Mem.mem_access m1) !! b ofs k) as [p1 | ],
           ((Mem.mem_access m2) !! b ofs k) as [p2 | ]; cbn; try tauto.
  intro H. elim H. constructor.
Qed.

Lemma mem_gcombine m1 m2 b ofs:
  ZMap.get ofs (Mem.mem_contents (mem_combine m1 m2)) !! b =
  memval_combine (ZMap.get ofs (Mem.mem_contents m1) !! b)
                 (ZMap.get ofs (Mem.mem_contents m2) !! b).
Proof.
  cbn.
  rewrite PMap_gcombine, ZMap_gcombine.
  reflexivity.
Qed.

Lemma join_split m1 m2 m3 m12 m123:
  join m1 m2 m12 -> join m12 m3 m123 ->
  exists m23, join m2 m3 m23.
Proof.
  intros [H12c H12nb H12a H12e] [H123c H123nb H123a H123e].
  exists (mem_combine m2 m3).
  constructor.
  - (* Contents *)
    intros b ofs Hvb.
    assert (Hvb123: Mem.valid_block m123 b).
    {
      unfold Mem.valid_block, Plt in *. rewrite H123nb.
      apply Pos.max_lt_iff in Hvb as [Hvb|Hvb]; apply Pos.max_lt_iff.
      - left. rewrite H12nb. apply Pos.max_lt_iff. now right.
      - now right.
    }
    specialize (H123c b ofs Hvb123). inv H123c.
    + (* Location is empty in m12 hence m2 *)
      destruct (valid_block_dec m12 b).
      * specialize (H12c b ofs v). inv H12c.
        -- left; eauto; try congruence.
           ++ firstorder.
           ++ intros. rewrite mem_combine_perm_iff_r; firstorder.
           ++ rewrite mem_gcombine.
              replace (ZMap.get ofs (Mem.mem_contents m2) !! b) with Undef.
              reflexivity. congruence.
        -- left; eauto.
           ++ intros. rewrite mem_combine_perm_iff_r; firstorder.
           ++ rewrite mem_gcombine.
              replace (ZMap.get ofs (Mem.mem_contents m2) !! b) with Undef.
              reflexivity.
      * specialize (H12e b ofs n). inv H12e; eauto.
        left; eauto.
        -- intros. rewrite mem_combine_perm_iff_r; firstorder.
        -- rewrite mem_gcombine.
           replace (ZMap.get ofs (Mem.mem_contents m2) !! b) with Undef.
           reflexivity.
    + (* Location is empty in m3 *)
      specialize (H12c b ofs H3). inv H12c.
      -- right; auto.
         ++ intros. rewrite mem_combine_perm_iff_l by auto. reflexivity.
         ++ rewrite mem_gcombine, H1.
            clear. destruct ZMap.get; reflexivity.
      -- apply Pos.max_lt_iff in Hvb as [Hvb|Hvb].
         ++ right; auto.
            ** intros. rewrite mem_combine_perm_iff_l by auto. reflexivity.
            ** rewrite mem_gcombine, H1.
               clear. destruct ZMap.get; reflexivity.
         ++ left; auto.
            ** intros. rewrite mem_combine_perm_iff_l by auto.
               split; intros; exfalso; eauto with mem.
            ** rewrite mem_gcombine. rewrite H6. reflexivity.
  - (* Nextblock *)
    reflexivity.
  - (* Alloc flag *)
    inv H12a; inv H123a; try congruence.
    + apply alloc_flag_join_r; eauto.
      cbn. rewrite H0. reflexivity.
      rewrite H12nb in H6.
      apply Pos.max_le_iff in H6 as [|].
      * etransitivity; eauto.
      * eauto.
    + apply alloc_flag_join_x; eauto.
      cbn. rewrite H0. eauto.
    + apply alloc_flag_join_l; eauto.
      cbn. rewrite H0. eauto.
      rewrite H12nb in H5.
      apply Pos.max_lub_iff in H5 as [? ?]; eauto.
    + apply alloc_flag_join_x; eauto.
      cbn. rewrite H0; eauto.
  - intros b ofs Hvb.
    apply Pos.le_nlt in Hvb.
    apply Pos.max_lub_iff in Hvb as [Hvb1 Hvb2]; eauto.
    assert (Hvb1': ~ Mem.valid_block m2 b).
    { apply Pos.le_nlt; eauto. }
    assert (Hvb2': ~ Mem.valid_block m3 b).
    { apply Pos.le_nlt; eauto. }
    destruct (valid_block_dec m1 b).
    + assert (Hvb3: Mem.valid_block m12 b).
      {
        unfold Mem.valid_block. rewrite H12nb.
        apply Pos.max_lt_iff. left. apply v.
      }
      assert (Hvb4: Mem.valid_block m123 b).
      {
        unfold Mem.valid_block. rewrite H123nb.
        apply Pos.max_lt_iff. left. apply Hvb3.
      }
      specialize (H12c b ofs Hvb3).
      specialize (H123c b ofs Hvb4).
      inv H12c; inv H123c; try congruence.
      constructor; eauto.
      * rewrite mem_combine_perm_iff_l; eauto.
      * rewrite mem_gcombine. rewrite H1. eauto.
    + assert (Hvb3: ~Mem.valid_block m12 b).
      {
        apply Pos.le_nlt. rewrite H12nb.
        apply Pos.max_lub_iff; split; eauto.
        apply Pos.le_nlt. apply n.
      }
      assert (Hvb4: ~Mem.valid_block m123 b).
      {
        apply Pos.le_nlt. rewrite H123nb.
        apply Pos.max_lub_iff; split; eauto.
        apply Pos.le_nlt. apply Hvb3.
      }
      specialize (H12e b ofs Hvb3).
      specialize (H123e b ofs Hvb4).
      inv H12e. inv H123e.
      constructor; eauto.
      * rewrite mem_combine_perm_iff_l; eauto.
      * rewrite mem_gcombine. rewrite H3. eauto.
Qed.

(** Once we bring in the first associativity property, we can show
  that the memory state we have constructed joins with [m1] into [m123]. *)

Lemma join_associative_exist m1 m2 m3 m12 m123:
  join m1 m2 m12 -> join m12 m3 m123 ->
  exists m23, join m2 m3 m23 /\ join m1 m23 m123.
Proof.
  intros.
  destruct (join_split m1 m2 m3 m12 m123) as [m23 Hm23]; auto.
  exists m23; eauto using join_associative.
Qed.

(** ------------------------------------------------------------------------- *)
(** ** Monotonicity *)

Section JOIN_PROP.

  Variable (m: mem).

  Instance valid_pointer_join:
    Monotonic
      (@Mem.valid_pointer)
      (join m ++> - ==> - ==> Bool.le).
  Proof.
    do 4 rstep. destruct Mem.valid_pointer eqn: X; try easy.
    cbn. rewrite !Mem.valid_pointer_nonempty_perm in *.
    rename x0 into b. rename x1 into ofs.
    exploit Mem.perm_valid_block; eauto. intros A.
    assert (B: Mem.valid_block y b).
    { unfold Mem.valid_block in *. inv H. unfold Plt in *.
      rewrite mjoin_nextblock0. lia. }
    destruct H. specialize (mjoin_contents0 _ ofs B).
    inv mjoin_contents0.
    - apply H0. apply X.
    - exfalso. apply H. eauto with mem.
  Qed.

  Instance weak_valid_pointer_join:
    Monotonic
      (@Mem.weak_valid_pointer)
      (join m ++> - ==> - ==> Bool.le).
  Proof.
    unfold Mem.weak_valid_pointer. do 4 rstep.
    destruct orb eqn: X.
    - simpl. rewrite orb_true_iff in *.
      destruct X; [ left | right ]; apply valid_pointer_join in H.
      specialize (H x0 x1). rewrite H0 in H. eauto.
      specialize (H x0 (x1 - 1)%Z). rewrite H0 in H. eauto.
    - easy.
  Qed.

  Instance bool_val_join:
    Monotonic
      (@bool_val)
      (- ==> - ==> join m ++> option_le eq).
  Proof. unfold bool_val. rauto. Qed.

  Instance sem_unary_operation_join:
    Monotonic
      (@sem_unary_operation)
      (- ==> - ==> - ==> join m ++> option_le eq).
  Proof.
    unfold sem_unary_operation.
    unfold sem_notbool, sem_notint, sem_neg, sem_absfloat.
    repeat rstep. f_equal. congruence.
  Qed.

  Instance sem_cast_join:
    Monotonic
      (@Cop.sem_cast)
      (- ==> - ==> - ==> join m ++> option_le eq).
  Proof. unfold Cop.sem_cast. rauto. Qed.

  Instance sem_binarith_join:
    Monotonic
      (@Cop.sem_binarith)
      (- ==> - ==> - ==> - ==> - ==> - ==> - ==> - ==> join m ++> option_le eq).
  Proof. unfold Cop.sem_binarith. rauto. Qed.

  Instance cmp_ptr_join:
    Related
      (@Cop.cmp_ptr)
      (@Cop.cmp_ptr)
      (join m ++> - ==> - ==> - ==> option_le eq).
  Proof.
    rstep. rstep. rstep. rstep. rstep.
    unfold Cop.cmp_ptr. rstep. rstep. rewrite H0. reflexivity. rstep.
    - rstep. unfold Val.cmplu_bool. repeat rstep.
      destruct eq_block; repeat rstep.
    - rstep. unfold Val.cmpu_bool. repeat rstep.
      destruct eq_block; repeat rstep.
  Qed.

  Instance sem_cmp_join:
    Monotonic
      (@Cop.sem_cmp)
      (- ==> - ==> - ==> - ==> - ==> join m ++> option_le eq).
  Proof. unfold Cop.sem_cmp. repeat rstep. Qed.

  Instance sem_binary_operation_join:
    Monotonic
      (@sem_binary_operation)
      (- ==> - ==> - ==> - ==> - ==> - ==> join m ++> option_le eq).
  Proof.
    unfold sem_binary_operation.
    unfold
      Cop.sem_add,
      Cop.sem_add_ptr_int,
      Cop.sem_add_ptr_long,
      Cop.sem_sub,
      Cop.sem_mul,
      Cop.sem_div,
      Cop.sem_mod,
      Cop.sem_and,
      Cop.sem_or,
      Cop.sem_xor,
      Cop.sem_shl,
      Cop.sem_shr.
    repeat rstep.
  Qed.

  Lemma perm_join m1 m2 b ofs k p:
    join m m1 m2 ->
    Mem.perm m1 b ofs k p ->
    Mem.perm m2 b ofs k p.
  Proof.
    intros HM H. inv HM. specialize (mjoin_contents0 b ofs).
    exploit mjoin_contents0.
    {
      exploit Mem.perm_valid_block; eauto.
      intros X. unfold Mem.valid_block, Plt in *.
      rewrite mjoin_nextblock0. lia.
    }
    intro X. inv X.
    - apply H1. apply H.
    - exfalso. apply H0. eauto with mem.
  Qed.

  Lemma range_perm_join m1 m2 b lo hi k p:
    join m m1 m2 ->
    Mem.range_perm m1 b lo hi k p ->
    Mem.range_perm m2 b lo hi k p.
  Proof.
    intros HM H ofs X. specialize (H _ X).
    eauto using perm_join.
  Qed.

  Instance load_join:
    Monotonic
      (@Mem.load)
      (- ==> join m ++> - ==> - ==> option_le eq).
  Proof.
    repeat rstep. destruct Mem.load eqn: X; try constructor.
    rename x1 into b. rename x2 into ofs. rename x into ch.
    rename x0 into m1. rename y into m2.
    exploit Mem.load_valid_access. eauto. intros [A B].
    exploit Mem.valid_access_load. split. eapply range_perm_join; eauto. apply B.
    intros [w Y]. rewrite Y. constructor.
    exploit Mem.load_result. apply X.
    exploit Mem.load_result. apply Y. intros -> ->.
    f_equal. apply Mem.getN_exten.
    destruct H.
    assert (H: Mem.valid_block m2 b).
    {
      exploit Mem.perm_valid_block.
      apply A. instantiate (1 := ofs). split; try lia.
      destruct ch; cbn; try lia.
      intros. unfold Mem.valid_block, Plt in *.
      rewrite mjoin_nextblock0. lia.
    }
    intros i Hi. specialize (mjoin_contents0 b i H).
    inv mjoin_contents0; eauto.
    - exfalso. apply H0. exploit A. instantiate (1 := i).
      rewrite <- size_chunk_conv in Hi. exact Hi.
      eauto with mem.
  Qed.

  Instance loadv_join:
    Monotonic
      (@Mem.loadv)
      (- ==> join m ++> - ==> option_le eq).
  Proof. unfold Mem.loadv. repeat rstep. Qed.

  Instance deref_loc_join a:
    Monotonic
      (@deref_loc a)
      (join m ++> - ==> - ==> - ==> - ==> impl).
  Proof.
    repeat rstep. intros A. inv A; eauto using @deref_loc_reference, @deref_loc_copy.
    transport H1. subst. eapply deref_loc_value; eauto.
    constructor. inv H0. constructor; eauto.
    transport H5. subst; eauto.
  Qed.

  Lemma get_setN_inside:
    forall vl p q c,
      p <= q < p + Z.of_nat (length vl) ->
      (ZMap.get q (Mem.setN vl p c)) = nth (Z.to_nat (q - p)) vl Undef.
  Proof.
    induction vl; intros.
    simpl in H. lia.
    simpl length in H. rewrite Nat2Z.inj_succ in H. simpl.
    destruct (zeq p q).
    - subst q. rewrite Mem.setN_outside by lia. rewrite ZMap.gss.
      replace (p - p) with 0 by lia. reflexivity.
    - rewrite IHvl by lia. destruct H as [A B].
      replace (q - p) with (Z.succ (q - p - 1)) by lia.
      rewrite Z2Nat.inj_succ. 2: lia.
      f_equal. f_equal. lia.
  Qed.

  Instance store_join:
    Monotonic
      (@Mem.store)
      (- ==> join m ++> - ==> - ==> - ==> option_le (join m)).
  Proof.
    repeat rstep. destruct Mem.store eqn: X; try constructor.
    rename x into ch. rename x1 into b. rename x2 into ofs. rename x3 into v.
    rename x0 into m1. rename y into m2.
    exploit Mem.store_valid_access_3; eauto. intros [A B].
    edestruct Mem.valid_access_store as [n Y]. split. 2: eauto.
    eapply range_perm_join; eauto.
    rewrite Y. constructor.
    constructor.
    - intros bx ox Hbx. destruct H.
      assert (HV: Mem.valid_block m2 bx).
      { eapply Mem.store_valid_block_2; eauto. }
      specialize (mjoin_contents0 bx ox HV). inv mjoin_contents0.
      + apply contents_join_l; eauto.
        * intros k p. specialize (H0 k p).
          assert (P1: Mem.perm m0 bx ox k p <-> Mem.perm m1 bx ox k p).
          split; eauto with mem.
          assert (P2: Mem.perm n bx ox k p <-> Mem.perm m2 bx ox k p).
          split; eauto with mem.
          rewrite P1. rewrite H0. symmetry. apply P2.
        * exploit Mem.store_mem_contents. apply X. intros ->.
          exploit Mem.store_mem_contents. apply Y. intros ->.
          destruct (PMap.elt_eq b bx).
          -- subst. rewrite !PMap.gss.
             destruct (zlt ox ofs).
             ++ now rewrite !Mem.setN_outside by lia.
             ++ destruct (zle (ofs + Z.of_nat (length (encode_val ch v))) ox).
                now rewrite !Mem.setN_outside by lia.
                now rewrite !get_setN_inside by lia.
          -- rewrite !PMap.gso; eauto.
        * eauto with mem.
      + apply contents_join_r; eauto.
        * intros P. apply H. eauto with mem.
        * intros k p.
          assert (P: Mem.perm n bx ox k p <-> Mem.perm m2 bx ox k p).
          split; eauto with mem.
          rewrite P. eauto.
        * exploit Mem.store_mem_contents. apply X. intros ->.
          destruct (PMap.elt_eq b bx).
          -- subst. rewrite PMap.gss.
             destruct (zlt ox ofs).
             ++ now rewrite !Mem.setN_outside by lia.
             ++ destruct (zle (ofs + Z.of_nat (length (encode_val ch v))) ox).
                now rewrite !Mem.setN_outside by lia.
                specialize (A ox).
                exploit A.
                rewrite encode_val_length in g0.
                rewrite <- size_chunk_conv in g0. lia.
                intros. exfalso. eauto with mem.
          -- rewrite PMap.gso; eauto.
        * rewrite H2.
          exploit Mem.store_mem_contents. apply Y. intros ->.
          destruct (PMap.elt_eq b bx).
          -- subst. rewrite PMap.gss.
             destruct (zlt ox ofs).
             ++ now rewrite !Mem.setN_outside by lia.
             ++ destruct (zle (ofs + Z.of_nat (length (encode_val ch v))) ox).
                now rewrite !Mem.setN_outside by lia.
                specialize (A ox).
                exploit A.
                rewrite encode_val_length in g0.
                rewrite <- size_chunk_conv in g0. lia.
                intros. exfalso. eauto with mem.
          -- rewrite PMap.gso; eauto.
    - destruct H.
      apply Mem.nextblock_store in X.
      apply Mem.nextblock_store in Y. congruence.
    - destruct H.
      exploit Mem.nextblock_store. apply X. intros C.
      apply Mem.store_alloc_flag in X.
      apply Mem.store_alloc_flag in Y.
      inv mjoin_alloc_flag0.
      + apply alloc_flag_join_l; eauto. congruence.
      + apply alloc_flag_join_r; eauto. congruence.
      + apply alloc_flag_join_x; eauto.
    - intros bx ox Hbx. destruct H.
      destruct (PMap.elt_eq b bx).
      + subst. assert (Mem.valid_block m2 bx).
        {
          apply Mem.store_valid_access_3 in Y as [C D].
          eapply Mem.perm_valid_block. apply C.
          instantiate (1 := ofs).
          rewrite size_chunk_conv. destruct ch; cbn; lia.
        }
        exploit Mem.store_valid_block_1; eauto. easy.
      + assert (Hvb: ~Mem.valid_block m2 bx).
        { intros x. apply Hbx.
          eapply Mem.store_valid_block_1; eauto. }
        specialize (mjoin_empty_contents0 bx ox Hvb).
        inv mjoin_empty_contents0.
        constructor; eauto.
        * intros x. apply H0. eauto with mem.
        * intros x. apply H1. eauto with mem.
        * erewrite Mem.store_mem_contents; eauto.
          rewrite PMap.gso; eauto.
        * erewrite Mem.store_mem_contents; eauto.
          rewrite PMap.gso; eauto.
        * intros x. apply H6. eauto with mem.
  Qed.

  Instance storev_join:
    Monotonic
      (@Mem.storev)
      (- ==> join m ++> - ==> - ==> option_le (join m)).
  Proof. unfold Mem.storev. repeat rstep. Qed.

  Transparent Mem.loadbytes Mem.storebytes.
  Instance loadbytes_join:
    Monotonic
      (@Mem.loadbytes)
      (join m ++> - ==> - ==> - ==> option_le eq).
  Proof.
    repeat rstep. destruct Mem.loadbytes eqn: X; try constructor.
    unfold Mem.loadbytes in *.
    rename x0 into b. rename x1 into ofs. rename x2 into sz.
    rename x into m1. rename y into m2.
    destruct (Mem.range_perm_dec m1 b ofs (ofs + sz) Cur Readable); inv X.
    destruct Mem.range_perm_dec.
    - constructor. apply Mem.getN_exten. intros i Hi.
      destruct H.
      assert (HI: ofs <= i < ofs + sz).
      {
        destruct (zle 0 sz).
        + rewrite Z2Nat.id in Hi; eauto.
        + rewrite Z_to_nat_neg in Hi; lia.
      }
      assert (HV: Mem.valid_block m2 b).
      { eapply Mem.perm_valid_block. apply r0; eauto. }
      specialize (mjoin_contents0 b i HV).
      inv mjoin_contents0; eauto.
      specialize (r i).  exploit r; eauto.
      intros. exfalso. eauto with mem.
    - exfalso. destruct H.  apply n. intros x Hx.
      assert (HV: Mem.valid_block m2 b).
      {
        exploit Mem.perm_valid_block. apply r; eauto.
        intros. unfold Mem.valid_block, Plt in *.
        rewrite mjoin_nextblock0. lia.
      }
      specialize (mjoin_contents0 b x HV). inv mjoin_contents0.
      + apply H0. eauto.
      + exfalso. apply H. eauto with mem.
  Qed.

  Instance storebytes_join:
    Monotonic
      (@Mem.storebytes)
      (join m ++> - ==> - ==> - ==> option_le (join m)).
  Proof.
    repeat rstep. destruct Mem.storebytes eqn: X; try constructor.
    rename x0 into b. rename x1 into ofs. rename x2 into vl.
    rename x into m1. rename y into m2.
    pose proof (Mem.storebytes_range_perm _ _ _ _ _ X) as A.
    edestruct Mem.range_perm_storebytes as (n & Y).
    eapply range_perm_join; eauto.  rewrite Y. constructor.
    constructor.
    - intros bx ox Hbx. destruct H.
      assert (HV: Mem.valid_block m2 bx).
      { eapply Mem.storebytes_valid_block_2; eauto. }
      specialize (mjoin_contents0 bx ox HV). inv mjoin_contents0.
      + apply contents_join_l; eauto.
        * intros k p. specialize (H0 k p).
          assert (P1: Mem.perm m0 bx ox k p <-> Mem.perm m1 bx ox k p).
          split; eauto with mem.
          assert (P2: Mem.perm n bx ox k p <-> Mem.perm m2 bx ox k p).
          split; eauto with mem.
          rewrite P1. rewrite H0. symmetry. apply P2.
        * exploit Mem.storebytes_mem_contents. apply X. intros ->.
          exploit Mem.storebytes_mem_contents. apply Y. intros ->.
          destruct (PMap.elt_eq b bx).
          -- subst. rewrite !PMap.gss.
             destruct (zlt ox ofs).
             ++ now rewrite !Mem.setN_outside by lia.
             ++ destruct (zle (ofs + Z.of_nat (Datatypes.length vl)) ox).
                now rewrite !Mem.setN_outside by lia.
                now rewrite !get_setN_inside by lia.
          -- rewrite !PMap.gso; eauto.
        * eauto with mem.
      + apply contents_join_r; eauto.
        * intros P. apply H. eauto with mem.
        * intros k p.
          assert (P: Mem.perm n bx ox k p <-> Mem.perm m2 bx ox k p).
          split; eauto with mem.
          rewrite P. eauto.
        * exploit Mem.storebytes_mem_contents. apply X. intros ->.
          destruct (PMap.elt_eq b bx).
          -- subst. rewrite PMap.gss.
             destruct (zlt ox ofs).
             ++ now rewrite !Mem.setN_outside by lia.
             ++ destruct (zle (ofs + Z.of_nat (Datatypes.length vl)) ox).
                now rewrite !Mem.setN_outside by lia.
                specialize (A ox). exploit A. lia.
                intros. exfalso. eauto with mem.
          -- rewrite PMap.gso; eauto.
        * rewrite H2.
          exploit Mem.storebytes_mem_contents. apply Y. intros ->.
          destruct (PMap.elt_eq b bx).
          -- subst. rewrite PMap.gss.
             destruct (zlt ox ofs).
             ++ now rewrite !Mem.setN_outside by lia.
             ++ destruct (zle (ofs + Z.of_nat (Datatypes.length vl)) ox).
                now rewrite !Mem.setN_outside by lia.
                specialize (A ox). exploit A. lia.
                intros. exfalso. eauto with mem.
          -- rewrite PMap.gso; eauto.
    - destruct H.
      apply Mem.nextblock_storebytes in X.
      apply Mem.nextblock_storebytes in Y. congruence.
    - destruct H.
      exploit Mem.nextblock_storebytes. apply X. intros C.
      apply Mem.storebytes_alloc_flag in X.
      apply Mem.storebytes_alloc_flag in Y.
      inv mjoin_alloc_flag0.
      + apply alloc_flag_join_l; eauto. congruence.
      + apply alloc_flag_join_r; eauto. congruence.
      + apply alloc_flag_join_x; eauto.
    - intros bx ox Hbx. destruct H.
      destruct (PMap.elt_eq b bx).
      + subst. destruct (valid_block_dec m2 bx).
        * exfalso. apply Hbx. eauto with mem.
        * specialize (mjoin_empty_contents0 bx ox n0).
          inv mjoin_empty_contents0.
          constructor; eauto with mem.
          -- unfold Mem.storebytes in X.
             destruct Mem.range_perm_dec eqn: Hp;
               try congruence. inv X. cbn.
             rewrite PMap.gss.
             destruct (zlt ox ofs).
             ++ now rewrite !Mem.setN_outside by lia.
             ++ destruct (zle (ofs + Z.of_nat (Datatypes.length vl)) ox).
                now rewrite !Mem.setN_outside by lia.
                specialize (A ox). exploit A. lia.
                intros. exfalso. eauto with mem.
          -- unfold Mem.storebytes in Y.
             destruct Mem.range_perm_dec eqn: Hp;
               try congruence. inv Y. cbn.
             rewrite PMap.gss.
             destruct (zlt ox ofs).
             ++ now rewrite !Mem.setN_outside by lia.
             ++ destruct (zle (ofs + Z.of_nat (Datatypes.length vl)) ox).
                now rewrite !Mem.setN_outside by lia.
                specialize (A ox). exploit A. lia.
                intros. exfalso. eauto with mem.
      + assert (Hvb: ~Mem.valid_block m2 bx). eauto with mem.
        specialize (mjoin_empty_contents0 bx ox Hvb).
        inv mjoin_empty_contents0.
        constructor; eauto with mem.
        * erewrite Mem.storebytes_mem_contents; eauto.
          rewrite PMap.gso; eauto.
        * erewrite Mem.storebytes_mem_contents; eauto.
          rewrite PMap.gso; eauto.
  Qed.

  Opaque Mem.loadbytes Mem.storebytes.

  Instance assign_loc_join:
    Monotonic
      (@assign_loc)
      (- ==> - ==> join m ++> - ==> - ==> - ==> - ==> set_le (join m)).
  Proof.
    repeat rstep. intros ma A. inv A.
    - transport H1. eexists; split; eauto.
      eapply assign_loc_value; eauto.
    - transport H4. subst.
      transport H5.
      eexists; split; eauto.
      eapply assign_loc_copy; eauto.
    - inv H0. transport H5. subst. transport H6.
      eexists. split; eauto. repeat econstructor; eauto. all: lia.
  Qed.

  Transparent Mem.free.

  Instance free_join:
    Monotonic
      (@Mem.free)
      (join m ++> - ==> - ==> - ==> option_le (join m)).
  Proof.
    repeat rstep.
    rename x0 into b. rename x1 into lo. rename x2 into hi.
    rename x into m1. rename y into m2.
    destruct (Mem.free m1 b lo hi) eqn: HF; try constructor.
    edestruct Mem.range_perm_free.
    eapply range_perm_join; eauto.
    eapply Mem.free_range_perm; eauto.
    rewrite e. constructor. constructor.
    - intros bx ox Hx. destruct H.
      assert (HV: Mem.valid_block m2 bx).
      { eapply Mem.valid_block_free_2; eauto. }
      specialize (mjoin_contents0 bx ox HV). inv mjoin_contents0.
      + apply contents_join_l; eauto.
        * intros k p. specialize (H0 k p). split; intros.
          -- exploit Mem.perm_free_3. apply HF. eauto. intros A.
             eapply Mem.perm_free_1; eauto.
             destruct (peq bx b). 2: eauto.
             destruct (zle lo ox). 2: lia.
             destruct (zlt ox hi). 2: lia.
             subst. exfalso. eapply Mem.perm_free_2. apply HF.
             instantiate (1 := ox). lia. eauto.
             apply H0; eauto.
          -- exploit Mem.perm_free_3. apply e. eauto. intros.
             eapply Mem.perm_free_1; eauto.
             destruct (peq bx b). 2: eauto.
             destruct (zle lo ox). 2: lia.
             destruct (zlt ox hi). 2: lia.
             subst. exfalso. eapply Mem.perm_free_2. apply e.
             instantiate (1 := ox). lia. eauto.
             apply H0; eauto.
        * eapply Mem.free_result in HF.
          eapply Mem.free_result in e. subst.
          apply H2.
        * eauto with mem.
      + apply contents_join_r; eauto.
        * intros A. apply H.
          eapply Mem.perm_free_3; eauto.
        * intros k p. specialize (H0 k p). rewrite H0.
          assert (bx <> b \/ ox < lo \/ hi <= ox).
          {
             destruct (peq bx b). 2: eauto.
             destruct (zle lo ox). 2: lia.
             destruct (zlt ox hi). 2: lia.
             exfalso. subst. apply H.
             apply Mem.free_range_perm in HF.
             eauto with mem.
          }
          split; intros.
          -- eapply Mem.perm_free_1; eauto.
          -- eapply Mem.perm_free_3; eauto.
        * eapply Mem.free_result in HF. subst. apply H1.
        * eapply Mem.free_result in HF.
          eapply Mem.free_result in e. subst.
          apply H2.
    - destruct H.
      apply Mem.nextblock_free in HF.
      apply Mem.nextblock_free in e. congruence.
    - destruct H.
      exploit Mem.nextblock_free. apply HF. intros C.
      apply Mem.free_alloc_flag in HF.
      apply Mem.free_alloc_flag in e.
      inv mjoin_alloc_flag0.
      + apply alloc_flag_join_l; eauto. congruence.
      + apply alloc_flag_join_r; eauto. congruence.
      + apply alloc_flag_join_x; eauto.
    - intros bx ox Hx. destruct H.
      assert (Hvb: ~Mem.valid_block m2 bx).
      { intros contra. apply Hx. eauto with mem. }
      specialize (mjoin_empty_contents0 bx ox Hvb).
      inv mjoin_empty_contents0. constructor; eauto.
      + intros p. apply H0. eauto with mem.
      + intros p. apply H1. eauto with mem.
      + replace (Mem.mem_contents m0)
          with (Mem.mem_contents m1); eauto.
        unfold Mem.free in HF.
        destruct Mem.range_perm_dec; try congruence. inv HF.
        reflexivity.
      + replace (Mem.mem_contents x)
          with (Mem.mem_contents m2); eauto.
        unfold Mem.free in e.
        destruct Mem.range_perm_dec; try congruence. inv e.
        reflexivity.
      + intros p. apply H6. eauto with mem.
  Qed.
  Opaque Mem.free.

  Instance free_list_join:
    Monotonic
      (@Mem.free_list)
      (join m ++> - ==> option_le (join m)).
  Proof.
    repeat rstep. revert x y H. rename x0 into l. induction l.
    - constructor. eauto.
    - intros. destruct a. destruct p.
      cbn. destruct (Mem.free x b z0 z) eqn: HX. 2: constructor.
      transport HX. rewrite H0. eauto.
  Qed.

  Local Transparent Mem.alloc.
  Instance alloc_join:
    Monotonic
      (@Mem.alloc)
      (join m ++> - ==> - ==> option_le ((join m) * eq)).
  Proof.
    repeat rstep.
    rename x0 into lo. rename x1 into hi.
    rename x into m1. rename y into m2.
    destruct (Mem.alloc m1 lo hi) eqn: HA; try constructor.
    destruct p as (m1' & b1).
    destruct H.
    exploit Mem.alloc_flag_alloc1; eauto. intros A.
    inv mjoin_alloc_flag0; try congruence.
    edestruct Mem.alloc_succeed as [[m2' b2] HB].
    apply H1. rewrite HB. constructor.
    assert (HNB: Mem.nextblock m1 = Mem.nextblock m2).
    { apply Pos.max_r in H2. congruence. }
    assert (X: b1 = b2).
    {
      apply Mem.alloc_result in HA.
      apply Mem.alloc_result in HB.
      congruence.
    }
    subst; split; cbn; eauto. constructor.
    - intros bx ox Hx. destruct (peq bx b2).
      + subst.
        assert (Hy: ~Mem.valid_block m2 b2).
        { eapply Mem.fresh_block_alloc; eauto. }
        specialize (mjoin_empty_contents0 b2 ox Hy).
        apply contents_join_l; eauto with mem.
        * intros X. exploit Mem.perm_valid_block. apply X.
          intros Y. unfold Mem.valid_block, Plt in *.
          apply Mem.alloc_result in HB. subst.
          rewrite mjoin_nextblock0 in Y. lia.
        * intros k p. split; intros; eauto with mem.
        * inv mjoin_empty_contents0; eauto.
        * unfold Mem.alloc in *.
          destruct (Mem.alloc_flag m1); try congruence.
          destruct (Mem.alloc_flag m2); try congruence.
          inv HA. inv HB. cbn. rewrite HNB at 3.
          rewrite !PMap.gss. reflexivity.
      + assert (HV: Mem.valid_block m2 bx).
          { exploit Mem.valid_block_alloc_inv; eauto.
            intros [|]; easy. }
          specialize (mjoin_contents0 bx ox HV). inv mjoin_contents0.
          * apply contents_join_l; eauto.
            -- intros k p. split; intros.
               ++ exploit Mem.perm_alloc_inv. apply HA. eauto.
                  destruct eq_block; try easy.
                   intros. eapply Mem.perm_alloc_1; eauto. firstorder.
               ++ exploit Mem.perm_alloc_inv. apply HB. eauto.
                   destruct eq_block; try easy.
                   intros. eapply Mem.perm_alloc_1; eauto. firstorder.
             -- unfold Mem.alloc in HA, HB.
                rewrite A in HA. inv HA.
                rewrite H1 in HB. inv HB. cbn.
                rewrite HNB.
                destruct (peq bx (Mem.nextblock m2)).
                ++ subst. rewrite !PMap.gss. reflexivity.
                ++ rewrite !PMap.gso; eauto.
             -- eauto with mem.
          * apply contents_join_r; eauto.
            -- intros X. apply H3. eauto with mem.
            -- intros k p. rewrite H4.
               split; intros; eauto with mem.
            -- unfold Mem.alloc in HA. rewrite A in HA. inv HA.
               cbn. rewrite PMap.gso; eauto.
            -- rewrite H6.
               unfold Mem.alloc in HB. rewrite H1 in HB.
               inv HB. cbn. rewrite PMap.gso; eauto.
    - apply Mem.nextblock_alloc in HA.
        apply Mem.nextblock_alloc in HB.
        rewrite HA. rewrite HB. rewrite HNB.
        symmetry. apply Pos.max_r.
        etransitivity; eauto. rewrite HNB. lia.
    - apply alloc_flag_join_l; eauto.
      + apply Mem.alloc_flag_alloc2 in HA. easy.
      + apply Mem.alloc_flag_alloc2 in HB. easy.
      + apply Mem.nextblock_alloc in HA. rewrite HA.
        etransitivity; eauto. rewrite HNB. lia.
    - intros b ofs Hb. assert (Hvb: ~Mem.valid_block m2 b).
      { intros v. apply Hb. eauto with mem. }
      assert (b <> b2).
      { intros e. subst. apply Hb. eauto with mem. }
      specialize (mjoin_empty_contents0 b ofs Hvb).
      inv mjoin_empty_contents0. constructor; eauto.
      + intros p. apply H5. eauto with mem.
      + intros p. apply H6. eauto with mem.
      + replace ((Mem.mem_contents m1') # b)
          with ((Mem.mem_contents m1) # b); eauto.
        unfold Mem.alloc in HA. rewrite A in HA. inv HA.
        cbn. rewrite PMap.gso; eauto.
      + replace ((Mem.mem_contents m2') # b)
          with ((Mem.mem_contents m2) # b); eauto.
        unfold Mem.alloc in HB. rewrite H1 in HB. inv HB.
        cbn. rewrite PMap.gso; eauto.
      + intros v. apply H11.
        eapply Mem.valid_block_alloc_inv in HA; eauto.
        destruct HA as [|]. congruence. eauto.
  Qed.
  Opaque Mem.alloc.

  Lemma bind_parameters_join:
    Monotonic
      (@bind_parameters)
      (- ==> - ==> join m ++> - ==> - ==> set_le (join m)).
  Proof.
    repeat rstep. intros ? ?. revert y H.
    induction H0.
    - eexists. split. econstructor. eauto.
    - intros. exploit assign_loc_join; eauto.
      intros (? & ? & ?).
      exploit IHbind_parameters. eauto.
      intros (? & ? & ?).
      eexists. split; eauto. econstructor; eauto.
  Qed.

  Lemma alloc_variables_join:
    Monotonic
      (@alloc_variables)
      (- ==> - ==> join m ++> - ==> - ==> set_le (join m)).
  Proof.
    repeat rstep. intros ? ?. revert y H.
    induction H0.
    - intros. eexists. split. econstructor. eauto.
    - intros. transport H. destruct x0. destruct H3. cbn in *. subst.
      exploit IHalloc_variables. eauto.
      intros (? & ? & ?).
      eexists. split; eauto. econstructor; eauto.
  Qed.

End JOIN_PROP.
