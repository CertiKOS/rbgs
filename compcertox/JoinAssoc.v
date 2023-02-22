From compcert Require Import Coqlib Maps Memory Join.

(** * Associativity properties for [join] *)

(** In our relational approach to separation algebras, associativity
  proceeds in two steps. First, we show that three shares join one way
  if and only if they join the other way. *)

Lemma join_associative m1 m2 m3 m12 m23 m123:
  join m1 m2 m12 -> join m12 m3 m123 -> join m2 m3 m23 -> join m1 m23 m123.
Proof.
  intros [H12c H12n H12f] [H123c H123n H123f] [H23c H23n H23f].
  assert (Hanyperm: forall m b ofs k p, Mem.perm m b ofs k p -> Mem.perm m b ofs Max Nonempty).
  {
    clear; intros.
    cut (Mem.perm m b ofs k Nonempty).
    - destruct k; eauto using Mem.perm_cur_max.
    - eapply Mem.perm_implies; eauto; try constructor.
  }
  split.
  - (* contents *)
    clear - Hanyperm H12c H123c H23c.
    intros b ofs.
    specialize (H12c b ofs); specialize (H123c b ofs); specialize (H23c b ofs).
    inv H12c; inv H123c; inv H23c.
    + left; auto; try congruence.
      intros k p; specialize (H0 k p); specialize (H4 k p); specialize (H8 k p). firstorder.
    + left; auto; try congruence.
      intros k p.
      split.
      * intro. elim H3. eapply Hanyperm. apply H0, H8, H11. 
      * intro. elim H7. eapply Hanyperm. apply H4, H11.
    + left; auto; try congruence.
      intros k p.
      split.
      * intro. elim H3. eapply Hanyperm. apply H8, H11. 
      * intro. elim H7. eapply Hanyperm. apply H0, H4, H11.
    + left; auto; try congruence.
      intros k p. rewrite <- H4, <- H0, <- H8. reflexivity.
    + left; auto; try congruence.
      * rewrite H0. auto.
      * intros k p. rewrite <- H8, H4. reflexivity.
    + left; auto; try congruence.
      * rewrite H0. auto.
      * intros k p. split.
        -- intro. elim H. apply H8. eauto.
        -- intro. elim H7. apply H4. eauto.
    + right; auto; try congruence.
      * rewrite <- H8. auto.
      * intros. rewrite H0, H4. reflexivity.
    + right; auto; try congruence.
      * rewrite <- H8; auto.
      * intros. rewrite H0, H4. reflexivity.
  - (* nextblock *)
    clear - H12n H123n H23n.
    rewrite H123n, H12n, H23n, Pos.max_assoc.
    reflexivity.
  - (* alloc flag *)
    clear - H12f H123f H23f.
    inv H12f; inv H123f; inv H23f; try congruence; constructor.
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
  rewrite !Mem.nextblock_noaccess by xomega.
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
Qed.

Lemma mem_combine_perm_r m1 m2 b ofs k p:
  Mem.perm m2 b ofs k p -> Mem.perm (mem_combine m1 m2) b ofs k p.
Proof.
  unfold Mem.perm. cbn. rewrite PMap_gcombine.
  destruct (_ !! b ofs k); cbn; firstorder.
  destruct (_ !! b ofs k); cbn; firstorder.
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
  intros [H12c H12nb H12a] [H123c H123nb H123a].
  exists (mem_combine m2 m3).
  constructor.
  - (* Contents *)
    clear - H12c H123c.
    intros b ofs. specialize (H12c b ofs). specialize (H123c b ofs).
    inv H123c.
    + (* Location is empty in m12 hence m2 *)
      assert (~ Mem.perm m2 b ofs Max Nonempty) by (inv H12c; firstorder).
      left; auto.
      * intros. rewrite mem_combine_perm_iff_r by auto. reflexivity.
      * inv H12c; congruence.
      * rewrite mem_gcombine.
        replace (ZMap.get ofs (Mem.mem_contents m2) !! b) with Undef by (inv H12c; congruence).
        reflexivity.
    + (* Location is empty in m3 *)
      right; auto.
      * intros. rewrite mem_combine_perm_iff_l by auto. reflexivity.
      * rewrite mem_gcombine, H1.
        clear. destruct ZMap.get; reflexivity.
  - (* Nextblock *)
    reflexivity.
  - (* Alloc flag *)
    cbn. inv H12a; inv H123a; try constructor.
    congruence.
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
