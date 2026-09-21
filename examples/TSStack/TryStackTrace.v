Require Import FMapPositive.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.Wf_nat.
Require Import Coq.PArith.PArith.
Require Import Coq.Logic.Classical_Prop.
Require Import Lia.

Require Import models.EffectSignatures.
Require Import LinCCAL.
Require Import LTS.

Require Import examples.Common.Heap.
Require Import examples.Common.ThreadDomain.
Require Import examples.TSStack.ListPoolSpec.
Require Import examples.TSStack.TryStackAuxSpec.
Require Import examples.TSStack.TryStackAuxGhost.
Require Import examples.TSStack.TryStackSpec.
Require Import examples.TSStack.TryStackLinearization.


(** The trace theorem of the TryStack layer: every well-formed ghost-timed
    TryStackAux state admits a consistent abstract history
    ([TryStackLinearization.consistent]).

    The history is built by induction on the logical clock.  Undoing the
    last recorded event of a well-formed state yields a well-formed state
    with a smaller clock; the history of the smaller state is extended.
    Pushes and snapshots extend trivially.  A removal of [n] inserts the
    abstract pop of [n] at the least position that is _feasible_ (every
    abstractly newer vertex whose push-inv precedes the position is either
    already popped before it or still pending, so that its push-inv can be
    postponed behind the pop) and _safe_ (postponing a push-inv behind the
    pop does not make it abstractly newer than a vertex that is popped later
    while it is still live).

    The construction works with unbounded ranks inside a gap; the ranks are
    compressed to the budget [pos_ok] at the very end, using a map from
    clock values to the abstract events they key. *)
Module TryStackTrace.
  Import LTSSpec.
  Import LinCCALBase.
  Import ListPoolSpec.
  Import TryStackAuxSpec.
  Import TryStackAuxGhost.
  Import TryStackLinearization.

  Section Trace.
    Context {A : Type}.

    Local Opaque node_eq_dec.

    (** * Abstract consistency

        The same conditions as [consistent], without the rank budget, with
        the push response of [m] understood to follow every abstract event
        of gap [r_m], and without speculative pops.  [a_total] and [a_nd]
        are the additional induction invariants: every vertex has an
        abstract push-inv, and a vertex that is not popped is abstractly
        newer than a completed vertex only if it is concretely newer or the
        completed vertex was popped before its push-inv. *)
    Record acons (s : @TryStackAuxState A) (h : History) : Prop := {
      a_inv_placed : forall n p,
        h_inv h n = Some p ->
        fst p < tsa_now s /\
        (exists i, tsa_node_inv s n = Some i /\ i <= fst p) /\
        (forall r, tsa_node_ret s n = Some r -> fst p <= r);
      a_total : forall n i,
        tsa_node_inv s n = Some i -> exists p, h_inv h n = Some p;
      a_pop_placed : forall n p a,
        h_pop h n = Some (pair p a) ->
        fst p < tsa_now s /\
        (exists q, h_inv h n = Some q /\ pos_lt q p) /\
        (exists st rt, tsa_removals s n = Some (pair (pair a st) rt) /\
          st <= fst p /\ fst p <= rt);
      a_removal_popped : forall n a st rt,
        tsa_removals s n = Some (pair (pair a st) rt) ->
        exists p, h_pop h n = Some (pair p a);
      a_pop_top : forall n p a x q r,
        h_pop h n = Some (pair p a) ->
        h_inv h x = Some q -> pos_lt q p ->
        tsa_node_ret s n = Some r -> r < fst q ->
        exists p' a', h_pop h x = Some (pair p' a') /\ pos_lt p' p;
      a_inv_unique : forall n m p,
        h_inv h n = Some p -> h_inv h m = Some p -> n = m;
      a_pop_unique : forall n m p a b,
        h_pop h n = Some (pair p a) -> h_pop h m = Some (pair p b) -> n = m;
      a_inv_pop_distinct : forall n m p a,
        h_inv h n = Some p -> h_pop h m = Some (pair p a) -> False;
      a_nd : forall x i m r q,
        h_pop h x = None ->
        tsa_node_inv s x = Some i -> tsa_node_ret s m = Some r -> i <= r ->
        h_inv h x = Some q -> r < fst q ->
        exists p' a', h_pop h m = Some (pair p' a') /\ pos_lt p' q
    }.

    (** The key map: which abstract event a clock value keys.  Push-invs
        are keyed by their concrete time, pops by the snapshot time of the
        removal. *)
    Definition KeyMap : Type := nat -> option (LPNodeId * bool).

    Definition key_spec (s : @TryStackAuxState A) (kn : KeyMap) : Prop :=
      (forall t x, kn t = Some (pair x true) <-> tsa_node_inv s x = Some t) /\
      (forall t n, kn t = Some (pair n false) <->
        exists a rt, tsa_removals s n = Some (pair (pair a t) rt)).

    (** * Positions *)

    Lemma pos_lt_lex g1 k1 g2 k2 :
      pos_lt (pair g1 k1) (pair g2 k2) <-> g1 < g2 \/ (g1 = g2 /\ k1 < k2).
    Proof. unfold pos_lt; simpl. tauto. Qed.

    Lemma pos_le_refl p : pos_le p p.
    Proof. right. reflexivity. Qed.

    Lemma pos_lt_le_trans p q r : pos_lt p q -> pos_le q r -> pos_lt p r.
    Proof. intros H [H'| ->]; [eapply pos_lt_trans; eauto|exact H]. Qed.

    Lemma pos_le_lt_trans p q r : pos_le p q -> pos_lt q r -> pos_lt p r.
    Proof. intros [H| ->] H'; [eapply pos_lt_trans; eauto|exact H']. Qed.

    Lemma pos_le_trans p q r : pos_le p q -> pos_le q r -> pos_le p r.
    Proof.
      intros [H|H] [H'|H'].
      - left. eapply pos_lt_trans; eauto.
      - subst. left. exact H.
      - subst. left. exact H'.
      - subst. right. reflexivity.
    Qed.

    Lemma pos_not_lt_le p q : ~ pos_lt p q -> pos_le q p.
    Proof.
      intro H. destruct (pos_trichotomy p q) as [H1|[H1|H1]]; [contradiction| |].
      - right. symmetry. exact H1.
      - left. exact H1.
    Qed.

    Lemma pos_lt_asym p q : pos_lt p q -> ~ pos_lt q p.
    Proof. intros H1 H2. apply (pos_lt_irrefl p). eapply pos_lt_trans; eauto. Qed.

    Lemma pos_le_antisym p q : pos_le p q -> pos_le q p -> p = q.
    Proof.
      intros [H1|H1] [H2|H2]; auto.
      exfalso. eapply pos_lt_asym; eauto.
    Qed.

    (** Least element of a nonempty set of positions (classically). *)
    Lemma nat_least (P : nat -> Prop) :
      (exists n, P n) -> exists n, P n /\ forall m, P m -> n <= m.
    Proof.
      intros Hex.
      destruct (dec_inh_nat_subset_has_unique_least_element P (fun n => classic (P n)) Hex)
        as (n & [Hn Hleast] & _).
      exists n. split; [exact Hn|exact Hleast].
    Qed.

    Lemma pos_least (P : Pos -> Prop) :
      (exists q, P q) -> exists p, P p /\ forall q, P q -> pos_le p q.
    Proof.
      intros (q0 & Hq0).
      destruct (nat_least (fun g => exists k, P (pair g k))) as (g & (k0 & Hgk0) & Hgleast).
      { exists (fst q0), (snd q0). destruct q0. exact Hq0. }
      destruct (nat_least (fun k => P (pair g k))) as (k & Hk & Hkleast).
      { exists k0. exact Hgk0. }
      exists (pair g k). split; [exact Hk|].
      intros [g' k'] Hq'. unfold pos_le, pos_lt; simpl.
      assert (Hg : g <= g') by (apply Hgleast; eauto).
      destruct (Nat.eq_dec g g') as [->|Hne].
      - assert (Hkk : k <= k') by (apply Hkleast; exact Hq').
        destruct (Nat.eq_dec k k') as [->|Hnek]; [right; reflexivity|left; right; split; [reflexivity|lia]].
      - left. left. lia.
    Qed.

    (** * Rank compression

        [cnt h kn g r t] counts the clock values [t' <= t] keying an
        abstract event of gap [g] with rank below [r]. *)
    Definition ev_pos (h : History) (yb : LPNodeId * bool) : option Pos :=
      if snd yb then h_inv h (fst yb)
      else match h_pop h (fst yb) with Some pa => Some (fst pa) | None => None end.

    Definition before_b (h : History) (kn : KeyMap) (g r t : nat) : bool :=
      match kn t with
      | Some yb =>
          match ev_pos h yb with
          | Some q => (Nat.eqb (fst q) g) && (Nat.ltb (snd q) r)
          | None => false
          end
      | None => false
      end.

    Fixpoint cnt (h : History) (kn : KeyMap) (g r t : nat) : nat :=
      match t with
      | 0 => if before_b h kn g r 0 then 1 else 0
      | S t' => cnt h kn g r t' + (if before_b h kn g r (S t') then 1 else 0)
      end.

    Lemma cnt_bound h kn g r t : cnt h kn g r t <= S t.
    Proof.
      induction t as [|t IH]; simpl.
      - destruct (before_b h kn g r 0); lia.
      - destruct (before_b h kn g r (S t)); lia.
    Qed.

    Lemma cnt_mono h kn g r1 r2 t :
      r1 <= r2 -> cnt h kn g r1 t <= cnt h kn g r2 t.
    Proof.
      intros Hle.
      assert (Hb : forall t', before_b h kn g r1 t' = true -> before_b h kn g r2 t' = true).
      { intros t'. unfold before_b. destruct (kn t') as [yb|]; [|discriminate].
        destruct (ev_pos h yb) as [q|]; [|discriminate].
        rewrite !Bool.andb_true_iff, !Nat.ltb_lt. intros [H1 H2]. split; [exact H1|lia]. }
      induction t as [|t IH]; simpl.
      - destruct (before_b h kn g r1 0) eqn:E1; [rewrite (Hb _ E1)|destruct (before_b h kn g r2 0)]; lia.
      - destruct (before_b h kn g r1 (S t)) eqn:E1; [rewrite (Hb _ E1)|destruct (before_b h kn g r2 (S t))]; lia.
    Qed.

    Lemma cnt_strict h kn g r1 r2 t t0 :
      r1 <= r2 -> t0 <= t ->
      before_b h kn g r1 t0 = false -> before_b h kn g r2 t0 = true ->
      cnt h kn g r1 t < cnt h kn g r2 t.
    Proof.
      intros Hle Ht0 Hf Htr.
      induction t as [|t IH]; simpl.
      - assert (t0 = 0) by lia. subst t0. rewrite Hf, Htr. lia.
      - destruct (Nat.eq_dec t0 (S t)) as [->|Hne].
        + rewrite Hf, Htr. pose proof (cnt_mono h kn g r1 r2 t Hle). lia.
        + assert (Hlt : cnt h kn g r1 t < cnt h kn g r2 t) by (apply IH; lia).
          destruct (before_b h kn g r1 (S t)) eqn:E1.
          * assert (before_b h kn g r2 (S t) = true).
            { revert E1. unfold before_b. destruct (kn (S t)) as [yb|]; [|discriminate].
              destruct (ev_pos h yb) as [q|]; [|discriminate].
              rewrite !Bool.andb_true_iff, !Nat.ltb_lt. intros [H1 H2]. split; [exact H1|lia]. }
            rewrite H. lia.
          * destruct (before_b h kn g r2 (S t)); lia.
    Qed.

    Definition compress_pos (h : History) (kn : KeyMap) (q : Pos) : Pos :=
      pair (fst q) (cnt h kn (fst q) (snd q) (fst q)).

    Definition compress (h : History) (kn : KeyMap) : History :=
      {| h_inv := fun n => match h_inv h n with
                           | Some q => Some (compress_pos h kn q)
                           | None => None
                           end;
         h_pop := fun n => match h_pop h n with
                           | Some pa => Some (pair (compress_pos h kn (fst pa)) (snd pa))
                           | None => None
                           end |}.

    (** An abstract event at position [q] keyed by [t <= fst q]. *)
    Definition keyed (h : History) (kn : KeyMap) (q : Pos) : Prop :=
      exists t yb, t <= fst q /\ kn t = Some yb /\ ev_pos h yb = Some q.

    Lemma keyed_before h kn q r t yb :
      kn t = Some yb -> ev_pos h yb = Some q ->
      before_b h kn (fst q) r t = true <-> snd q < r.
    Proof.
      intros Hk He. unfold before_b. rewrite Hk, He.
      rewrite Bool.andb_true_iff, Nat.eqb_eq, Nat.ltb_lt. tauto.
    Qed.

    Lemma compress_lt h kn q1 q2 :
      keyed h kn q1 -> pos_lt q1 q2 ->
      pos_lt (compress_pos h kn q1) (compress_pos h kn q2).
    Proof.
      intros (t & yb & Ht & Hk & He) Hlt.
      unfold compress_pos. apply pos_lt_lex.
      destruct (Nat.eq_dec (fst q1) (fst q2)) as [Heq|Hne].
      - right. split; [exact Heq|]. rewrite <- Heq.
        assert (Hk2 : snd q1 < snd q2).
        { destruct q1 as [g1 k1], q2 as [g2 k2]. unfold pos_lt in Hlt. simpl in Hlt, Heq. simpl.
          destruct Hlt as [Hlt|[_ Hlt]]; lia. }
        apply (cnt_strict h kn (fst q1) (snd q1) (snd q2) (fst q1) t); try lia.
        + destruct (before_b h kn (fst q1) (snd q1) t) eqn:E; [|reflexivity].
          rewrite (keyed_before h kn q1 (snd q1) t yb Hk He) in E. lia.
        + rewrite (keyed_before h kn q1 (snd q2) t yb Hk He). exact Hk2.
      - left. destruct q1 as [g1 k1], q2 as [g2 k2]. unfold pos_lt in Hlt. simpl in Hlt, Hne. simpl.
        destruct Hlt as [Hlt|[Hlt _]]; lia.
    Qed.

    Lemma compress_lt_inv h kn q1 q2 :
      keyed h kn q1 -> keyed h kn q2 ->
      pos_lt (compress_pos h kn q1) (compress_pos h kn q2) -> pos_lt q1 q2.
    Proof.
      intros H1 H2 Hlt.
      destruct (pos_trichotomy q1 q2) as [H|[H|H]]; [exact H| |].
      - subst. exfalso. eapply pos_lt_irrefl; eauto.
      - exfalso. apply (compress_lt h kn q2 q1 H2) in H. eapply pos_lt_asym; eauto.
    Qed.

    Lemma compress_inj h kn q1 q2 :
      keyed h kn q1 -> keyed h kn q2 ->
      compress_pos h kn q1 = compress_pos h kn q2 -> q1 = q2.
    Proof.
      intros H1 H2 Heq.
      destruct (pos_trichotomy q1 q2) as [H|[H|H]]; [|exact H|].
      - apply (compress_lt h kn q1 q2 H1) in H. rewrite Heq in H.
        exfalso. eapply pos_lt_irrefl; eauto.
      - apply (compress_lt h kn q2 q1 H2) in H. rewrite Heq in H.
        exfalso. eapply pos_lt_irrefl; eauto.
    Qed.

    Lemma compress_ok h kn q : pos_ok (compress_pos h kn q).
    Proof.
      unfold pos_ok, compress_pos; simpl.
      pose proof (cnt_bound h kn (fst q) (snd q) (fst q)). lia.
    Qed.

    Lemma compress_fst h kn q : fst (compress_pos h kn q) = fst q.
    Proof. reflexivity. Qed.

    (** [ret_pos r] precedes a compressed position exactly when the gap is
        above [r]. *)
    Lemma ret_pos_lt_compress h kn r q :
      pos_lt (ret_pos r) (compress_pos h kn q) <-> r < fst q.
    Proof.
      unfold ret_pos, compress_pos, pos_lt; simpl.
      pose proof (cnt_bound h kn (fst q) (snd q) (fst q)). lia.
    Qed.

    (** Every event of an abstractly consistent history is keyed. *)
    Lemma acons_inv_keyed s h kn n q :
      acons s h -> key_spec s kn -> h_inv h n = Some q -> keyed h kn q.
    Proof.
      intros Hc [Hkinv _] Hq.
      destruct (a_inv_placed _ _ Hc _ _ Hq) as (_ & (i & Hi & Hile) & _).
      exists i, (pair n true). repeat split; [exact Hile| |].
      - apply Hkinv. exact Hi.
      - unfold ev_pos; simpl. exact Hq.
    Qed.

    Lemma acons_pop_keyed s h kn n p a :
      acons s h -> key_spec s kn -> h_pop h n = Some (pair p a) -> keyed h kn p.
    Proof.
      intros Hc [_ Hkpop] Hp.
      destruct (a_pop_placed _ _ Hc _ _ _ Hp) as (_ & _ & (st & rt & Hrem & Hst & _)).
      exists st, (pair n false). repeat split; [exact Hst| |].
      - apply Hkpop. eauto.
      - unfold ev_pos; simpl. rewrite Hp. reflexivity.
    Qed.

    Lemma compress_consistent s h kn :
      tsa_ghost_wf s -> acons s h -> key_spec s kn ->
      consistent s (compress h kn).
    Proof.
      intros Hwf Hc Hk.
      assert (Hinv : forall n q, h_inv (compress h kn) n = Some q <->
        exists q0, h_inv h n = Some q0 /\ q = compress_pos h kn q0).
      { intros n q. simpl. destruct (h_inv h n) as [q0|]; split.
        - intro H. inversion H; subst. eauto.
        - intros (q1 & H1 & ->). inversion H1; subst. reflexivity.
        - discriminate.
        - intros (q1 & H1 & _). discriminate. }
      assert (Hpop : forall n p a, h_pop (compress h kn) n = Some (pair p a) <->
        exists p0, h_pop h n = Some (pair p0 a) /\ p = compress_pos h kn p0).
      { intros n p a. simpl. destruct (h_pop h n) as [[p0 a0]|]; split.
        - intro H. inversion H; subst. simpl. eauto.
        - intros (p1 & H1 & ->). inversion H1; subst. reflexivity.
        - discriminate.
        - intros (p1 & H1 & _). discriminate. }
      constructor.
      - intros n p Hp. apply Hinv in Hp. destruct Hp as (q0 & Hq0 & ->).
        destruct (a_inv_placed _ _ Hc _ _ Hq0) as (Hnow & Hi & Hret).
        split; [apply compress_ok|]. split; [rewrite compress_fst; exact Hnow|].
        split; [rewrite compress_fst; exact Hi|].
        intros r Hr. rewrite compress_fst. apply Hret. exact Hr.
      - intros n r Hr. destruct (wf_ret_inv _ Hwf _ _ Hr) as (i & Hi & _).
        destruct (a_total _ _ Hc _ _ Hi) as [p Hp].
        exists (compress_pos h kn p). apply Hinv. eauto.
      - intros n p a Hp. apply Hpop in Hp. destruct Hp as (p0 & Hp0 & ->).
        destruct (a_pop_placed _ _ Hc _ _ _ Hp0) as (Hnow & (q & Hq & Hqlt) & (st & rt & Hrem & Hst & Hrt)).
        split; [apply compress_ok|]. split; [rewrite compress_fst; exact Hnow|].
        split.
        + exists (compress_pos h kn q). split; [apply Hinv; eauto|].
          apply compress_lt; [eapply acons_inv_keyed; eauto|exact Hqlt].
        + left. exists st, rt. rewrite compress_fst. auto.
      - intros n a st rt Hrem.
        destruct (a_removal_popped _ _ Hc _ _ _ _ Hrem) as [p Hp].
        exists (compress_pos h kn p). apply Hpop. eauto.
      - intros n m p q a Hn Hm Hrn Hrm. exfalso.
        apply Hpop in Hn. destruct Hn as (p0 & Hp0 & _).
        destruct (a_pop_placed _ _ Hc _ _ _ Hp0) as (_ & _ & (st & rt & Hrem & _)).
        congruence.
      - intros n p a x q Hp Hx Hlt Hedge.
        apply Hpop in Hp. destruct Hp as (p0 & Hp0 & ->).
        apply Hinv in Hx. destruct Hx as (q0 & Hq0 & ->).
        destruct Hedge as (p1 & q1 & Hp1 & (r & Hr & ->) & Hlt1).
        apply Hinv in Hp1. destruct Hp1 as (q2 & Hq2 & Heq).
        rewrite Hq0 in Hq2. inversion Hq2; subst q2. subst p1.
        apply ret_pos_lt_compress in Hlt1.
        assert (Hlt0 : pos_lt q0 p0).
        { eapply compress_lt_inv; eauto; [eapply acons_inv_keyed|eapply acons_pop_keyed]; eauto. }
        destruct (a_pop_top _ _ Hc _ _ _ _ _ _ Hp0 Hq0 Hlt0 Hr Hlt1) as (p' & a' & Hp' & Hlt').
        exists (compress_pos h kn p'), a'. split; [apply Hpop; eauto|].
        apply compress_lt; [eapply acons_pop_keyed; eauto|exact Hlt'].
      - intros n m p Hn Hm. apply Hinv in Hn. apply Hinv in Hm.
        destruct Hn as (q1 & Hq1 & ->). destruct Hm as (q2 & Hq2 & Heq).
        apply compress_inj in Heq; [|eapply acons_inv_keyed; eauto|eapply acons_inv_keyed; eauto].
        subst q2. eapply a_inv_unique; eauto.
      - intros n m p a b Hn Hm. apply Hpop in Hn. apply Hpop in Hm.
        destruct Hn as (q1 & Hq1 & ->). destruct Hm as (q2 & Hq2 & Heq).
        apply compress_inj in Heq; [|eapply acons_pop_keyed; eauto|eapply acons_pop_keyed; eauto].
        subst q2. eapply a_pop_unique; eauto.
      - intros n m p a Hn Hm. apply Hinv in Hn. apply Hpop in Hm.
        destruct Hn as (q1 & Hq1 & ->). destruct Hm as (q2 & Hq2 & Heq).
        apply compress_inj in Heq; [|eapply acons_inv_keyed; eauto|eapply acons_pop_keyed; eauto].
        subst q2. eapply a_inv_pop_distinct; eauto.
    Qed.


    (** * Undoing the last recorded event of a well-formed state *)

    Definition with_now (s : @TryStackAuxState A) (T : nat) : @TryStackAuxState A :=
      {| tsa_vertices := tsa_vertices s;
         tsa_edges := tsa_edges s;
         tsa_snapshots := tsa_snapshots s;
         tsa_pending_pushes := tsa_pending_pushes s;
         tsa_garbage := tsa_garbage s;
         tsa_now := T;
         tsa_node_inv := tsa_node_inv s;
         tsa_node_ret := tsa_node_ret s;
         tsa_snap_time := tsa_snap_time s;
         tsa_removals := tsa_removals s |}.

    Definition undo_inv (s : @TryStackAuxState A) (x : LPNodeId) (T : nat) : @TryStackAuxState A :=
      {| tsa_vertices := fun m => if node_eq_dec m x then None else tsa_vertices s m;
         tsa_edges := fun m1 m2 => tsa_edges s m1 m2 /\ m1 <> x;
         tsa_snapshots := tsa_snapshots s;
         tsa_pending_pushes := TMap.remove (fst x) (tsa_pending_pushes s);
         tsa_garbage := tsa_garbage s;
         tsa_now := T;
         tsa_node_inv := fun m => if node_eq_dec m x then None else tsa_node_inv s m;
         tsa_node_ret := tsa_node_ret s;
         tsa_snap_time := tsa_snap_time s;
         tsa_removals := tsa_removals s |}.

    Definition undo_ret (s : @TryStackAuxState A) (x : LPNodeId) (T : nat) : @TryStackAuxState A :=
      {| tsa_vertices := tsa_vertices s;
         tsa_edges := tsa_edges s;
         tsa_snapshots := tsa_snapshots s;
         tsa_pending_pushes := TMap.add (fst x) (snd x) (tsa_pending_pushes s);
         tsa_garbage := tsa_garbage s;
         tsa_now := T;
         tsa_node_inv := tsa_node_inv s;
         tsa_node_ret := fun m => if node_eq_dec m x then None else tsa_node_ret s m;
         tsa_snap_time := tsa_snap_time s;
         tsa_removals := tsa_removals s |}.

    Definition undo_snap (s : @TryStackAuxState A) (a : tid) (T : nat) : @TryStackAuxState A :=
      {| tsa_vertices := tsa_vertices s;
         tsa_edges := tsa_edges s;
         tsa_snapshots := TMap.remove a (tsa_snapshots s);
         tsa_pending_pushes := tsa_pending_pushes s;
         tsa_garbage := tsa_garbage s;
         tsa_now := T;
         tsa_node_inv := tsa_node_inv s;
         tsa_node_ret := tsa_node_ret s;
         tsa_snap_time := TMap.remove a (tsa_snap_time s);
         tsa_removals := tsa_removals s |}.

    Definition undo_rem (s : @TryStackAuxState A) (n : LPNodeId) (T : nat) : @TryStackAuxState A :=
      {| tsa_vertices := tsa_vertices s;
         tsa_edges := tsa_edges s;
         tsa_snapshots := tsa_snapshots s;
         tsa_pending_pushes := tsa_pending_pushes s;
         tsa_garbage := fun m => tsa_garbage s m /\ m <> n;
         tsa_now := T;
         tsa_node_inv := tsa_node_inv s;
         tsa_node_ret := tsa_node_ret s;
         tsa_snap_time := tsa_snap_time s;
         tsa_removals := fun m => if node_eq_dec m n then None else tsa_removals s m |}.

    (** Recorded times other than [T] are below [T]. *)
    Lemma ghost_time_lt (s : @TryStackAuxState A) T t ev :
      tsa_ghost_wf s -> tsa_now s = S T -> ghost_event_at s t ev -> t <> T -> t < T.
    Proof.
      intros Hwf Hnow Hev Hne. pose proof (ghost_event_now _ _ _ Hwf Hev). lia.
    Qed.

    Lemma ghost_time_lt_other (s : @TryStackAuxState A) T t ev ev' :
      tsa_ghost_wf s -> tsa_now s = S T ->
      ghost_event_at s T ev' -> ghost_event_at s t ev -> ev <> ev' -> t < T.
    Proof.
      intros Hwf Hnow Hev' Hev Hne. apply (ghost_time_lt s T t ev Hwf Hnow Hev).
      intros ->. apply Hne. eapply wf_unique; eauto.
    Qed.

    Ltac undo_simpl :=
      unfold tsa_is_vertex, tsa_is_pending, ghost_event_at in *; simpl in *.

    Lemma with_now_wf (s : @TryStackAuxState A) T :
      tsa_ghost_wf s -> tsa_now s = S T ->
      (forall ev, ~ ghost_event_at s T ev) ->
      tsa_ghost_wf (with_now s T).
    Proof.
      intros Hwf Hnow Hno.
      assert (Hlt : forall t ev, ghost_event_at s t ev -> t < T).
      { intros t ev Hev. apply (ghost_time_lt s T t ev Hwf Hnow Hev).
        intros ->. eapply Hno. exact Hev. }
      constructor; simpl.
      - exact (wf_vertex_inv _ Hwf).
      - intros n i Hi. exact (Hlt i (GInv n) Hi).
      - exact (wf_ret_inv _ Hwf).
      - intros n r Hr. exact (Hlt r (GRet n) Hr).
      - exact (wf_pending _ Hwf).
      - exact (wf_edges _ Hwf).
      - exact (wf_snapshot _ Hwf).
      - intros a t Ht. split; [exact (Hlt t (GSnap a) Ht)|].
        exact (proj2 (wf_snap_time _ Hwf a t Ht)).
      - exact (wf_garbage _ Hwf).
      - intros n actor st rt Hrem.
        destruct (wf_removal _ Hwf _ _ _ _ Hrem) as (H1 & H2 & H3 & H4).
        split; [exact H1|]. split; [|split; assumption].
        apply (Hlt rt (GRem n)). exists actor, st. exact Hrem.
      - intros t ev1 ev2 H1 H2. eapply (wf_unique _ Hwf); eassumption.
      - exact (wf_same_actor _ Hwf).
    Qed.

    Lemma undo_snap_wf (s : @TryStackAuxState A) a T :
      tsa_ghost_wf s -> tsa_now s = S T ->
      TMap.find a (tsa_snap_time s) = Some T ->
      tsa_ghost_wf (undo_snap s a T).
    Proof.
      intros Hwf Hnow Ha.
      assert (Hlt : forall t ev, ghost_event_at s t ev -> ev <> GSnap a -> t < T).
      { intros t ev Hev Hne. eapply ghost_time_lt_other; eauto. exact Ha. }
      constructor; simpl.
      - exact (wf_vertex_inv _ Hwf).
      - intros n i Hi. exact (Hlt i (GInv n) Hi ltac:(discriminate)).
      - exact (wf_ret_inv _ Hwf).
      - intros n r Hr. exact (Hlt r (GRet n) Hr ltac:(discriminate)).
      - exact (wf_pending _ Hwf).
      - exact (wf_edges _ Hwf).
      - intros b N HN. destruct (Pos.eq_dec b a) as [->|Hne].
        + rewrite TMap.grs in HN. discriminate.
        + rewrite TMap.gro in HN by exact Hne. rewrite TMap.gro by exact Hne.
          exact (wf_snapshot _ Hwf b N HN).
      - intros b t Ht. destruct (Pos.eq_dec b a) as [->|Hne].
        + rewrite TMap.grs in Ht. discriminate.
        + rewrite TMap.gro in Ht by exact Hne. rewrite TMap.gro by exact Hne.
          split; [|exact (proj2 (wf_snap_time _ Hwf b t Ht))].
          apply (Hlt t (GSnap b) Ht). intro Heq. inversion Heq. congruence.
      - exact (wf_garbage _ Hwf).
      - intros n actor st rt Hrem.
        destruct (wf_removal _ Hwf _ _ _ _ Hrem) as (H1 & H2 & H3 & H4).
        split; [exact H1|]. split; [|split; assumption].
        apply (Hlt rt (GRem n)); [exists actor, st; exact Hrem|discriminate].
      - intros t ev1 ev2 H1 H2.
        assert (Hsub : forall ev, ghost_event_at (undo_snap s a T) t ev -> ghost_event_at s t ev).
        { intros ev Hev. destruct ev; simpl in *; try exact Hev.
          destruct (Pos.eq_dec actor a) as [->|Hne].
          - rewrite TMap.grs in Hev. discriminate.
          - rewrite TMap.gro in Hev by exact Hne. exact Hev. }
        eapply (wf_unique _ Hwf); apply Hsub; eassumption.
      - exact (wf_same_actor _ Hwf).
    Qed.

    Lemma undo_rem_wf (s : @TryStackAuxState A) n a st T :
      tsa_ghost_wf s -> tsa_now s = S T ->
      tsa_removals s n = Some (pair (pair a st) T) ->
      tsa_ghost_wf (undo_rem s n T).
    Proof.
      intros Hwf Hnow Hn.
      assert (HremT : ghost_event_at s T (GRem n)) by (exists a, st; exact Hn).
      assert (Hlt : forall t ev, ghost_event_at s t ev -> ev <> GRem n -> t < T).
      { intros t ev Hev Hne. eapply ghost_time_lt_other; eauto. }
      assert (Hother : forall m rec, m <> n -> tsa_removals s m = Some rec ->
        exists a' st' rt', rec = pair (pair a' st') rt' /\ rt' < T).
      { intros m [[a' st'] rt'] Hne Hm. exists a', st', rt'. split; [reflexivity|].
        apply (Hlt rt' (GRem m)); [exists a', st'; exact Hm|].
        intro Heq. inversion Heq. congruence. }
      constructor; simpl.
      - exact (wf_vertex_inv _ Hwf).
      - intros m i Hi. exact (Hlt i (GInv m) Hi ltac:(discriminate)).
      - exact (wf_ret_inv _ Hwf).
      - intros m r Hr. exact (Hlt r (GRet m) Hr ltac:(discriminate)).
      - exact (wf_pending _ Hwf).
      - exact (wf_edges _ Hwf).
      - exact (wf_snapshot _ Hwf).
      - intros b t Ht. split; [|exact (proj2 (wf_snap_time _ Hwf b t Ht))].
        exact (Hlt t (GSnap b) Ht ltac:(discriminate)).
      - intros m. destruct (node_eq_dec m n) as [->|Hne].
        + split; [intros [_ H]; congruence|]. intros [rec H]. discriminate.
        + rewrite (wf_garbage _ Hwf m). split.
          * intros [[rec H] _]. eauto.
          * intros [rec H]. split; [eauto|exact Hne].
      - intros m actor st' rt Hrem.
        destruct (node_eq_dec m n) as [->|Hne]; [discriminate|].
        destruct (wf_removal _ Hwf _ _ _ _ Hrem) as (H1 & H2 & H3 & H4).
        split; [exact H1|]. split.
        + destruct (Hother m _ Hne Hrem) as (a' & st'' & rt' & Heq & Hlt').
          inversion Heq; subst. exact Hlt'.
        + split; [exact H3|].
          intros y i Hi Hilt Hedge.
          destruct (H4 y i Hi Hilt Hedge) as (a' & st'' & rt' & Hy & Hlt').
          exists a', st'', rt'. split; [|exact Hlt'].
          destruct (node_eq_dec y n) as [->|Hne'].
          * rewrite Hn in Hy. inversion Hy; subst.
            destruct (Hother m _ Hne Hrem) as (a'' & st3 & rt3 & Heq & Hlt3).
            inversion Heq; subst. lia.
          * exact Hy.
      - intros t ev1 ev2 H1 H2.
        assert (Hsub : forall ev, ghost_event_at (undo_rem s n T) t ev -> ghost_event_at s t ev).
        { intros ev Hev. destruct ev; simpl in *; try exact Hev.
          - destruct Hev as (a' & st' & Hev). destruct (node_eq_dec n0 n); [discriminate|]. eauto.
          - destruct Hev as (a' & rt' & Hev). destruct (node_eq_dec n0 n); [discriminate|]. eauto. }
        eapply (wf_unique _ Hwf); apply Hsub; eassumption.
      - exact (wf_same_actor _ Hwf).
    Qed.

    Lemma undo_inv_wf (s : @TryStackAuxState A) x T :
      tsa_ghost_wf s -> tsa_now s = S T ->
      tsa_node_inv s x = Some T ->
      tsa_ghost_wf (undo_inv s x T).
    Proof.
      intros Hwf Hnow Hx.
      assert (Hlt : forall t ev, ghost_event_at s t ev -> ev <> GInv x -> t < T).
      { intros t ev Hev Hne. eapply ghost_time_lt_other; eauto. exact Hx. }
      assert (Hret_none : tsa_node_ret s x = None).
      { destruct (tsa_node_ret s x) as [r|] eqn:Hr; [|reflexivity].
        destruct (wf_ret_inv _ Hwf _ _ Hr) as (i & Hi & Hlt').
        rewrite Hx in Hi. inversion Hi; subst i.
        pose proof (Hlt r (GRet x) Hr ltac:(discriminate)). lia. }
      assert (Hpend : TMap.find (fst x) (tsa_pending_pushes s) = Some (snd x)).
      { apply (wf_pending _ Hwf x). split; [eauto|exact Hret_none]. }
      assert (Hinv_other : forall m i, tsa_node_inv s m = Some i -> m <> x -> i < T).
      { intros m i Hi Hne. apply (Hlt i (GInv m) Hi). intro Heq. inversion Heq. congruence. }
      constructor; simpl.
      - intros m. unfold tsa_is_vertex. simpl. destruct (node_eq_dec m x) as [->|Hne].
        + split; [intro H; exfalso; apply H; reflexivity|]. intros [i H]. discriminate.
        + exact (wf_vertex_inv _ Hwf m).
      - intros m i Hi. destruct (node_eq_dec m x) as [->|Hne]; [discriminate|].
        exact (Hinv_other m i Hi Hne).
      - intros m r Hr. destruct (node_eq_dec m x) as [->|Hne]; [congruence|].
        exact (wf_ret_inv _ Hwf m r Hr).
      - intros m r Hr. exact (Hlt r (GRet m) Hr ltac:(discriminate)).
      - intros [t l]. unfold tsa_is_pending. simpl. destruct (Pos.eq_dec t (fst x)) as [->|Hne].
        + rewrite TMap.grs. split; [discriminate|].
          intros [[i Hi] Hr]. exfalso.
          destruct (node_eq_dec (pair (fst x) l) x) as [Heq|Hne']; [discriminate Hi|].
          assert (Hp : tsa_is_pending s (pair (fst x) l)).
          { apply (wf_pending _ Hwf). split; [eauto|exact Hr]. }
          unfold tsa_is_pending in Hp; simpl in Hp. rewrite Hpend in Hp. inversion Hp.
          apply Hne'. destruct x; simpl in *; congruence.
        + rewrite TMap.gro by exact Hne.
          destruct (node_eq_dec (t, l) x) as [Heq|Hne'].
          * exfalso. apply Hne. rewrite <- Heq. reflexivity.
          * exact (wf_pending _ Hwf (pair t l)).
      - intros m1 m2. destruct (node_eq_dec m1 x) as [->|Hne].
        + split; [intros [_ H]; congruence|]. intros (r & i & _ & H & _). discriminate.
        + rewrite (wf_edges _ Hwf m1 m2). split.
          * intros [(r & i & Hr & Hi & Hlt') _]. eauto.
          * intros (r & i & Hr & Hi & Hlt'). split; [eauto|exact Hne].
      - intros b N HN. destruct (wf_snapshot _ Hwf b N HN) as (t & Ht & Hmem).
        exists t. split; [exact Ht|]. intro m. rewrite Hmem.
        destruct (node_eq_dec m x) as [->|Hne].
        + split.
          * intros (i & Hi & Hlt'). rewrite Hx in Hi. inversion Hi; subst i.
            pose proof (Hlt t (GSnap b) Ht ltac:(discriminate)). lia.
          * intros (i & Hi & _). discriminate.
        + reflexivity.
      - intros b t Ht. split; [|exact (proj2 (wf_snap_time _ Hwf b t Ht))].
        exact (Hlt t (GSnap b) Ht ltac:(discriminate)).
      - exact (wf_garbage _ Hwf).
      - intros m actor st rt Hrem.
        destruct (wf_removal _ Hwf _ _ _ _ Hrem) as (H1 & H2 & (i & Hi & Hilt) & H4).
        assert (Hne : m <> x).
        { intros ->. rewrite Hx in Hi. inversion Hi; subst i.
          pose proof (Hlt rt (GRem x) ltac:(exists actor, st; exact Hrem) ltac:(discriminate)). lia. }
        split; [exact H1|]. split.
        + apply (Hlt rt (GRem m)); [exists actor, st; exact Hrem|discriminate].
        + split.
          * exists i. destruct (node_eq_dec m x); [congruence|]. auto.
          * intros y i' Hi' Hilt' [Hedge Hney].
            destruct (node_eq_dec y x); [congruence|].
            exact (H4 y i' Hi' Hilt' Hedge).
      - intros t ev1 ev2 H1 H2.
        assert (Hsub : forall ev, ghost_event_at (undo_inv s x T) t ev -> ghost_event_at s t ev).
        { intros ev Hev. destruct ev; simpl in *; try exact Hev.
          destruct (node_eq_dec n x); [discriminate|exact Hev]. }
        eapply (wf_unique _ Hwf); apply Hsub; eassumption.
      - intros actor l1 l2 i1 i2 H1 H2 Hlt'.
        destruct (node_eq_dec (actor, l1) x); [discriminate|].
        destruct (node_eq_dec (actor, l2) x); [discriminate|].
        exact (wf_same_actor _ Hwf actor l1 l2 i1 i2 H1 H2 Hlt').
    Qed.

    Lemma undo_ret_wf (s : @TryStackAuxState A) x T :
      tsa_ghost_wf s -> tsa_now s = S T ->
      tsa_node_ret s x = Some T ->
      tsa_ghost_wf (undo_ret s x T).
    Proof.
      intros Hwf Hnow Hx.
      assert (Hlt : forall t ev, ghost_event_at s t ev -> ev <> GRet x -> t < T).
      { intros t ev Hev Hne. eapply ghost_time_lt_other; eauto. exact Hx. }
      destruct (wf_ret_inv _ Hwf _ _ Hx) as (ix & Hix & Hixlt).
      assert (Hinv_lt : forall m i, tsa_node_inv s m = Some i -> i < T).
      { intros m i Hi. exact (Hlt i (GInv m) Hi ltac:(discriminate)). }
      assert (Hnot_pending : forall l, l <> snd x ->
        tsa_node_inv s (pair (fst x) l) <> None -> tsa_node_ret s (pair (fst x) l) <> None).
      { intros l Hne Hi Hr.
        destruct (tsa_node_inv s (pair (fst x) l)) as [i|] eqn:Hi'; [|congruence].
        destruct (lt_eq_lt_dec i ix) as [[Hlt'|Heq]|Hlt'].
        - destruct (wf_same_actor _ Hwf (fst x) l (snd x) i ix Hi' ltac:(destruct x; exact Hix) Hlt')
            as (r & Hr' & _). congruence.
        - subst i. pose proof (wf_inv_unique _ _ _ _ Hwf Hi' ltac:(destruct x; exact Hix)) as Heq.
          apply Hne. destruct x; simpl in *. inversion Heq. reflexivity.
        - destruct (wf_same_actor _ Hwf (fst x) (snd x) l ix i ltac:(destruct x; exact Hix) Hi' Hlt')
            as (r & Hr' & Hrlt). destruct x; simpl in *. rewrite Hx in Hr'. inversion Hr'; subst r.
          pose proof (Hinv_lt _ _ Hi'). lia. }
      constructor; simpl.
      - exact (wf_vertex_inv _ Hwf).
      - intros m i Hi. exact (Hinv_lt m i Hi).
      - intros m r Hr. destruct (node_eq_dec m x); [discriminate|]. exact (wf_ret_inv _ Hwf m r Hr).
      - intros m r Hr. destruct (node_eq_dec m x) as [->|Hne]; [discriminate|].
        apply (Hlt r (GRet m) Hr). intro Heq. inversion Heq. congruence.
      - intros [t l]. unfold tsa_is_pending. simpl. destruct (Pos.eq_dec t (fst x)) as [->|Hne].
        + rewrite TMap.gss. destruct (node_eq_dec (fst x, l) x) as [Heq|Hne'].
          * split.
            -- intros _. split; [|reflexivity]. rewrite Heq. eauto.
            -- intros _. destruct x; simpl in *. inversion Heq. reflexivity.
          * split.
            -- intro H. inversion H. exfalso. apply Hne'. destruct x; simpl in *; subst; reflexivity.
            -- intros [[i Hi] Hr]. exfalso.
               assert (l <> snd x) by (intro; apply Hne'; destruct x; simpl in *; congruence).
               apply (Hnot_pending l H); congruence.
        + rewrite TMap.gso by exact Hne.
          destruct (node_eq_dec (t, l) x) as [Heq|Hne'].
          * exfalso. apply Hne. rewrite <- Heq. reflexivity.
          * exact (wf_pending _ Hwf (pair t l)).
      - intros m1 m2. rewrite (wf_edges _ Hwf m1 m2).
        destruct (node_eq_dec m2 x) as [->|Hne].
        + split.
          * intros (r & i & Hr & Hi & Hlt'). rewrite Hx in Hr. inversion Hr; subst r.
            pose proof (Hinv_lt _ _ Hi). lia.
          * intros (r & i & Hr & _). discriminate.
        + reflexivity.
      - exact (wf_snapshot _ Hwf).
      - intros b t Ht. split; [|exact (proj2 (wf_snap_time _ Hwf b t Ht))].
        exact (Hlt t (GSnap b) Ht ltac:(discriminate)).
      - exact (wf_garbage _ Hwf).
      - intros m actor st rt Hrem.
        destruct (wf_removal _ Hwf _ _ _ _ Hrem) as (H1 & H2 & H3 & H4).
        split; [exact H1|]. split.
        + apply (Hlt rt (GRem m)); [exists actor, st; exact Hrem|discriminate].
        + split; [exact H3|exact H4].
      - intros t ev1 ev2 H1 H2.
        assert (Hsub : forall ev, ghost_event_at (undo_ret s x T) t ev -> ghost_event_at s t ev).
        { intros ev Hev. destruct ev; simpl in *; try exact Hev.
          destruct (node_eq_dec n x); [discriminate|exact Hev]. }
        eapply (wf_unique _ Hwf); apply Hsub; eassumption.
      - intros actor l1 l2 i1 i2 H1 H2 Hlt'.
        destruct (wf_same_actor _ Hwf actor l1 l2 i1 i2 H1 H2 Hlt') as (r1 & Hr1 & Hr1lt).
        exists r1. split; [|exact Hr1lt].
        destruct (node_eq_dec (actor, l1) x) as [Heq|Hne]; [|exact Hr1].
        rewrite Heq in Hr1. rewrite Hx in Hr1. inversion Hr1; subst r1.
        pose proof (Hinv_lt _ _ H2). lia.
    Qed.


    (** * Extending the history over the undone event *)

    Lemma acons_now_lift (s s' : @TryStackAuxState A) h :
      tsa_vertices s' = tsa_vertices s -> tsa_node_inv s' = tsa_node_inv s ->
      tsa_node_ret s' = tsa_node_ret s -> tsa_removals s' = tsa_removals s ->
      tsa_now s' <= tsa_now s ->
      acons s' h -> acons s h.
    Proof.
      intros HV Hinv Hret Hrem Hnow Hc.
      constructor.
      - intros n p Hp. destruct (a_inv_placed _ _ Hc _ _ Hp) as (H1 & H2 & H3).
        rewrite Hinv, Hret in *. split; [lia|split; assumption].
      - intros n i Hi. rewrite <- Hinv in Hi. exact (a_total _ _ Hc _ _ Hi).
      - intros n p a Hp. destruct (a_pop_placed _ _ Hc _ _ _ Hp) as (H1 & H2 & H3).
        rewrite Hrem in *. split; [lia|split; assumption].
      - intros n a st rt Hr. rewrite <- Hrem in Hr. exact (a_removal_popped _ _ Hc _ _ _ _ Hr).
      - intros n p a x q r Hp Hq Hlt Hr Hlt'. rewrite <- Hret in Hr.
        exact (a_pop_top _ _ Hc _ _ _ _ _ _ Hp Hq Hlt Hr Hlt').
      - exact (a_inv_unique _ _ Hc).
      - exact (a_pop_unique _ _ Hc).
      - exact (a_inv_pop_distinct _ _ Hc).
      - intros x i m r q H1 H2 H3 H4 H5 H6. rewrite <- Hinv in H2. rewrite <- Hret in H3.
        exact (a_nd _ _ Hc _ _ _ _ _ H1 H2 H3 H4 H5 H6).
    Qed.

    Lemma key_spec_lift (s s' : @TryStackAuxState A) kn :
      tsa_node_inv s' = tsa_node_inv s -> tsa_removals s' = tsa_removals s ->
      key_spec s' kn -> key_spec s kn.
    Proof.
      intros Hinv Hrem [H1 H2]. split.
      - intros t x. rewrite <- Hinv. apply H1.
      - intros t n. rewrite <- Hrem. apply H2.
    Qed.

    (** The push response of [x] at [T]: the history is unchanged. *)
    Lemma acons_undo_ret (s : @TryStackAuxState A) x T h :
      tsa_ghost_wf s -> tsa_now s = S T -> tsa_node_ret s x = Some T ->
      acons (undo_ret s x T) h -> acons s h.
    Proof.
      intros Hwf Hnow Hx Hc.
      assert (Hret : forall m r, tsa_node_ret s m = Some r ->
        m = x /\ r = T \/ tsa_node_ret (undo_ret s x T) m = Some r).
      { intros m r Hr. simpl. destruct (node_eq_dec m x) as [->|Hne]; [left|right; exact Hr].
        rewrite Hx in Hr. inversion Hr. auto. }
      constructor.
      - intros n p Hp. destruct (a_inv_placed _ _ Hc _ _ Hp) as (H1 & H2 & H3).
        simpl in *. split; [lia|]. split; [exact H2|].
        intros r Hr. destruct (Hret n r Hr) as [[-> ->]|Hr']; [lia|exact (H3 r Hr')].
      - intros n i Hi. exact (a_total _ _ Hc _ _ Hi).
      - intros n p a Hp. destruct (a_pop_placed _ _ Hc _ _ _ Hp) as (H1 & H2 & H3).
        simpl in *. split; [lia|split; assumption].
      - intros n a st rt Hr. exact (a_removal_popped _ _ Hc _ _ _ _ Hr).
      - intros n p a x' q r Hp Hq Hlt Hr Hlt'.
        destruct (Hret n r Hr) as [[-> ->]|Hr'].
        + destruct (a_inv_placed _ _ Hc _ _ Hq) as (H1 & _). simpl in H1. lia.
        + exact (a_pop_top _ _ Hc _ _ _ _ _ _ Hp Hq Hlt Hr' Hlt').
      - exact (a_inv_unique _ _ Hc).
      - exact (a_pop_unique _ _ Hc).
      - exact (a_inv_pop_distinct _ _ Hc).
      - intros x' i m r q H1 H2 H3 H4 H5 H6.
        destruct (Hret m r H3) as [[-> ->]|Hr'].
        + destruct (a_inv_placed _ _ Hc _ _ H5) as (H7 & _). simpl in H7. lia.
        + exact (a_nd _ _ Hc _ _ _ _ _ H1 H2 Hr' H4 H5 H6).
    Qed.

    (** The push invocation of [x] at [T]: the abstract push-inv of [x] is
        placed at [(T, 0)]. *)
    Definition ext_inv_hist (h : History) (x : LPNodeId) (T : nat) : History :=
      {| h_inv := fun m => if node_eq_dec m x then Some (pair T 0) else h_inv h m;
         h_pop := h_pop h |}.

    Definition ext_key (kn : KeyMap) (t : nat) (yb : LPNodeId * bool) : KeyMap :=
      fun t' => if Nat.eq_dec t' t then Some yb else kn t'.

    Lemma acons_undo_inv (s : @TryStackAuxState A) x T h :
      tsa_ghost_wf s -> tsa_now s = S T -> tsa_node_inv s x = Some T ->
      acons (undo_inv s x T) h -> acons s (ext_inv_hist h x T).
    Proof.
      intros Hwf Hnow Hx Hc.
      assert (Hlt : forall t ev, ghost_event_at s t ev -> ev <> GInv x -> t < T).
      { intros t ev Hev Hne. eapply ghost_time_lt_other; eauto. exact Hx. }
      assert (Hret_none : tsa_node_ret s x = None).
      { destruct (tsa_node_ret s x) as [r|] eqn:Hr; [|reflexivity].
        destruct (wf_ret_inv _ Hwf _ _ Hr) as (i & Hi & Hlt').
        rewrite Hx in Hi. inversion Hi; subst i.
        pose proof (Hlt r (GRet x) Hr ltac:(discriminate)). lia. }
      assert (Hrem_none : tsa_removals s x = None).
      { destruct (tsa_removals s x) as [[[a st] rt]|] eqn:Hr; [|reflexivity].
        destruct (wf_removal _ Hwf _ _ _ _ Hr) as (Hstrt & _ & (i & Hi & Hilt) & _).
        rewrite Hx in Hi. inversion Hi; subst i.
        pose proof (Hlt rt (GRem x) ltac:(exists a, st; exact Hr) ltac:(discriminate)). lia. }
      assert (Hpop_none : h_pop h x = None).
      { destruct (h_pop h x) as [[p a]|] eqn:Hp; [|reflexivity].
        destruct (a_pop_placed _ _ Hc _ _ _ Hp) as (_ & _ & (st & rt & Hr & _)).
        simpl in Hr. congruence. }
      assert (Hinv : forall m q, h_inv (ext_inv_hist h x T) m = Some q <->
        (m = x /\ q = pair T 0) \/ (m <> x /\ h_inv h m = Some q)).
      { intros m q. simpl. destruct (node_eq_dec m x) as [->|Hne].
        - split; [intro H; inversion H; auto|]. intros [[_ ->]|[H _]]; [reflexivity|congruence].
        - split; [auto|]. intros [[H _]|[_ H]]; [congruence|exact H]. }
      assert (Hinv_old : forall m q, h_inv h m = Some q -> m <> x /\ fst q < T).
      { intros m q Hq. destruct (a_inv_placed _ _ Hc _ _ Hq) as (H1 & (i & Hi & _) & _).
        simpl in *. split; [|exact H1]. intros ->. destruct (node_eq_dec x x); congruence. }
      assert (Hpop_old : forall m p a, h_pop h m = Some (pair p a) -> fst p < T).
      { intros m p a Hp. destruct (a_pop_placed _ _ Hc _ _ _ Hp) as (H1 & _). exact H1. }
      constructor.
      - intros n p Hp. apply Hinv in Hp. destruct Hp as [[-> ->]|[Hne Hp]].
        + simpl. split; [lia|]. split; [exists T; auto|].
          intros r Hr. congruence.
        + destruct (a_inv_placed _ _ Hc _ _ Hp) as (H1 & (i & Hi & Hile) & H3).
          simpl in *. destruct (node_eq_dec n x); [congruence|].
          split; [lia|]. split; [eauto|exact H3].
      - intros n i Hi. destruct (node_eq_dec n x) as [->|Hne].
        + exists (pair T 0). apply Hinv. auto.
        + destruct (a_total _ _ Hc n i) as [p Hp].
          { simpl. destruct (node_eq_dec n x); [congruence|exact Hi]. }
          exists p. apply Hinv. auto.
      - intros n p a Hp. simpl in Hp.
        destruct (a_pop_placed _ _ Hc _ _ _ Hp) as (H1 & (q & Hq & Hqlt) & H3).
        simpl in *. split; [lia|]. split; [|exact H3].
        exists q. split; [|exact Hqlt]. apply Hinv. right.
        split; [|exact Hq]. exact (proj1 (Hinv_old _ _ Hq)).
      - intros n a st rt Hr. exact (a_removal_popped _ _ Hc _ _ _ _ Hr).
      - intros n p a x' q r Hp Hq Hlt' Hr Hlt''. simpl in Hp.
        apply Hinv in Hq. destruct Hq as [[-> ->]|[Hne Hq]].
        + exfalso. pose proof (Hpop_old _ _ _ Hp). destruct p as [g k].
          unfold pos_lt in Hlt'; simpl in *. lia.
        + destruct (a_pop_top _ _ Hc _ _ _ _ _ _ Hp Hq Hlt' Hr Hlt'') as (p' & a' & Hp' & Hlt3).
          exists p', a'. auto.
      - intros n m p Hn Hm. apply Hinv in Hn. apply Hinv in Hm.
        destruct Hn as [[-> ->]|[Hne Hn]]; destruct Hm as [[-> Heq]|[Hne' Hm]].
        + reflexivity.
        + exfalso. pose proof (Hinv_old _ _ Hm) as [_ H]. simpl in H. lia.
        + exfalso. pose proof (Hinv_old _ _ Hn) as [_ H]. rewrite Heq in H. simpl in H. lia.
        + eapply a_inv_unique; eauto.
      - intros n m p a b Hn Hm. simpl in *. eapply a_pop_unique; eauto.
      - intros n m p a Hn Hm. simpl in Hm. apply Hinv in Hn.
        destruct Hn as [[-> ->]|[Hne Hn]].
        + pose proof (Hpop_old _ _ _ Hm). simpl in H. lia.
        + eapply a_inv_pop_distinct; eauto.
      - intros x' i m r q H1 H2 H3 H4 H5 H6. simpl in H1.
        apply Hinv in H5. destruct H5 as [[-> ->]|[Hne H5]].
        + exfalso. simpl in H6. rewrite Hx in H2. inversion H2; subst i.
          pose proof (Hlt r (GRet m) H3 ltac:(discriminate)). lia.
        + assert (H2' : tsa_node_inv (undo_inv s x T) x' = Some i).
          { simpl. destruct (node_eq_dec x' x); [congruence|exact H2]. }
          destruct (a_nd _ _ Hc _ _ _ _ _ H1 H2' H3 H4 H5 H6) as (p' & a' & Hp' & Hlt').
          exists p', a'. auto.
    Qed.

    Lemma key_spec_undo_inv (s : @TryStackAuxState A) x T kn :
      tsa_ghost_wf s -> tsa_node_inv s x = Some T ->
      key_spec (undo_inv s x T) kn -> key_spec s (ext_key kn T (pair x true)).
    Proof.
      intros Hwf Hx [H1 H2]. unfold ext_key. split.
      - intros t y. destruct (Nat.eq_dec t T) as [->|Hne].
        + split.
          * intro H. inversion H; subst y. exact Hx.
          * intro H. f_equal. f_equal. eapply wf_inv_unique; eauto.
        + rewrite (H1 t y). simpl. destruct (node_eq_dec y x) as [->|Hne'].
          * split; [discriminate|]. intro H. rewrite Hx in H. inversion H. congruence.
          * reflexivity.
      - intros t n. destruct (Nat.eq_dec t T) as [->|Hne].
        + split; [discriminate|]. intros (a & rt & Hr).
          destruct (wf_removal _ Hwf _ _ _ _ Hr) as (Hst & Hrt & (i & Hi & Hilt) & _).
          exfalso. assert (tsa_ghost_wf s) by exact Hwf.
          pose proof (wf_unique _ Hwf T (GInv x) (GSnapOf n) Hx ltac:(exists a, rt; exact Hr)).
          discriminate.
        + exact (H2 t n).
    Qed.

    (** * The removal case

        [s] is well-formed with clock [S T]; its last event is the removal of
        [n] by [a] with snapshot time [st].  [h'] is a history of the state
        without that removal. *)
    Section Removal.
      Variable s : @TryStackAuxState A.
      Variables (n : LPNodeId) (a : tid) (st T : nat) (h' : History).
      Hypothesis Hwf : tsa_ghost_wf s.
      Hypothesis Hnow : tsa_now s = S T.
      Hypothesis Hn : tsa_removals s n = Some (pair (pair a st) T).
      Hypothesis Hc : acons (undo_rem s n T) h'.

      (** ** Basic facts *)

      Lemma rem_st_lt : st < T.
      Proof. destruct (wf_removal _ Hwf _ _ _ _ Hn) as (H & _). exact H. Qed.

      Lemma rem_inv_n : exists i, tsa_node_inv s n = Some i /\ i < st.
      Proof. destruct (wf_removal _ Hwf _ _ _ _ Hn) as (_ & _ & H & _). exact H. Qed.

      Lemma rem_time_lt t ev :
        ghost_event_at s t ev -> ev <> GRem n -> t < T.
      Proof.
        intros Hev Hne. eapply ghost_time_lt_other; eauto. exists a, st. exact Hn.
      Qed.

      Lemma rem_inv_lt m i : tsa_node_inv s m = Some i -> i < T.
      Proof. intros Hi. exact (rem_time_lt i (GInv m) Hi ltac:(discriminate)). Qed.

      Lemma rem_ret_lt m r : tsa_node_ret s m = Some r -> r < T.
      Proof. intros Hr. exact (rem_time_lt r (GRet m) Hr ltac:(discriminate)). Qed.

      Lemma rem_inv_ne_st m : tsa_node_inv s m <> Some st.
      Proof.
        intro Hm.
        pose proof (wf_unique _ Hwf st (GInv m) (GSnapOf n) Hm ltac:(exists a, T; exact Hn)).
        discriminate.
      Qed.

      (** Removals of other vertices are those of [(undo_rem s n T)]. *)
      Lemma rem_other m : m <> n -> tsa_removals (undo_rem s n T) m = tsa_removals s m.
      Proof. intro Hne. unfold undo_rem; simpl. destruct (node_eq_dec m n); congruence. Qed.

      Lemma rem_self : tsa_removals (undo_rem s n T) n = None.
      Proof. unfold undo_rem; simpl. destruct (node_eq_dec n n); congruence. Qed.

      Lemma rem_pop_n : h_pop h' n = None.
      Proof.
        destruct (h_pop h' n) as [[p b]|] eqn:Hp; [|reflexivity].
        destruct (a_pop_placed _ _ Hc _ _ _ Hp) as (_ & _ & (st' & rt' & Hr & _)).
        rewrite rem_self in Hr. discriminate.
      Qed.

      Lemma rem_pop_ne x p b : h_pop h' x = Some (pair p b) -> x <> n.
      Proof. intros Hp ->. rewrite rem_pop_n in Hp. discriminate. Qed.

      Lemma rem_inv_pos_lt x q : h_inv h' x = Some q -> fst q < T.
      Proof. intro Hq. exact (proj1 (a_inv_placed _ _ Hc _ _ Hq)). Qed.

      Lemma rem_pop_pos_lt x p b : h_pop h' x = Some (pair p b) -> fst p < T.
      Proof. intro Hp. exact (proj1 (a_pop_placed _ _ Hc _ _ _ Hp)). Qed.

      Lemma rem_inv_key x q : h_inv h' x = Some q -> exists i, tsa_node_inv s x = Some i /\ i <= fst q.
      Proof. intro Hq. exact (proj1 (proj2 (a_inv_placed _ _ Hc _ _ Hq))). Qed.

      Lemma rem_inv_ret x q r : h_inv h' x = Some q -> tsa_node_ret s x = Some r -> fst q <= r.
      Proof. intros Hq Hr. exact (proj2 (proj2 (a_inv_placed _ _ Hc _ _ Hq)) r Hr). Qed.

      (** The snapshot blocking condition of [wf_removal], specialised. *)
      Lemma rem_blocking y i rn :
        tsa_node_ret s n = Some rn ->
        tsa_node_inv s y = Some i -> rn < i -> i < st ->
        exists p b, h_pop h' y = Some (pair p b).
      Proof.
        intros Hrn Hi Hlt1 Hlt2.
        destruct (wf_removal _ Hwf _ _ _ _ Hn) as (_ & _ & _ & Hblock).
        assert (Hedge : tsa_edges s y n) by (apply (wf_edges _ Hwf); eauto).
        destruct (Hblock y i Hi Hlt2 Hedge) as (a' & st' & rt' & Hy & Hrt').
        assert (Hne : y <> n) by (intros ->; rewrite Hn in Hy; inversion Hy; lia).
        rewrite <- (rem_other y Hne) in Hy.
        destruct (a_removal_popped _ _ Hc _ _ _ _ Hy) as [p Hp]. eauto.
      Qed.

      (** A popped-or-not vertex that is not popped and is abstractly newer
          than the completed [n] was pushed after the snapshot. *)
      Lemma rem_unpopped_newer_after_st x q rn i :
        tsa_node_ret s n = Some rn ->
        h_pop h' x = None -> h_inv h' x = Some q -> rn < fst q ->
        tsa_node_inv s x = Some i -> st < i.
      Proof.
        intros Hrn Hpop Hq Hlt Hi.
        assert (Hrn' : tsa_node_ret (undo_rem s n T) n = Some rn) by exact Hrn.
        assert (Hi' : tsa_node_inv (undo_rem s n T) x = Some i) by exact Hi.
        assert (Hgt : rn < i).
        { destruct (le_lt_dec i rn) as [Hle|Hlt']; [|exact Hlt']. exfalso.
          destruct (a_nd _ _ Hc _ _ _ _ _ Hpop Hi' Hrn' Hle Hq Hlt) as (p' & b' & Hp' & _).
          rewrite rem_pop_n in Hp'. discriminate. }
        destruct (lt_eq_lt_dec i st) as [[Hlt'|Heq]|Hgt'].
        - exfalso. destruct (rem_blocking x i rn Hrn Hi Hgt Hlt') as (p & b & Hp). congruence.
        - exfalso. subst i. exact (rem_inv_ne_st x Hi).
        - exact Hgt'.
      Qed.

      (** ** Feasible positions *)

      Section Completed.
        Variable rn : nat.
        Hypothesis Hrn : tsa_node_ret s n = Some rn.

        Lemma rem_rn_lt : rn < T.
        Proof. exact (rem_ret_lt n rn Hrn). Qed.

        Definition newer (x : LPNodeId) : Prop :=
          exists q, h_inv h' x = Some q /\ rn < fst q.

        Definition blocker (Q : Pos) (x : LPNodeId) : Prop :=
          newer x /\ placed_before h' Q x /\ ~ popped_before h' Q x.

        Definition pending_at (g : nat) (x : LPNodeId) : Prop :=
          forall r, tsa_node_ret s x = Some r -> g <= r.

        Definition safe (Q : Pos) (x : LPNodeId) : Prop :=
          forall m pm bm r q,
            h_pop h' m = Some (pair pm bm) -> tsa_node_ret s m = Some r ->
            h_inv h' x = Some q -> fst q <= r -> r < fst Q -> ~ pos_lt pm Q ->
            exists px bx, h_pop h' x = Some (pair px bx) /\ pos_lt px pm.

        Definition FS (Q : Pos) : Prop :=
          pos_le (pair st 0) Q /\ placed_before h' Q n /\ fst Q <= T /\
          forall x, blocker Q x -> pending_at (fst Q) x /\ safe Q x.

        (** Abstractly newer, unpopped, completed vertices. *)
        Definition Cset (x : LPNodeId) : Prop :=
          newer x /\ h_pop h' x = None /\ exists r, tsa_node_ret s x = Some r.

        Lemma newer_not_n : ~ newer n.
        Proof.
          intros (q & Hq & Hlt). pose proof (rem_inv_ret n q rn Hq Hrn). lia.
        Qed.

        Lemma placed_n Q : (exists q, h_inv h' n = Some q /\ fst q < fst Q) -> placed_before h' Q n.
        Proof.
          intros (q & Hq & Hlt). exists q. split; [exact Hq|].
          destruct q, Q. unfold pos_lt; simpl in *. lia.
        Qed.

        Lemma inv_n_exists : exists q, h_inv h' n = Some q /\ fst q <= rn.
        Proof.
          destruct rem_inv_n as (i & Hi & _).
          destruct (a_total _ _ Hc n i Hi) as [q Hq].
          exists q. split; [exact Hq|]. exact (rem_inv_ret n q rn Hq Hrn).
        Qed.

        (** [x0] in [Cset] with inv position [M]: nothing newer than a
            completed [m] can be popped after [M] while [x0] is live. *)
        Lemma Cset_pop_after x0 M m pm bm r :
          Cset x0 -> h_inv h' x0 = Some M ->
          h_pop h' m = Some (pair pm bm) -> tsa_node_ret s m = Some r -> r < fst M ->
          pos_lt M pm -> False.
        Proof.
          intros (_ & Hpop0 & _) HM Hpm Hr Hlt Hlt'.
          assert (Hr' : tsa_node_ret (undo_rem s n T) m = Some r) by exact Hr.
          destruct (a_pop_top _ _ Hc _ _ _ _ _ _ Hpm HM Hlt' Hr' Hlt) as (p' & b' & Hp' & _).
          congruence.
        Qed.

        Lemma pop_not_before_inv M pm x0 m bm :
          h_inv h' x0 = Some M -> h_pop h' m = Some (pair pm bm) ->
          ~ pos_lt pm M -> pos_lt M pm.
        Proof.
          intros HM Hpm Hnlt.
          destruct (pos_trichotomy M pm) as [H|[H|H]]; [exact H| |contradiction].
          subst. exfalso. eapply a_inv_pop_distinct; eauto.
        Qed.

        Lemma exists_M :
          exists M, FS M /\ forall z qz, Cset z -> h_inv h' z = Some qz -> pos_le M qz.
        Proof.
          pose proof rem_st_lt as Hst.
          destruct (classic (exists x, Cset x)) as [HC|HnC].
          - destruct (pos_least (fun q => exists x, Cset x /\ h_inv h' x = Some q))
              as (M & (x0 & HC0 & HM) & Hleast).
            { destruct HC as [x [Hnew Hrest]]. destruct Hnew as (q & Hq & Hlt).
              exists q, x. split; [split; [|exact Hrest]|exact Hq]. exists q. auto. }
            pose proof HC0 as (Hnew0 & Hpop0 & (r0 & Hr0)).
            destruct Hnew0 as (M' & HM' & HMlt). rewrite HM in HM'. inversion HM'; subst M'.
            destruct (rem_inv_key x0 M HM) as (i0 & Hi0 & Hi0le).
            pose proof (rem_unpopped_newer_after_st x0 M rn i0 Hrn Hpop0 HM HMlt Hi0) as Hi0st.
            pose proof (rem_inv_pos_lt x0 M HM) as HMT.
            exists M. split; [|intros z qz Hz Hqz; apply Hleast; eauto].
            split; [|split; [|split]].
            + left. destruct M. unfold pos_lt; simpl in *. lia.
            + apply placed_n. destruct inv_n_exists as (qn & Hqn & Hqnle). exists qn. split; [exact Hqn|lia].
            + lia.
            + intros x (Hnewx & (qx & Hqx & Hqxlt) & Hnpop). split.
              * intros r Hr. destruct (le_lt_dec (fst M) r) as [Hle|Hlt]; [exact Hle|]. exfalso.
                destruct (h_pop h' x) as [[px bx]|] eqn:Hpx.
                -- assert (Hnlt : ~ pos_lt px M) by (intro H; apply Hnpop; exists px, bx; auto).
                   pose proof (pop_not_before_inv M px x0 x bx HM Hpx Hnlt).
                   eapply Cset_pop_after; eauto.
                -- assert (HCx : Cset x) by (split; [exact Hnewx|split; [exact Hpx|eauto]]).
                   pose proof (Hleast qx ltac:(eauto)) as Hle.
                   apply (pos_lt_irrefl qx). eapply pos_lt_le_trans; eauto.
              * intros m pm bm r q Hpm Hr Hq Hqle Hrlt Hnlt.
                exfalso. pose proof (pop_not_before_inv M pm x0 m bm HM Hpm Hnlt).
                eapply Cset_pop_after; eauto.
          - exists (pair T 0). split; [|intros z qz Hz _; exfalso; apply HnC; eauto].
            split; [|split; [|split]].
            + left. unfold pos_lt; simpl. lia.
            + apply placed_n. destruct inv_n_exists as (qn & Hqn & _). exists qn. split; [exact Hqn|].
              simpl. exact (rem_inv_pos_lt n qn Hqn).
            + simpl. lia.
            + intros x (Hnewx & _ & Hnpop). split.
              * intros r Hr. exfalso. apply HnC. exists x. split; [exact Hnewx|]. split; [|eauto].
                destruct (h_pop h' x) as [[px bx]|] eqn:Hpx; [|reflexivity].
                exfalso. apply Hnpop. exists px, bx. split; [exact Hpx|].
                pose proof (rem_pop_pos_lt x px bx Hpx). destruct px. unfold pos_lt; simpl in *. lia.
              * intros m pm bm r q Hpm Hr Hq Hqle Hrlt Hnlt. exfalso. apply Hnlt.
                pose proof (rem_pop_pos_lt m pm bm Hpm). destruct pm. unfold pos_lt; simpl in *. lia.
        Qed.

        (** The least feasible position, and the vertex it gets from [exists_M]. *)
        Lemma exists_P :
          exists P, FS P /\ (forall Q, FS Q -> pos_le P Q) /\
            (forall z qz, Cset z -> h_inv h' z = Some qz -> pos_lt qz P -> False).
        Proof.
          destruct exists_M as (M & HM & Hmin).
          destruct (pos_least FS) as (P & HP & Hleast); [eauto|].
          exists P. split; [exact HP|]. split; [exact Hleast|].
          intros z qz Hz Hqz Hlt.
          pose proof (Hmin z qz Hz Hqz) as H1. pose proof (Hleast M HM) as H2.
          apply (pos_lt_irrefl qz). eapply pos_lt_le_trans; [exact Hlt|].
          eapply pos_le_trans; eauto.
        Qed.

        (** Every blocker of the least feasible position is already popped. *)
        Lemma blocker_popped P :
          FS P -> (forall Q, FS Q -> pos_le P Q) ->
          (forall z qz, Cset z -> h_inv h' z = Some qz -> pos_lt qz P -> False) ->
          forall x, blocker P x -> exists px bx, h_pop h' x = Some (pair px bx).
        Proof.
          intros HP Hleast HnoC x (Hnewx & (qx & Hqx & Hqxlt) & Hnpop).
          destruct (h_pop h' x) as [[px bx]|] eqn:Hpx; [eauto|]. exfalso.
          destruct Hnewx as (qx' & Hqx' & Hlt). rewrite Hqx in Hqx'. inversion Hqx'; subst qx'.
          destruct (rem_inv_key x qx Hqx) as (ix & Hix & Hixle).
          pose proof (rem_unpopped_newer_after_st x qx rn ix Hrn Hpx Hqx Hlt Hix) as Hixst.
          assert (HFS : FS qx).
          { split; [|split; [|split]].
            - left. destruct qx. unfold pos_lt; simpl in *. lia.
            - apply placed_n. destruct inv_n_exists as (qn & Hqn & Hqnle). exists qn. split; [exact Hqn|lia].
            - pose proof (rem_inv_pos_lt x qx Hqx). lia.
            - intros z (Hnewz & (qz & Hqz & Hqzlt) & Hnpopz). split.
              + intros r Hr. destruct (le_lt_dec (fst qx) r) as [Hle|Hlt']; [exact Hle|]. exfalso.
                destruct (h_pop h' z) as [[pz bz]|] eqn:Hpz.
                * assert (Hnlt : ~ pos_lt pz qx) by (intro H; apply Hnpopz; exists pz, bz; auto).
                  pose proof (pop_not_before_inv qx pz x z bz Hqx Hpz Hnlt) as Hlt2.
                  assert (Hr' : tsa_node_ret (undo_rem s n T) z = Some r) by exact Hr.
                  destruct (a_pop_top _ _ Hc _ _ _ _ _ _ Hpz Hqx Hlt2 Hr' Hlt') as (p' & b' & Hp' & _).
                  congruence.
                * apply (HnoC z qz); [|exact Hqz|eapply pos_lt_trans; eauto].
                  split; [exact Hnewz|split; [exact Hpz|eauto]].
              + intros m pm bm r q Hpm Hr Hq Hqle Hrlt Hnlt. exfalso.
                pose proof (pop_not_before_inv qx pm x m bm Hqx Hpm Hnlt) as Hlt2.
                assert (Hr' : tsa_node_ret (undo_rem s n T) m = Some r) by exact Hr.
                destruct (a_pop_top _ _ Hc _ _ _ _ _ _ Hpm Hqx Hlt2 Hr' Hrlt) as (p' & b' & Hp' & _).
                congruence. }
          pose proof (Hleast qx HFS) as Hle.
          apply (pos_lt_irrefl qx). eapply pos_lt_le_trans; eauto.
        Qed.


        (** ** The extended history *)

        Section Construct.
          Variable P : Pos.
          Hypothesis HP : FS P.
          Hypothesis HPleast : forall Q, FS Q -> pos_le P Q.
          Hypothesis HnoC : forall z qz, Cset z -> h_inv h' z = Some qz -> pos_lt qz P -> False.

          Definition shift (q : Pos) : Pos :=
            if Nat.eq_dec (fst q) (fst P)
            then (if le_dec (snd P) (snd q) then pair (fst P) (snd q + (T + 2)) else q)
            else q.

          Definition moved_b (x : LPNodeId) : bool :=
            match h_inv h' x with
            | Some q =>
                if lt_dec rn (fst q) then
                  if pos_lt_dec q P then
                    match h_pop h' x with
                    | Some pb => if pos_lt_dec (fst pb) P then false else true
                    | None => true
                    end
                  else false
                else false
            | None => false
            end.

          Definition mpos (i : nat) : Pos := pair (fst P) (snd P + 1 + i).

          Definition new_inv (x : LPNodeId) : option Pos :=
            if moved_b x
            then match tsa_node_inv s x with Some i => Some (mpos i) | None => None end
            else match h_inv h' x with Some q => Some (shift q) | None => None end.

          Definition new_pop (x : LPNodeId) : option (Pos * tid) :=
            if node_eq_dec x n then Some (pair P a)
            else match h_pop h' x with
                 | Some pb => Some (pair (shift (fst pb)) (snd pb))
                 | None => None
                 end.

          Definition new_hist : History := {| h_inv := new_inv; h_pop := new_pop |}.

          (** Facts about [P]. *)
          Lemma P_ge_st : st <= fst P.
          Proof.
            destruct HP as (Hle & _). destruct Hle as [Hlt|Heq].
            - destruct P. unfold pos_lt in Hlt; simpl in *. lia.
            - rewrite <- Heq. reflexivity.
          Qed.

          Lemma P_le_T : fst P <= T.
          Proof. destruct HP as (_ & _ & H & _). exact H. Qed.

          Lemma P_after_inv_n : exists q, h_inv h' n = Some q /\ pos_lt q P.
          Proof. destruct HP as (_ & H & _). exact H. Qed.

          Lemma P_blocker x : blocker P x -> pending_at (fst P) x /\ safe P x.
          Proof. destruct HP as (_ & _ & _ & H). exact (H x). Qed.

          Lemma P_blocker_popped x :
            blocker P x -> exists px bx, h_pop h' x = Some (pair px bx) /\ ~ pos_lt px P.
          Proof.
            intro Hb. destruct (blocker_popped P HP HPleast HnoC x Hb) as (px & bx & Hpx).
            exists px, bx. split; [exact Hpx|]. destruct Hb as (_ & _ & Hnpop).
            intro Hlt. apply Hnpop. exists px, bx. auto.
          Qed.

          (** Facts about [shift] and [mpos]. *)
          Lemma shift_fst q : fst (shift q) = fst q.
          Proof.
            unfold shift. destruct (Nat.eq_dec (fst q) (fst P)) as [Heq|]; [|reflexivity].
            destruct (le_dec (snd P) (snd q)); [simpl; auto|reflexivity].
          Qed.

          Lemma shift_lt_P q : pos_lt q P -> shift q = q.
          Proof.
            intro Hlt. unfold shift. destruct (Nat.eq_dec (fst q) (fst P)) as [Heq|]; [|reflexivity].
            destruct (le_dec (snd P) (snd q)) as [Hle|]; [|reflexivity].
            exfalso. destruct q, P. unfold pos_lt in Hlt; simpl in *. lia.
          Qed.

          Lemma shift_ge_P q : ~ pos_lt q P -> pos_lt P (shift q).
          Proof.
            intro Hnlt. unfold shift. destruct q as [gq kq], P as [gp kp]. simpl in *.
            unfold pos_lt in *; simpl in *.
            destruct (Nat.eq_dec gq gp) as [->|Hne].
            - destruct (le_dec kp kq) as [Hle|Hnle]; simpl; [lia|]. exfalso. apply Hnlt. right. split; [reflexivity|lia].
            - simpl. left. lia.
          Qed.

          Lemma shift_mono q1 q2 : pos_lt q1 q2 -> pos_lt (shift q1) (shift q2).
          Proof.
            intro Hlt. unfold shift. destruct q1 as [g1 k1], q2 as [g2 k2], P as [gp kp].
            unfold pos_lt in *; simpl in *.
            destruct (Nat.eq_dec g1 gp) as [->|Hne1]; destruct (Nat.eq_dec g2 gp) as [->|Hne2].
            - destruct (le_dec kp k1) as [Hle1|Hnle1]; destruct (le_dec kp k2) as [Hle2|Hnle2]; simpl; lia.
            - destruct (le_dec kp k1); simpl; lia.
            - destruct (le_dec kp k2); simpl; lia.
            - simpl. lia.
          Qed.

          Lemma shift_lt_inv q1 q2 : pos_lt (shift q1) (shift q2) -> pos_lt q1 q2.
          Proof.
            intro Hlt. destruct (pos_trichotomy q1 q2) as [H|[H|H]]; [exact H| |].
            - subst. exfalso. eapply pos_lt_irrefl; eauto.
            - exfalso. apply shift_mono in H. eapply pos_lt_asym; eauto.
          Qed.

          Lemma shift_inj q1 q2 : shift q1 = shift q2 -> q1 = q2.
          Proof.
            intro Heq. destruct (pos_trichotomy q1 q2) as [H|[H|H]]; [|exact H|].
            - apply shift_mono in H. rewrite Heq in H. exfalso. eapply pos_lt_irrefl; eauto.
            - apply shift_mono in H. rewrite Heq in H. exfalso. eapply pos_lt_irrefl; eauto.
          Qed.

          Lemma shift_ne_P q : shift q <> P.
          Proof.
            intro Heq. destruct (pos_lt_dec q P) as [Hlt|Hnlt].
            - rewrite shift_lt_P in Heq by exact Hlt. subst. eapply pos_lt_irrefl; eauto.
            - pose proof (shift_ge_P q Hnlt). rewrite Heq in H. eapply pos_lt_irrefl; eauto.
          Qed.

          Lemma mpos_gt_P i : pos_lt P (mpos i).
          Proof. unfold mpos, pos_lt. destruct P; simpl. lia. Qed.

          Lemma mpos_lt_shift i q : i < T -> ~ pos_lt q P -> pos_lt (mpos i) (shift q).
          Proof.
            intros Hi Hnlt. unfold mpos, shift. destruct q as [gq kq], P as [gp kp].
            unfold pos_lt in *; simpl in *.
            destruct (Nat.eq_dec gq gp) as [->|Hne].
            - destruct (le_dec kp kq) as [Hle|Hnle]; simpl.
              + right. split; [reflexivity|lia].
              + exfalso. apply Hnlt. right. split; [reflexivity|lia].
            - simpl. left. lia.
          Qed.

          Lemma mpos_ne_shift i q : i < T -> mpos i <> shift q.
          Proof.
            intros Hi Heq. destruct (pos_lt_dec q P) as [Hlt|Hnlt].
            - rewrite shift_lt_P in Heq by exact Hlt. pose proof (mpos_gt_P i). rewrite Heq in H.
              eapply pos_lt_asym; eauto.
            - pose proof (mpos_lt_shift i q Hi Hnlt). rewrite Heq in H. eapply pos_lt_irrefl; eauto.
          Qed.

          Lemma mpos_ne_P i : mpos i <> P.
          Proof. intro Heq. pose proof (mpos_gt_P i). rewrite Heq in H. eapply pos_lt_irrefl; eauto. Qed.

          Lemma mpos_inj i j : mpos i = mpos j -> i = j.
          Proof. unfold mpos. intro H. inversion H. lia. Qed.

          Lemma mpos_fst i : fst (mpos i) = fst P.
          Proof. reflexivity. Qed.

          (** Characterisation of [moved_b]. *)
          Lemma moved_b_true x : moved_b x = true <-> blocker P x.
          Proof.
            unfold moved_b, blocker, newer, placed_before, popped_before.
            destruct (h_inv h' x) as [q|] eqn:Hq.
            - destruct (lt_dec rn (fst q)) as [Hlt|Hnlt].
              + destruct (pos_lt_dec q P) as [HqP|HnqP].
                * destruct (h_pop h' x) as [[p b]|] eqn:Hp; simpl.
                  -- destruct (pos_lt_dec p P) as [HpP|HnpP].
                     ++ split; [discriminate|]. intros (_ & _ & Hnpop). exfalso. apply Hnpop. eauto.
                     ++ split; [|reflexivity]. intros _. split; [eauto|]. split; [eauto|].
                        intros (p' & b' & Hp' & Hlt'). inversion Hp'; subst. contradiction.
                  -- split; [|reflexivity]. intros _. split; [eauto|]. split; [eauto|].
                     intros (p' & b' & Hp' & _). discriminate.
                * split; [discriminate|]. intros (_ & (q' & Hq' & Hlt') & _).
                  inversion Hq'; subst. contradiction.
              + split; [discriminate|]. intros ((q' & Hq' & Hlt') & _). inversion Hq'; subst. contradiction.
            - split; [discriminate|]. intros ((q' & Hq' & _) & _). discriminate.
          Qed.

          Lemma moved_b_false x : moved_b x = false <-> ~ blocker P x.
          Proof.
            rewrite <- moved_b_true. destruct (moved_b x); split; congruence.
          Qed.

          Lemma moved_n : moved_b n = false.
          Proof. apply moved_b_false. intros (Hnew & _). exact (newer_not_n Hnew). Qed.

          (** Characterisation of the new history. *)
          Lemma new_inv_some x q' :
            new_inv x = Some q' <->
            (blocker P x /\ exists i, tsa_node_inv s x = Some i /\ q' = mpos i) \/
            (~ blocker P x /\ exists q, h_inv h' x = Some q /\ q' = shift q).
          Proof.
            unfold new_inv. destruct (moved_b x) eqn:Hm.
            - apply moved_b_true in Hm. destruct (tsa_node_inv s x) as [i|] eqn:Hi.
              + split.
                * intro H. inversion H. left. split; [exact Hm|]. eauto.
                * intros [(_ & i' & Hi' & ->)|(Hnb & _)]; [|contradiction]. inversion Hi'; subst. reflexivity.
              + split; [discriminate|]. intros [(_ & i' & Hi' & _)|(Hnb & _)]; [discriminate|contradiction].
            - apply moved_b_false in Hm. destruct (h_inv h' x) as [q|] eqn:Hq.
              + split.
                * intro H. inversion H. right. split; [exact Hm|]. eauto.
                * intros [(Hb & _)|(_ & q0 & Hq0 & ->)]; [contradiction|]. inversion Hq0; subst. reflexivity.
              + split; [discriminate|]. intros [(Hb & _)|(_ & q0 & Hq0 & _)]; [contradiction|discriminate].
          Qed.

          Lemma new_pop_some x p b :
            new_pop x = Some (pair p b) <->
            (x = n /\ p = P /\ b = a) \/
            (x <> n /\ exists p0, h_pop h' x = Some (pair p0 b) /\ p = shift p0).
          Proof.
            unfold new_pop. destruct (node_eq_dec x n) as [->|Hne].
            - split.
              + intro H. inversion H. auto.
              + intros [(_ & -> & ->)|(Hne & _)]; [reflexivity|congruence].
            - destruct (h_pop h' x) as [[p0 b0]|] eqn:Hp.
              + split.
                * intro H. inversion H; subst. right. split; [exact Hne|]. eauto.
                * intros [(H & _)|(_ & p1 & Hp1 & ->)]; [congruence|]. inversion Hp1; subst. reflexivity.
              + split; [discriminate|]. intros [(H & _)|(_ & p1 & Hp1 & _)]; [congruence|discriminate].
          Qed.

          Lemma blocker_key x : blocker P x -> exists i, tsa_node_inv s x = Some i /\ i <= fst P /\ i < T.
          Proof.
            intros (_ & (q & Hq & Hlt) & _).
            destruct (rem_inv_key x q Hq) as (i & Hi & Hile).
            exists i. split; [exact Hi|]. split; [|exact (rem_inv_lt x i Hi)].
            destruct q, P. unfold pos_lt in Hlt; simpl in *. lia.
          Qed.

          (** Non-blockers that are placed before [P] and are newer are popped
              before [P]. *)
          Lemma unmoved_newer x q :
            ~ blocker P x -> h_inv h' x = Some q -> pos_lt q P -> rn < fst q ->
            exists px bx, h_pop h' x = Some (pair px bx) /\ pos_lt px P.
          Proof.
            intros Hnb Hq Hlt Hnew.
            destruct (classic (popped_before h' P x)) as [(px & bx & Hpx & Hlt')|Hnpop]; [eauto|].
            exfalso. apply Hnb. split; [exists q; auto|]. split; [exists q; auto|exact Hnpop].
          Qed.

          Lemma new_acons : acons s new_hist.
          Proof.
            pose proof P_le_T as HPT. pose proof P_ge_st as HPst.
            pose proof rem_rn_lt as HrnT.
            constructor; simpl.
            (* a_inv_placed *)
            - intros x p Hp. apply new_inv_some in Hp.
              destruct Hp as [(Hb & i & Hi & ->)|(Hnb & q & Hq & ->)].
              + destruct (blocker_key x Hb) as (i' & Hi' & Hile & _). rewrite Hi in Hi'. inversion Hi'; subst i'.
                rewrite mpos_fst. split; [lia|]. split; [eauto|].
                intros r Hr. exact (proj1 (P_blocker x Hb) r Hr).
              + rewrite shift_fst. destruct (a_inv_placed _ _ Hc _ _ Hq) as (H1 & H2 & H3).
                simpl in *. split; [lia|split; assumption].
            (* a_total *)
            - intros x i Hi. unfold new_inv. destruct (moved_b x).
              + rewrite Hi. eauto.
              + destruct (a_total _ _ Hc x i Hi) as [q Hq]. rewrite Hq. eauto.
            (* a_pop_placed *)
            - intros x p b Hp. apply new_pop_some in Hp.
              destruct Hp as [(-> & -> & ->)|(Hne & p0 & Hp0 & ->)].
              + split; [lia|]. split.
                * destruct P_after_inv_n as (qn & Hqn & Hlt).
                  exists (shift qn). split; [|rewrite shift_lt_P by exact Hlt; exact Hlt].
                  apply new_inv_some. right. split; [|eauto]. intros (Hnew & _). exact (newer_not_n Hnew).
                * exists st, T. split; [exact Hn|]. split; [exact HPst|exact HPT].
              + destruct (a_pop_placed _ _ Hc _ _ _ Hp0) as (H1 & (q & Hq & Hqlt) & (st' & rt' & Hr & Hst' & Hrt')).
                simpl in H1. rewrite shift_fst. split; [lia|]. split.
                * destruct (moved_b x) eqn:Hm.
                  -- apply moved_b_true in Hm. destruct (blocker_key x Hm) as (i & Hi & _ & HiT).
                     exists (mpos i). split; [apply new_inv_some; left; eauto|].
                     destruct (P_blocker_popped x Hm) as (px & bx & Hpx & Hnlt).
                     rewrite Hp0 in Hpx. inversion Hpx; subst px bx.
                     apply mpos_lt_shift; assumption.
                  -- apply moved_b_false in Hm.
                     exists (shift q). split; [apply new_inv_some; right; eauto|].
                     apply shift_mono. exact Hqlt.
                * exists st', rt'. rewrite (rem_other x Hne) in Hr. auto.
            (* a_removal_popped *)
            - intros x b st' rt' Hr. destruct (node_eq_dec x n) as [->|Hne].
              + rewrite Hn in Hr. inversion Hr; subst. exists P. apply new_pop_some. auto.
              + rewrite <- (rem_other x Hne) in Hr.
                destruct (a_removal_popped _ _ Hc _ _ _ _ Hr) as [p Hp].
                exists (shift p). apply new_pop_some. right. split; [exact Hne|]. eauto.
            (* a_pop_top *)
            - intros m p b x q r Hp Hq Hlt Hr Hrlt.
              apply new_pop_some in Hp. apply new_inv_some in Hq.
              destruct Hp as [(-> & -> & ->)|(Hne & pm & Hpm & ->)].
              + (* the new pop of n *)
                rewrite Hrn in Hr. inversion Hr; subst r.
                destruct Hq as [(Hb & i & Hi & ->)|(Hnb & q0 & Hq0 & ->)].
                * exfalso. pose proof (mpos_gt_P i). eapply pos_lt_asym; eauto.
                * assert (Hq0P : pos_lt q0 P).
                  { destruct (pos_lt_dec q0 P) as [H|H]; [exact H|]. exfalso.
                    pose proof (shift_ge_P q0 H). eapply pos_lt_asym; eauto. }
                  rewrite shift_lt_P in Hrlt by exact Hq0P.
                  destruct (unmoved_newer x q0 Hnb Hq0 Hq0P Hrlt) as (px & bx & Hpx & Hpxlt).
                  exists px, bx. split; [|exact Hpxlt].
                  apply new_pop_some. right. split; [eapply rem_pop_ne; eauto|].
                  exists px. split; [exact Hpx|]. symmetry. apply shift_lt_P. exact Hpxlt.
              + (* an old pop, shifted *)
                assert (Hr' : tsa_node_ret (undo_rem s n T) m = Some r) by exact Hr.
                destruct Hq as [(Hb & i & Hi & ->)|(Hnb & q0 & Hq0 & ->)].
                * (* x was moved *)
                  destruct Hb as (Hnewx & (q0 & Hq0 & Hq0P) & Hnpop).
                  assert (HpmP : ~ pos_lt pm P).
                  { intro H. rewrite shift_lt_P in Hlt by exact H. pose proof (mpos_gt_P i).
                    apply (pos_lt_irrefl P). eapply pos_lt_trans; eauto. eapply pos_lt_trans; eauto. }
                  assert (Hb' : blocker P x) by (split; [exact Hnewx|split; [exists q0; auto|exact Hnpop]]).
                  rewrite mpos_fst in Hrlt.
                  destruct (le_lt_dec (fst q0) r) as [Hle|Hgt].
                  -- destruct (P_blocker x Hb') as (_ & Hsafe).
                     destruct (Hsafe m pm b r q0 Hpm Hr Hq0 Hle Hrlt HpmP) as (px & bx & Hpx & Hpxlt).
                     exists (shift px), bx. split; [|apply shift_mono; exact Hpxlt].
                     apply new_pop_some. right. split; [eapply rem_pop_ne; eauto|]. eauto.
                  -- assert (Hq0pm : pos_lt q0 pm).
                     { eapply pos_lt_le_trans; [exact Hq0P|]. apply pos_not_lt_le. exact HpmP. }
                     destruct (a_pop_top _ _ Hc _ _ _ _ _ _ Hpm Hq0 Hq0pm Hr' Hgt) as (px & bx & Hpx & Hpxlt).
                     exists (shift px), bx. split; [|apply shift_mono; exact Hpxlt].
                     apply new_pop_some. right. split; [eapply rem_pop_ne; eauto|]. eauto.
                * (* x unmoved *)
                  rewrite shift_fst in Hrlt.
                  apply shift_lt_inv in Hlt.
                  destruct (a_pop_top _ _ Hc _ _ _ _ _ _ Hpm Hq0 Hlt Hr' Hrlt) as (px & bx & Hpx & Hpxlt).
                  exists (shift px), bx. split; [|apply shift_mono; exact Hpxlt].
                  apply new_pop_some. right. split; [eapply rem_pop_ne; eauto|]. eauto.
            (* a_inv_unique *)
            - intros x y p Hx Hy. apply new_inv_some in Hx. apply new_inv_some in Hy.
              destruct Hx as [(Hbx & i & Hi & ->)|(Hnbx & qx & Hqx & ->)];
                destruct Hy as [(Hby & j & Hj & Heq)|(Hnby & qy & Hqy & Heq)].
              + apply mpos_inj in Heq. subst j. eapply wf_inv_unique; eauto.
              + exfalso. destruct (blocker_key x Hbx) as (i' & Hi' & _ & HiT). rewrite Hi in Hi'. inversion Hi'; subst i'.
                exact (mpos_ne_shift i qy HiT Heq).
              + exfalso. destruct (blocker_key y Hby) as (j' & Hj' & _ & HjT). rewrite Hj in Hj'. inversion Hj'; subst j'.
                exact (mpos_ne_shift j qx HjT (eq_sym Heq)).
              + apply shift_inj in Heq. subst qy. eapply a_inv_unique; eauto.
            (* a_pop_unique *)
            - intros x y p b c Hx Hy. apply new_pop_some in Hx. apply new_pop_some in Hy.
              destruct Hx as [(-> & -> & ->)|(Hnex & px & Hpx & ->)];
                destruct Hy as [(-> & Heq & _)|(Hney & py & Hpy & Heq)].
              + reflexivity.
              + exfalso. exact (shift_ne_P py (eq_sym Heq)).
              + exfalso. exact (shift_ne_P px Heq).
              + apply shift_inj in Heq. subst py. eapply a_pop_unique; eauto.
            (* a_inv_pop_distinct *)
            - intros x y p b Hx Hy. apply new_inv_some in Hx. apply new_pop_some in Hy.
              destruct Hy as [(-> & -> & ->)|(Hney & py & Hpy & ->)].
              + destruct Hx as [(Hbx & i & Hi & Heq)|(Hnbx & qx & Hqx & Heq)].
                * exact (mpos_ne_P i (eq_sym Heq)).
                * exact (shift_ne_P qx (eq_sym Heq)).
              + destruct Hx as [(Hbx & i & Hi & Heq)|(Hnbx & qx & Hqx & Heq)].
                * destruct (blocker_key x Hbx) as (i' & Hi' & _ & HiT). rewrite Hi in Hi'. inversion Hi'; subst i'.
                  exact (mpos_ne_shift i py HiT (eq_sym Heq)).
                * apply shift_inj in Heq. subst. eapply a_inv_pop_distinct; eauto.
            (* a_nd *)
            - intros x i m r q Hpop Hi Hr Hle Hq Hrlt.
              assert (Hpop' : h_pop h' x = None /\ x <> n).
              { unfold new_pop in Hpop. destruct (node_eq_dec x n) as [->|Hne]; [discriminate|].
                destruct (h_pop h' x) as [pb|]; [discriminate|auto]. }
              destruct Hpop' as [Hpop' Hne].
              apply new_inv_some in Hq. destruct Hq as [(Hb & _)|(Hnb & q0 & Hq0 & ->)].
              + exfalso. destruct (P_blocker_popped x Hb) as (px & bx & Hpx & _). congruence.
              + rewrite shift_fst in Hrlt.
                assert (Hi' : tsa_node_inv (undo_rem s n T) x = Some i) by exact Hi.
                assert (Hr' : tsa_node_ret (undo_rem s n T) m = Some r) by exact Hr.
                destruct (a_nd _ _ Hc _ _ _ _ _ Hpop' Hi' Hr' Hle Hq0 Hrlt) as (pm & bm & Hpm & Hlt).
                exists (shift pm), bm. split; [|apply shift_mono; exact Hlt].
                apply new_pop_some. right. split; [eapply rem_pop_ne; eauto|]. eauto.
          Qed.

        End Construct.

        Lemma completed_case : exists h, acons s h.
        Proof.
          destruct exists_P as (P & HP & Hleast & HnoC).
          exists (new_hist P). exact (new_acons P HP Hleast HnoC).
        Qed.

      End Completed.

      (** ** The pending case: [n] has no push response, so no vertex is
          abstractly newer than it and the pop goes to the end. *)
      Definition pend_hist : History :=
        {| h_inv := h_inv h';
           h_pop := fun x => if node_eq_dec x n then Some (pair (pair T 0) a) else h_pop h' x |}.

      Lemma pending_case : tsa_node_ret s n = None -> acons s pend_hist.
      Proof.
        intros Hrn.
        assert (Hpop : forall x p b, h_pop pend_hist x = Some (pair p b) <->
          (x = n /\ p = pair T 0 /\ b = a) \/ (x <> n /\ h_pop h' x = Some (pair p b))).
        { intros x p b. simpl. destruct (node_eq_dec x n) as [->|Hne].
          - split; [intro H; inversion H; auto|]. intros [(_ & -> & ->)|(H & _)]; [reflexivity|congruence].
          - split; [auto|]. intros [(H & _)|(_ & H)]; [congruence|exact H]. }
        constructor.
        - intros x p Hp. destruct (a_inv_placed _ _ Hc _ _ Hp) as (H1 & H2 & H3). simpl in H1.
          split; [lia|split; assumption].
        - intros x i Hi. exact (a_total _ _ Hc x i Hi).
        - intros x p b Hp. apply Hpop in Hp. destruct Hp as [(-> & -> & ->)|(Hne & Hp)].
          + split; [simpl; lia|]. split.
            * destruct rem_inv_n as (i & Hi & _). destruct (a_total _ _ Hc n i Hi) as [q Hq].
              exists q. split; [exact Hq|]. pose proof (rem_inv_pos_lt n q Hq).
              destruct q. unfold pos_lt; simpl in *. lia.
            * pose proof rem_st_lt. exists st, T. split; [exact Hn|]. simpl. split; lia.
          + destruct (a_pop_placed _ _ Hc _ _ _ Hp) as (H1 & H2 & (st' & rt' & Hr & H3)). simpl in H1.
            split; [lia|]. split; [exact H2|]. exists st', rt'. rewrite (rem_other x Hne) in Hr. auto.
        - intros x b st' rt' Hr. destruct (node_eq_dec x n) as [->|Hne].
          + rewrite Hn in Hr. injection Hr as Hb _ _. subst b. exists (pair T 0).
            simpl. destruct (node_eq_dec n n); [reflexivity|congruence].
          + rewrite <- (rem_other x Hne) in Hr. destruct (a_removal_popped _ _ Hc _ _ _ _ Hr) as [p Hp].
            exists p. apply (proj2 (Hpop x p b)). right. auto.
        - intros m p b x q r Hp Hq Hlt Hr Hrlt. apply Hpop in Hp.
          destruct Hp as [(-> & -> & ->)|(Hne & Hp)]; [congruence|].
          assert (Hr' : tsa_node_ret (undo_rem s n T) m = Some r) by exact Hr.
          destruct (a_pop_top _ _ Hc _ _ _ _ _ _ Hp Hq Hlt Hr' Hrlt) as (px & bx & Hpx & Hpxlt).
          exists px, bx. split; [|exact Hpxlt]. apply Hpop. right. split; [eapply rem_pop_ne; eauto|exact Hpx].
        - exact (a_inv_unique _ _ Hc).
        - intros x y p b c Hx Hy. apply Hpop in Hx. apply Hpop in Hy.
          destruct Hx as [(-> & -> & ->)|(Hnex & Hx)]; destruct Hy as [(-> & Heq & _)|(Hney & Hy)].
          + reflexivity.
          + exfalso. pose proof (rem_pop_pos_lt y _ _ Hy). simpl in H. lia.
          + exfalso. pose proof (rem_pop_pos_lt x _ _ Hx). rewrite Heq in H. simpl in H. lia.
          + eapply a_pop_unique; eauto.
        - intros x y p b Hx Hy. apply Hpop in Hy.
          destruct Hy as [(-> & -> & ->)|(Hney & Hy)].
          + pose proof (rem_inv_pos_lt x _ Hx). simpl in H. lia.
          + eapply a_inv_pop_distinct; eauto.
        - intros x i m r q Hpop0 Hi Hr Hle Hq Hrlt.
          assert (Hpop' : h_pop h' x = None).
          { simpl in Hpop0. destruct (node_eq_dec x n); [discriminate|exact Hpop0]. }
          assert (Hne : x <> n).
          { simpl in Hpop0. destruct (node_eq_dec x n); [discriminate|assumption]. }
          assert (Hi' : tsa_node_inv (undo_rem s n T) x = Some i) by exact Hi.
          assert (Hr' : tsa_node_ret (undo_rem s n T) m = Some r) by exact Hr.
          destruct (a_nd _ _ Hc _ _ _ _ _ Hpop' Hi' Hr' Hle Hq Hrlt) as (pm & bm & Hpm & Hlt).
          exists pm, bm. split; [|exact Hlt]. apply Hpop. right. split; [eapply rem_pop_ne; eauto|exact Hpm].
      Qed.

      Lemma removal_acons : exists h, acons s h.
      Proof.
        destruct (tsa_node_ret s n) as [rn|] eqn:Hrn.
        - exact (completed_case rn Hrn).
        - exists pend_hist. exact (pending_case Hrn).
      Qed.

    End Removal.

    (** The key map records the snapshot time of the new removal. *)
    Lemma key_spec_rem (s : @TryStackAuxState A) n a st T kn :
      tsa_ghost_wf s -> tsa_now s = S T ->
      tsa_removals s n = Some (pair (pair a st) T) ->
      key_spec (undo_rem s n T) kn -> key_spec s (ext_key kn st (pair n false)).
    Proof.
      intros Hwf Hnow Hn [H1 H2].
      assert (Hsnap : ghost_event_at s st (GSnapOf n)) by (exists a, T; exact Hn).
      unfold ext_key. split.
      - intros t x. destruct (Nat.eq_dec t st) as [->|Hne].
        + split; [discriminate|]. intro Hx.
          pose proof (wf_unique _ Hwf st (GInv x) (GSnapOf n) Hx Hsnap). discriminate.
        + exact (H1 t x).
      - intros t m. destruct (Nat.eq_dec t st) as [->|Hne].
        + split.
          * intro H. inversion H; subst m. eauto.
          * intros (a' & rt' & Hm).
            pose proof (wf_unique _ Hwf st (GSnapOf m) (GSnapOf n) ltac:(exists a', rt'; exact Hm) Hsnap) as Heq.
            inversion Heq. reflexivity.
        + rewrite (H2 t m). simpl. destruct (node_eq_dec m n) as [->|Hne'].
          * split; [intros (a' & rt' & H); discriminate|].
            intros (a' & rt' & H). rewrite Hn in H. inversion H. congruence.
          * reflexivity.
    Qed.

    Lemma removal_case (s : @TryStackAuxState A) n a st T h kn :
      tsa_ghost_wf s -> tsa_now s = S T ->
      tsa_removals s n = Some (pair (pair a st) T) ->
      acons (undo_rem s n T) h -> key_spec (undo_rem s n T) kn ->
      exists h' kn', acons s h' /\ key_spec s kn'.
    Proof.
      intros Hwf Hnow Hn Hc Hk.
      destruct (removal_acons s n a st T h Hwf Hnow Hn Hc) as [h' Hc'].
      exists h', (ext_key kn st (pair n false)). split; [exact Hc'|].
      eapply key_spec_rem; eauto.
    Qed.

    (** * The trace theorem *)

    Definition empty_history : History :=
      {| h_inv := fun _ => None; h_pop := fun _ => None |}.

    Theorem trace_abs :
      forall T (s : @TryStackAuxState A),
        tsa_ghost_wf s -> tsa_now s = T ->
        exists h kn, acons s h /\ key_spec s kn.
    Proof.
      induction T as [|T IH]; intros s Hwf Hnow.
      - exists empty_history, (fun _ => None).
        assert (Hnoinv : forall n i, tsa_node_inv s n <> Some i).
        { intros n i Hi. pose proof (wf_inv_now _ Hwf _ _ Hi). lia. }
        assert (Hnorem : forall n rec, tsa_removals s n <> Some rec).
        { intros n [[a st] rt] Hr. destruct (wf_removal _ Hwf _ _ _ _ Hr) as (_ & H & _). lia. }
        split.
        + constructor; simpl; try discriminate.
          * intros n i Hi. exfalso. eapply Hnoinv; eauto.
          * intros n a st rt Hr. exfalso. eapply Hnorem; eauto.
        + split.
          * intros t x. split; [discriminate|]. intro H. exfalso. eapply Hnoinv; eauto.
          * intros t n. split; [discriminate|]. intros (a & rt & H). exfalso. eapply Hnorem; eauto.
      - destruct (classic (exists x, tsa_node_inv s x = Some T)) as [[x Hx]|Hnoinv].
        + destruct (IH (undo_inv s x T) (undo_inv_wf s x T Hwf Hnow Hx) eq_refl)
            as (h & kn & Hc & Hk).
          exists (ext_inv_hist h x T), (ext_key kn T (pair x true)).
          split; [apply acons_undo_inv; auto|apply key_spec_undo_inv; auto].
        + destruct (classic (exists x, tsa_node_ret s x = Some T)) as [[x Hx]|Hnoret].
          * destruct (IH (undo_ret s x T) (undo_ret_wf s x T Hwf Hnow Hx) eq_refl)
              as (h & kn & Hc & Hk).
            exists h, kn. split; [eapply acons_undo_ret; eauto|].
            eapply key_spec_lift; [| |exact Hk]; reflexivity.
          * destruct (classic (exists b, TMap.find b (tsa_snap_time s) = Some T)) as [[b Hb]|Hnosnap].
            -- destruct (IH (undo_snap s b T) (undo_snap_wf s b T Hwf Hnow Hb) eq_refl)
                 as (h & kn & Hc & Hk).
               exists h, kn. split.
               ++ eapply acons_now_lift; [| | | | |exact Hc]; simpl; try reflexivity. lia.
               ++ eapply key_spec_lift; [| |exact Hk]; reflexivity.
            -- destruct (classic (exists n a st, tsa_removals s n = Some (pair (pair a st) T)))
                 as [(n & a & st & Hn)|Hnorem].
               ++ destruct (IH (undo_rem s n T) (undo_rem_wf s n a st T Hwf Hnow Hn) eq_refl)
                    as (h & kn & Hc & Hk).
                  eapply removal_case; eauto.
               ++ assert (Hno : forall ev, ~ ghost_event_at s T ev).
                  { intros ev Hev. destruct ev; simpl in Hev.
                    - apply Hnoinv. eauto.
                    - apply Hnoret. eauto.
                    - apply Hnosnap. eauto.
                    - destruct Hev as (a & st & Hev). apply Hnorem. eauto.
                    - destruct Hev as (a & rt & Hev).
                      destruct (wf_removal _ Hwf _ _ _ _ Hev) as (H1 & H2 & _). lia. }
                  destruct (IH (with_now s T) (with_now_wf s T Hwf Hnow Hno) eq_refl)
                    as (h & kn & Hc & Hk).
                  exists h, kn. split.
                  ** eapply acons_now_lift; [| | | | |exact Hc]; simpl; try reflexivity. lia.
                  ** eapply key_spec_lift; [| |exact Hk]; reflexivity.
    Qed.

    Theorem trace_theorem (s : @TryStackAuxState A) :
      tsa_ghost_wf s -> exists h, consistent s h.
    Proof.
      intros Hwf.
      destruct (trace_abs (tsa_now s) s Hwf eq_refl) as (h & kn & Hc & Hk).
      exists (compress h kn). apply compress_consistent; assumption.
    Qed.

  End Trace.
End TryStackTrace.
