Require Import Relations RelationClasses Relators.
Require Import List Maps.
Require Import Coqlib.
Require Import CallconvAlgebra_.
Require Import LanguageInterface_ Events Globalenvs Smallstep_ CategoricalComp FlatComp.
Require Import Memory Values.
Require Import Linking.
Require Import Lifting AbstractStateRel.

Generalizable All Variables.

(* A li_func convert from one language interface to another. This is useful
   because equivalence on the level of language interfaces can't be defined
   as definitional equality. *)
Record li_func (liA liB: language_interface) :=
  mk_li_func {
      query_func: query liB -> query liA;
      reply_func: reply liB -> reply liA;
    }.
Arguments query_func {liA liB} _ _.
Arguments reply_func {liA liB} _ _.

Section APPLY.

  Context {liA1 liA2 liB1 liB2 S} (L: lts liA1 liB1 S)
          (FA: li_func liA1 liA2) (FB: li_func liB1 liB2).

  Definition lts_map_outgoing: lts liA1 liB2 S :=
    {|
      genvtype := genvtype L;
      globalenv := globalenv L;
      step := step L;
      initial_state q s := initial_state L (query_func FB q) s;
      at_external := at_external L;
      after_external := after_external L;
      final_state s r := final_state L s (reply_func FB r);
    |}.

  Definition lts_map_incoming: lts liA2 liB1 S :=
    {|
      genvtype := genvtype L;
      globalenv := globalenv L;
      step := step L;
      initial_state := initial_state L;
      at_external s q := at_external L s (query_func FA q);
      after_external s r s' := after_external L s (reply_func FA r) s';
      final_state := final_state L;
    |}.

End APPLY.

Definition map_outgoing {liA liB1 liB2} (L: semantics liA liB1) (F: li_func liB1 liB2) :=
  {|
    skel := skel L;
    activate se := lts_map_outgoing (L se) F;
    footprint := footprint L;
  |}.

Definition map_incoming {liA1 liA2 liB} (L: semantics liA1 liB) (F: li_func liA1 liA2) :=
  {|
    skel := skel L;
    activate se := lts_map_incoming (L se) F;
    footprint := footprint L;
  |}.

Infix "##" := map_incoming (at level 50): lts_scope.
Infix "$$" := map_outgoing (at level 50): lts_scope.

(* The generated definition looks funky
   Try use idtac as default *)
Program Definition li_func_null {K}: li_func (li_null @ K) li_null :=
  {|
    query_func q := match q with end;
    reply_func r := match r with end;
  |}.

Program Definition li_func_k {li K1 K2}: li_func ((li@K1)@K2) (li@(K1*K2)) :=
  {|
    query_func '(q, k) := ((q, fst k), snd k);
    reply_func '(r, k) := ((r, fst k), snd k);
  |}.

Definition lift_layer {li K} (L: semantics li_null li): semantics li_null (li@K) :=
  L@K ## li_func_null.

Definition lift_layer_k {li K1 K2} (L: semantics li_null (li@K1)): semantics li_null (li@(K1*K2)) :=
  L@K2 ## li_func_null $$ li_func_k.

Infix "⊗" := kcc_tensor (at level 50, left associativity) : cc_scope.

Section TENSOR.

  Context {K1 K2} (L1: semantics li_null (li_c@K1)) (L2: semantics li_null (li_c@K2)).
  Context {J1 J2} (jcc: crel J1 J2) (kcc: callconv (li_c@K1) (li_c@K2)).
  Context (HL: fsim_components 1 kcc L1 L2).

  (* One more condition we need from crel maybe match_query implies match_reply
     if the memory is unchanged on the blocks in the crel *)

  Inductive state_match:

  Lemma lift_layer_fsim: forward_simulation 1 (kcc ⊗ jcc) (lift_layer_k L1) (lift_layer_k L2).
  Proof.


End TENSOR.

Class mem_ops: Type :=
  {
    split: mem -> mem * mem;
    combine: mem * mem -> mem;
  }.

Class CallConv_Invariants `(cca: callconv (li_c@K1a) (li_c@K2a))
      `(ccb: callconv (li_c@K1b) (li_c@K2b)) :=
  {
    op :> mem_ops;

    (* For certified abstraction layers, the calling conventions essentially
       captures the abstraction from concrete C values in particular memory
       blocks to abstract data. The other memory blocks in the memory should not
       affect the abstraction relation. For example, in the following diagram,
       `m2a` is part of a larger memory `m2` and the abstract relation from the
       calling convention `cca` translates `m2a` to abstract data in
       `k1a`. Then, if we extract the same blocks from the source program memory
       `m1` and obtain `m1a`, we get the "core" of the abstraction
       relation. That is to say, if we have (m1, k1a) related to (m2, k2a), we
       can strip off the unused blocks from `m1` and `m2` to get the fact that
       (m1a, k1a) is related to (m2a, k1a). For the other hand, if we have (m1a,
       k1a) related to (m2a, k2a), we can add a few extra blocks into the memory
       as long as they don't interfere the blocks in the "core" part

       In the end, the operations in `mem_ops` are parametrized by the "core" of
       the abstraction relations, which should be several block identifiers. The
       layers being composed in this ways should not interfering private states
       so the composition on the abstraction relations should witness an
       evidence of such non-interference, which I think can be interpreted as a
       pair of split and combine operations. (Maybe a few more extra properties
       are required) *)

    (*
       (m1a, _)  k1a             m1a   k1a
         |      / |               |    /|
         |     /  |      <-->     |   / |
         |    /   |               |  /  |
         |   /    |               | /   |
       (m2a, _)  k2a             m2a   k2a  *)

    (* Extract the "core" part from an inclusive abstraction relation *)
    match_query_core1 wa vf1 args1 sg1 m1 k1a vf2 args2 sg2 m2 k2a:
      match_query cca wa ((cq vf1 args1 sg1 m1), k1a) ((cq vf2 args2 sg2 m2), k2a) ->
      let '(m1a, _) := split m1 in
      let '(m2a, _) := split m2 in
      match_query cca wa ((cq vf1 args1 sg1 m1a), k1a) ((cq vf2 args2 sg2 m2a), k2a);

    match_query_core2 wb vf1 args1 sg1 m1 k1b vf2 args2 sg2 m2 k2b:
      match_query ccb wb ((cq vf1 args1 sg1 m1), k1b) ((cq vf2 args2 sg2 m2), k2b) ->
      let '(_, m1b) := split m1 in
      let '(_, m2b) := split m2 in
      match_query ccb wb ((cq vf1 args1 sg1 m1b), k1b) ((cq vf2 args2 sg2 m2b), k2b);

    (* Add several extras blocks to the "core" part of the abstraction relation *)
    match_reply_core1 wa ret1 m1a k1a ret2 m2a k2a m1b m2b:
      match_reply cca wa ((cr ret1 m1a), k1a) ((cr ret2 m2a), k2a) ->
      let m1 := combine (m1a, m1b) in
      let m2 := combine (m2a, m2b) in
      match_reply cca wa ((cr ret1 m1), k1a) ((cr ret2 m2), k2a);

    match_reply_core2 wb ret1 m1a k1b ret2 m2a k2b m1b m2b:
      match_reply ccb wb ((cr ret1 m1b), k1b) ((cr ret2 m2b), k2b) ->
      let m1 := combine (m1a, m1b) in
      let m2 := combine (m2a, m2b) in
      match_reply ccb wb ((cr ret1 m1), k1b) ((cr ret2 m2), k2b);

    (* The invariant is essentially a relation represents the following
       diagram. We need it for matching the states of the inactive component. *)
    (*
        m1a     k1a
         |     / |
         |    /  |
         |   /   |
         |  /    |
         | /     |
        m2a     k2a
     *)
    inv1: ccworld cca -> mem * K1a -> mem * K2a -> Prop;
    inv2: ccworld ccb -> mem * K1b -> mem * K2b -> Prop;

    inv1_pre q1 q2 k1a k2a wa:
      match_query cca wa (q1, k1a) (q2, k2a) ->
      let 'cq _ _ _ m1 := q1 in
      let 'cq _ _ _ m2 := q2 in
      let '(m1a, _) := split m1 in
      let '(m2a, _) := split m2 in
      inv1 wa (m1a, k1a) (m2a, k2a);

    inv1_post wa wb ret1 ret2 m1a k1a m2a k2a m1b' m2b' k1b' k2b':
      inv1 wa (m1a, k1a) (m2a, k2a) ->
      let r1 := cr ret1 (combine (m1a, m1b')) in
      let r2 := cr ret2 (combine (m2a, m2b')) in
      match_reply ccb wb (cr ret1 m1b', k1b') (cr ret2 m2b', k2b') ->
      match_reply cca wa (r1, k1a) (r2, k2a);

    inv2_pre q1 q2 k1b k2b wb:
      match_query ccb wb (q1, k1b) (q2, k2b) ->
      let 'cq _ _ _ m1 := q1 in
      let 'cq _ _ _ m2 := q2 in
      let '(_, m1b) := split m1 in
      let '(_, m2b) := split m2 in
      inv2 wb (m1b, k1b) (m2b, k2b);

    inv2_post wa wb ret1 ret2 m1b k1b m2b k2b m1a' m2a' k1a' k2a':
      inv2 wb (m1b, k1b) (m2b, k2b) ->
      let r1 := cr ret1 (combine (m1a', m1b)) in
      let r2 := cr ret2 (combine (m2a', m2b)) in
      match_reply cca wa (cr ret1 m1a', k1a') (cr ret2 m2a', k2a') ->
      match_reply ccb wb (r1, k1b) (r2, k2b);

  }.

Coercion op: CallConv_Invariants >-> mem_ops.

Module Layer.

  Section COMP.
    Context {K1 K2: Type}.
    Context (L1: semantics li_null (li_c@K1)) (L2: semantics li_null (li_c@K2)).
    Context (M: mem_ops).

    Section WITH_SE.
      Context (se: Genv.symtbl).

      Variant tensor_state :=
      | tensor_st1 (s:  Smallstep_.state L1) (m: mem) (k: K2)
      | tensor_st2 (s:  Smallstep_.state L2) (m: mem) (k: K1).

      Inductive tensor_step: tensor_state -> trace -> tensor_state -> Prop :=
      | tensor_step1 s t s' m k:
          Step (L1 se) s t s' ->
          tensor_step (tensor_st1 s m k) t (tensor_st1 s' m k)
      | tensor_step2 s t s' m k:
          Step (L2 se) s t s' ->
          tensor_step (tensor_st2 s m k) t (tensor_st2 s' m k).

      Inductive tensor_initial_state: query (li_c@(K1 * K2)) -> tensor_state -> Prop :=
      | initial_state1 s k1 k2 vf sg args m:
          let ms := split m in
          initial_state (L1 se) (cq vf sg args (fst ms), k1) s ->
          tensor_initial_state ((cq vf sg args m), (k1, k2)) (tensor_st1 s (snd ms) k2)
      | initial_state2 s k1 k2 vf sg args m:
          let ms := split m in
          initial_state (L2 se) (cq vf sg args (snd ms), k2) s ->
          tensor_initial_state ((cq vf sg args m), (k1, k2)) (tensor_st2 s (fst ms) k1).

      Inductive tensor_at_external: tensor_state -> query li_null -> Prop := .

      Inductive tensor_after_external:
        tensor_state -> reply li_null -> tensor_state -> Prop := .

      Inductive tensor_final_state: tensor_state -> reply (li_c@(K1 * K2)) -> Prop :=
      | final_state1 s k1 k2 ret m1 m2:
          let m := combine (m1, m2) in
          final_state (L1 se) s ((cr ret m1), k1) ->
          tensor_final_state (tensor_st1 s m2 k2) ((cr ret m), (k1, k2))
      | final_state2 s k1 k2 ret m1 m2:
          let m := combine (m1, m2) in
          final_state (L2 se) s ((cr ret m2), k2) ->
          tensor_final_state (tensor_st2 s m1 k1) ((cr ret m), (k1, k2)).

      Lemma star_tensor_step1 s t s' m k:
        Star (L1 se) s t s' ->
        star (fun _ => tensor_step) tt (tensor_st1 s m k) t (tensor_st1 s' m k).
      Proof.
        induction 1; [eapply star_refl | eapply star_step]; eauto.
        constructor; auto.
      Qed.

      Lemma star_tensor_step2 s t s' m k:
        Star (L2 se) s t s' ->
        star (fun _ => tensor_step) tt (tensor_st2 s m k) t (tensor_st2 s' m k).
      Proof.
        induction 1; [eapply star_refl | eapply star_step]; eauto.
        constructor; auto.
      Qed.

      Lemma plus_tensor_step1 s t s' m k:
        Plus (L1 se) s t s' ->
        plus (fun _ => tensor_step) tt (tensor_st1 s m k) t (tensor_st1 s' m k).
      Proof.
        destruct 1; econstructor; eauto using tensor_step1, star_tensor_step1.
      Qed.

      Lemma plus_tensor_step2 s t s' m k:
        Plus (L2 se) s t s' ->
        plus (fun _ => tensor_step) tt (tensor_st2 s m k) t (tensor_st2 s' m k).
      Proof.
        destruct 1; econstructor; eauto using tensor_step2, star_tensor_step2.
      Qed.

    End WITH_SE.

    Program Definition tensor_semantics' sk: semantics li_null (li_c@(K1 * K2)) :=
      {|
      activate se :=
        {|
          step ge := tensor_step se;
          initial_state := tensor_initial_state se;
          at_external := tensor_at_external;
          after_external := tensor_after_external;
          final_state := tensor_final_state se;
          globalenv := tt;
        |};
      skel := sk;
      footprint id := footprint L1 id \/ footprint L2 id;
      |}.

  End COMP.

  Section FSIM.

    Context `(L1a: semantics li_null (li_c@K1a))
            `(L1b: semantics li_null (li_c@K1b))
            `(L2a: semantics li_null (li_c@K2a))
            `(L2b: semantics li_null (li_c@K2b))
            (cca: callconv (li_c@K1a) (li_c@K2a))
            (ccb: callconv (li_c@K1b) (li_c@K2b))
            (HL1: fsim_components cc_id cca L1a L2a)
            (HL2: fsim_components cc_id ccb L1b L2b).
    Context (INV: CallConv_Invariants cca ccb).
    Context (se1 se2: Genv.symtbl) (w: ccworld (kcc_tensor cca ccb))
            (Hse: match_senv (kcc_tensor cca ccb) w se1 se2)
            (Hse1: Genv.valid_for (skel L1a) se1)
            (Hse2: Genv.valid_for (skel L1b) se1).
    Variable (sk: AST.program unit unit).

    Inductive index: Type :=
    | index1 (i: fsim_index HL1)
    | index2 (i: fsim_index HL2).

    Variant order: index -> index -> Prop :=
    | order1 i1 i2: fsim_order HL1 i1 i2 -> order (index1 i1) (index1 i2)
    | order2 i1 i2: fsim_order HL2 i1 i2 -> order (index2 i1) (index2 i2).

    Arguments tensor_st1 {K1 K2 L1 L2}.
    Arguments tensor_st2 {K1 K2 L1 L2}.
    Variant match_states: index -> tensor_state L1a L1b
                          -> tensor_state L2a L2b -> Prop :=
    | match_states1 i s1 s2 m1 m2 k1 k2:
        fsim_match_states HL1 se1 se2 (fst w) i s1 s2 ->
        inv2 (snd w) (m1, k1) (m2, k2) ->
        match_states (index1 i) (tensor_st1 s1 m1 k1)
                     (tensor_st1 s2 m2 k2)
    | match_states2 i s1 s2 m1 m2 k1 k2:
        fsim_match_states HL2 se1 se2 (snd w) i s1 s2 ->
        inv1 (fst w) (m1, k1) (m2, k2) ->
        match_states (index2 i) (tensor_st2 s1 m1 k1)
                     (tensor_st2 s2 m2 k2).

    Local Lemma semantics_simulation sk1 sk2:
      fsim_properties cc_id (kcc_tensor cca ccb) se1 se2 w
                      (tensor_semantics' L1a L1b INV sk1 se1)
                      (tensor_semantics' L2a L2b INV sk2 se2)
                      index order match_states.
    Proof.
      constructor.
      - intros [q1 [k1a k1b]] [q2 [k2a k2b]] s1 Hq H. inv H;
        destruct ms as [m1a m1b] eqn: Hm1; destruct w as [wa wb] eqn: Hw;
        destruct q2 as [? ? ? m2]; destruct (split m2) as [m2a m2b] eqn: Hm2.
        + pose proof (fsim_lts HL1 _ _ (proj1 Hse) Hse1).
          edestruct @fsim_match_initial_states as (idx & s' & H' & Hs); eauto.
          instantiate (1 := ({| cq_vf := cq_vf; cq_sg := cq_sg; cq_args := cq_args; cq_mem := fst (m2a, m2b) |}, k2a)).
          exploit match_query_core1. apply (proj1 Hq).
          cbn in *. subst ms. rewrite Hm1. rewrite Hm2. auto.
          eexists (index1 idx), (tensor_st1 s' (snd (split m2)) k2b).
          split.
          * constructor. congruence.
          * constructor. subst w. apply Hs.
            pose proof (inv2_pre _ _ _ _ _ (proj2 Hq)). cbn in H0.
            cbn in *. subst ms. rewrite Hm1 in H0. rewrite Hm2 in H0. rewrite Hm2. subst w. apply H0.
        + pose proof (fsim_lts HL2 _ _ (proj2 Hse) Hse2).
          edestruct @fsim_match_initial_states as (idx & s' & H' & Hs); eauto.
          instantiate (1 := ({| cq_vf := cq_vf; cq_sg := cq_sg; cq_args := cq_args; cq_mem := snd (m2a, m2b) |}, k2b)).
          exploit match_query_core2. apply (proj2 Hq).
          cbn in *. subst ms. rewrite Hm1. rewrite Hm2. auto.
          eexists (index2 idx), (tensor_st2 s' (fst (split m2)) k2a).
          split.
          * constructor. congruence.
          * constructor. subst w. apply Hs.
            pose proof (inv1_pre _ _ _ _ _ (proj1 Hq)). cbn in H0.
            cbn in *. subst ms; rewrite Hm1 in H0. rewrite Hm2 in H0. rewrite Hm2. subst w. apply H0.
      - intros i s1 s2 [r1 [k1a k1b]] Hs H. inv H;
        destruct w as [wa wb] eqn: Hw; inv Hs; cbn [fst snd] in *.
        + pose proof (fsim_lts HL1 _ _ (proj1 Hse) Hse1).
          edestruct @fsim_match_final_states as (r2 & H' & Hr); eauto. destruct r2 as [r2 k2a].
          destruct r2 as [? m4] eqn: Hr2.
          eexists (({|cr_retval := cr_retval; cr_mem := combine (m4, m3)|}, (k2a, k2))).
          split.
          * constructor. auto.
          * constructor.
            exploit match_reply_core1. apply Hr. eauto.
            exploit inv2_post. apply H6. apply Hr. auto.
        + pose proof (fsim_lts HL2 _ _ (proj2 Hse) Hse2).
          edestruct @fsim_match_final_states as (r2 & H' & Hr); eauto. destruct r2 as [r2 k2b].
          destruct r2 as [? m4] eqn: Hr2.
          eexists (({|cr_retval := cr_retval; cr_mem := combine (m3, m4)|}, (k2, k2b))).
          split.
          * constructor. auto.
          * constructor.
            exploit inv1_post. apply H6. apply Hr. auto.
            exploit match_reply_core2. apply Hr. eauto.
      - intros. easy.
      - intros. inv H; inv H0; destruct w as [wa wb] eqn: Hw.
        + pose proof (fsim_lts HL1 _ _ (proj1 Hse) Hse1).
          edestruct @fsim_simulation as (idx' & s2' & Hs2' & Hs'); eauto.
          eexists (index1 idx'), (tensor_st1 s2' m2 k2).
          split.
          * destruct Hs2'; [left | right].
            now apply plus_tensor_step1.
            split; [apply star_tensor_step1 | constructor ]; apply H0.
          * constructor; subst w. apply Hs'. auto.
        + pose proof (fsim_lts HL2 _ _ (proj2 Hse) Hse2).
          edestruct @fsim_simulation as (idx' & s2' & Hs2' & Hs'); eauto.
          eexists (index2 idx'), (tensor_st2 s2' m2 k2).
          split.
          * destruct Hs2'; [left | right].
            now apply plus_tensor_step2.
            split; [apply star_tensor_step2 | constructor ]; apply H0.
          * constructor; subst w. apply Hs'. auto.
    Qed.
  End FSIM.

  Lemma tensor_compose_simulation'
        `(cca: callconv (li_c@K1a) (li_c@K2a))
        `(ccb: callconv (li_c@K1b) (li_c@K2b))
        (INV: CallConv_Invariants cca ccb)
        L1a L2a L1b L2b sk:
    forward_simulation cc_id cca L1a L2a ->
    forward_simulation cc_id ccb L1b L2b ->
    linkorder (skel L1a) sk ->
    linkorder (skel L1b) sk ->
    forward_simulation cc_id (kcc_tensor cca ccb)
                       (tensor_semantics' L1a L1b INV sk)
                       (tensor_semantics' L2a L2b INV sk).
  Proof.
    intros [HL1] [HL2] Hk1 Hk2. constructor.
    eapply Forward_simulation
      with (order _ _ _ _ cca ccb HL1 HL2)
           (match_states _ _ _ _ cca ccb HL1 HL2 INV).
    - auto.
    - intros. cbn.
      rewrite (fsim_footprint HL1).
      rewrite (fsim_footprint HL2). reflexivity.
    - intros. eapply semantics_simulation; eauto.
      eapply Genv.valid_for_linkorder; eauto.
      eapply Genv.valid_for_linkorder; eauto.
    - clear - HL1 HL2. intros [|].
      + induction (fsim_order_wf HL1 i) as [x Hx IHx].
        constructor. intros z Hxz. inv Hxz. apply IHx; eauto.
      + induction (fsim_order_wf HL2 i) as [x Hx IHx].
        constructor. intros z Hxz. inv Hxz. apply IHx; eauto.
  Qed.

End Layer.

(* The code below doesn't work because it tries to define the tensor product
   composition on transition systems with abstract data in general. It doesn't
   work because we want to look into the queries and replies to obtain the
   memory state, so to speak. Therefore, we turned to the concrete language
   interface li_c. But it's still a problem that for transition systems L in
   general we can't obtain the memory state from the (state L) *)

(* Module Legacy. *)
(*   (* Note for L@K: liA@K ↠ liB@K, the abstract state is only updated via external *)
(*    calls. But for a transition system of type liA@K ↠ liB@K or even liA@K1 ↠ *)
(*    liB@K2 in general, the abstract state may change at any transition step. But *)
(*    here we limit our scope to the special case where internal steps do not *)
(*    modify the abstract state *) *)

(*   Section COMP. *)
(*     (* TODO: notation precedence *) *)
(*     Context {I} {K: I -> Type} *)
(*             {liA liB} (L: forall i, semantics (liA@(K i)) (liB@(K i))). *)

(*     (* Isomorphic to K0 * K1 * K2 * ... if indexed by natural number *) *)
(*     Notation Ki := (forall i, K i). *)

(*     Hypothesis I_dec: forall (i j: I), {i = j} + {i <> j}. *)

(*     Definition update_at (k: Ki) (j: I) (kj: K j): Ki. *)
(*     Proof. *)
(*       intros i. destruct (I_dec i j). *)
(*       - subst. exact kj. *)
(*       - exact (k i). *)
(*     Defined. *)

(*     Section WITH_SE. *)
(*       Context (se: Genv.symtbl). *)

(*       (* Even though s has type (state (L i)), it should not be understood as the *)
(*        state specific to the i-th component like in the flat composition. It *)
(*        should be a directed join of all the states for the transition systems *)
(*        being composed, where the state information from every component is *)
(*        kept. It would be more appropriate that we define a new type for the *)
(*        state that is independent of i, which is the way we deal with the *)
(*        abstract data. *)

(*        The all-inclusive abstract data k has a similar flavor but since two *)
(*        abstract types K1 and K2 are not necessarily compatible they are first *)
(*        lifted to K1*K2. Each field in the composite abstract data comes from its *)
(*        respective component *) *)

(*       (* An alternative approach would be to store  *) *)

(*       (* (mem, k_i)  (k_1, k_2, ... k_n) *) *)
(*       (* (m_1, m_2, m_3, .. m_n) *) *)

(*       (* L_int ⊗ L_arr *) *)

(*       (* L1 : 1 -> C ≤{1 -> cc1} L2 : 1 -> C@K2 *) *)
(*       (* L3 : 1 -> C ≤{1 -> cc2} L4 : 1 -> C@K4 *) *)

(*       (* cc1 : query(L1) ↔ query(L2) * K2 *) *)
(*       (* cc2 : query(L3) ↔ qeury(L4) * K4 *) *)

(*       (* L1 ⊗ L3 : 1 -> C *) *)
(*       (* L2 ⊗ L4 : 1 -> C@(K2*K4) *) *)
(*       (* L1 ⊗ L3 ≤{1 -> cc} L2 ⊗ L4 *) *)

(*       (* cc : query(L1 ⊗ L3) ≅ mem ↔ query(L2 ⊗ L4) ≅ mem * K2 * K4 *) *)

(*       Variant tensor_state := *)
(*         tensor_st (i: I) (s: Smallstep_.state (L i)) (k: Ki). *)

(*       Inductive tensor_step: tensor_state -> trace -> tensor_state -> Prop := *)
(*       | step_intro i s t s' k: *)
(*           Step (L i se) s t s' -> *)
(*           tensor_step (tensor_st i s k) t (tensor_st i s' k). *)

(*       Inductive tensor_initial_state: query (liB@Ki) -> tensor_state -> Prop := *)
(*       | initial_state_intro i s k q: *)
(*           initial_state (L i se) (q, k i) s -> *)
(*           tensor_initial_state (q, k) (tensor_st i s k). *)

(*       Inductive tensor_at_external: tensor_state -> query (liA@Ki) -> Prop := *)
(*       | at_external_intro i s k q: *)
(*           at_external (L i se) s (q, k i) -> *)
(*           tensor_at_external (tensor_st i s k) (q, k). *)

(*       (* This is the only transition where the abstract data is allowed to be *)
(*        updated and only i-th state can be updated *) *)
(*       Inductive tensor_after_external: *)
(*         tensor_state -> reply (liA@Ki) -> tensor_state -> Prop := *)
(*       | after_external_intro i s s' k k' r kr: *)
(*           (forall j, i <> j -> k j = k' j) -> k' i = kr -> *)
(*           after_external (L i se) s (r, kr) s' -> *)
(*           tensor_after_external (tensor_st i s k) (r, k') (tensor_st i s' k'). *)

(*       Inductive tensor_final_state: tensor_state -> reply (liB@Ki) -> Prop := *)
(*       | final_state_intro i s k r: *)
(*           final_state (L i se) s (r, k i) -> *)
(*           tensor_final_state (tensor_st i s k) (r, k). *)

(*       Lemma star_internal i s t s' k: *)
(*         Star (L i se) s t s' -> *)
(*         star (fun _ => tensor_step) tt (tensor_st i s k) t (tensor_st i s' k). *)
(*       Proof. *)
(*         induction 1; [eapply star_refl | eapply star_step]; eauto. *)
(*         constructor; auto. *)
(*       Qed. *)

(*       Lemma plus_internal i s t s' k: *)
(*         Plus (L i se) s t s' -> *)
(*         plus (fun _ => tensor_step) tt (tensor_st i s k) t (tensor_st i s' k). *)
(*       Proof. *)
(*         destruct 1; econstructor; eauto using step_intro, star_internal. *)
(*       Qed. *)

(*     End WITH_SE. *)

(*     Program Definition tensor_semantics' sk: semantics (liA@Ki) (liB@Ki) := *)
(*       {| *)
(*       activate se := *)
(*         {| *)
(*           step ge := tensor_step se; *)
(*           initial_state := tensor_initial_state se; *)
(*           at_external := tensor_at_external se; *)
(*           after_external := tensor_after_external se; *)
(*           final_state := tensor_final_state se; *)
(*           globalenv := tt; *)
(*         |}; *)
(*       skel := sk; *)
(*       footprint id := exists i, footprint (L i) id; *)
(*       |}. *)

(*   End COMP. *)

(*   Require Import AbstractStateRel. *)
(*   Require SmallstepLinking_. *)

(*   Section FSIM. *)

(*     Generalizable All Variables. *)

(*     Context {I} (K1 K2: I -> Type) (Hi: Inhabited I) *)
(*             `(L1: forall i, semantics (liA1@(K1 i)) (liB1@(K1 i))) *)
(*             `(L2: forall i, semantics (liA2@(K2 i)) (liB2@(K2 i))) *)
(*             (cca: forall i, callconv (liA1@(K1 i)) (liA2@(K2 i))) *)
(*             (ccb: forall i, callconv (liB1@(K1 i)) (liB2@(K2 i))) *)
(*             (HL: forall i, fsim_components (cca i) (ccb i) (L1 i) (L2 i)) *)
(*             (se1 se2: Genv.symtbl) (w: ccworld (kcc_tensor ccb)) *)
(*             (Hse: match_senv (kcc_tensor ccb) w se1 se2) *)
(*             (Hse1: forall i, Genv.valid_for (skel (L1 i)) se1). *)
(*     Variable (sk: AST.program unit unit). *)

(*     Notation index := ({i & fsim_index (HL i)} * (forall i, K1 i) * (forall i, K2 i))%type. *)
(*     Variant order: index -> index -> Prop := *)
(*     | order_intro i x y kx1 kx2 ky1 ky2: *)
(*         fsim_order (HL i) x y -> order (existT _ i x, kx1, kx2) (existT _ i y, ky1, ky2). *)

(*     Variant match_states: index -> tensor_state L1 -> tensor_state L2 -> Prop := *)
(*     | match_tensor_st i idx k1 k2 s1 s2 ks1 ks2: *)
(*         fsim_match_states (HL i) se1 se2 (w i) idx s1 s2 -> *)
(*         (forall j, j <> i -> ks1 j = k1 j /\ ks2 j = k2 j) -> *)
(*         match_states (existT _ i idx, k1, k2) (tensor_st _ i s1 ks1) (tensor_st _ i s2 ks2). *)

(*     Local Lemma semantics_simulation sk1 sk2: *)
(*       fsim_properties (kcc_tensor cca) (kcc_tensor ccb) se1 se2 w *)
(*                       (tensor_semantics' L1 sk1 se1) *)
(*                       (tensor_semantics' L2 sk2 se2) *)
(*                       index order match_states. *)
(*     Proof. *)
(*       split. *)
(*       - intros [q1 kq1] [q2 kq2] s Hq H. inv H. *)
(*         pose proof (fsim_lts (HL i) _ _ (Hse i) (Hse1 i)). *)
(*         edestruct @fsim_match_initial_states as (idx & s' & Hs' & Hs); eauto. *)
(*         eexists (existT _ i idx, kq1, kq2), _. split; econstructor; eauto. *)
(*       - intros ((idx, k1), k2) s1 s2 [r kr] Hs H. inv H. *)
(*         inv Hs. SmallstepLinking_.subst_dep. *)
(*         pose proof (fsim_lts (HL i) _ _ (Hse i) (Hse1 i)). *)
(*         edestruct @fsim_match_final_states as (r' & H' & Hr'); eauto. *)
(*         destruct r' as [r' kr']. eexists (_, _). split. *)
(*         + admit. *)
(*         + intros j. *)
(*     Abort All. *)

(*   End FSIM. *)
(* End Legacy. *)
