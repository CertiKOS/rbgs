From compcert Require Import
     Integers Coqlib Maps
     Memory AST Values
     Globalenvs Linking Ctypes.
From clightp Require Import
  ClightP PEnv.

Import ClightP.

Set Asymmetric Patterns.

Opaque PTree_Properties.of_list.

Lemma find_field_in id fs v:
  find_field fs id = Some v -> In (id, v) fs.
Proof.
  induction fs; intros; try easy.
  destruct a. cbn in H. destruct peq; inv H; eauto.
  - left. reflexivity.
  - right. eapply IHfs; eauto.
Qed.

Lemma pvars_ok_ext ce0 ce vars:
  composite_env_consistent ce0 ->
  (forall id co, ce0 ! id = Some co -> ce ! id = Some co) ->
  pvars_ok ce0 vars -> pvars_ok ce vars.
Proof.
  intros Hce0 Hce Hvs.
  unfold pvars_ok in *. intros * Hid.
  apply Hvs in Hid. destruct Hid.
  split.
  - clear - init_ok Hce.
    induction init_ok; intros; constructor; eauto.
    inv HT. econstructor; eauto.
  - unfold pvar_align_ok in *.
    clear - align_ok type_ok Hce Hce0.
    unfold pvar_type_ok in type_ok.
    revert type_ok. induction align_ok.
    + intros. inv type_ok. constructor. apply H.
    + intros. inv type_ok. constructor.
      * intros. eapply H0; eauto.
      * cbn in H1 |- *.
        destruct (Z_lt_ge_dec 0 n).
        -- assert (0 <= 0 < n) by lia.
           erewrite H6; eauto. apply Z.divide_mul_l.
           eapply sizeof_type_div4; eauto.
        -- (* rewrite Z.max 0 n to 0 *)
           rewrite !Z.max_l in * by lia.
           (* rewrite x * 0 to 0 *)
            rewrite Z.mul_0_r in *. eauto.
    + intros. inv type_ok.
      econstructor.
      * intros. eapply H0; eauto.
        eapply H8. apply find_field_in; eauto.
      * eauto.
      * intros. eapply H2; eauto.
        instantiate (1 := bf). instantiate (1 := f).
        erewrite <- Ctypes.field_offset_stable; eauto.
        eapply co_consistent_complete.
        unfold composite_env_consistent in Hce0. eauto.
      * eauto.
  - unfold pvar_size_ok in *.
    erewrite <- sizeof_vars_same; eauto.
  - unfold pvar_type_ok in *.
    clear - type_ok Hce.
    induction type_ok; econstructor; eauto.
    inv H. econstructor; eauto.
Qed.

Lemma link_pvars_ok vars1 vars2 ce1 ce2 ce:
  (forall id co, ce1 ! id = Some co -> ce ! id = Some co) ->
  (forall id co, ce2 ! id = Some co -> ce ! id = Some co) ->
  composite_env_consistent ce1 ->
  composite_env_consistent ce2 ->
  pvars_ok ce1 vars1 ->
  pvars_ok ce2 vars2 ->
  pvars_ok ce (vars1 ++ vars2).
Proof.
  intros Hce1 Hce2 Hc1 Hc2 Hvs1 Hvs2.
  eapply pvars_ok_ext in Hvs1; eauto.
  eapply pvars_ok_ext in Hvs2; eauto.
  unfold pvars_ok in *. intros * Hid.
  apply in_app_or in Hid as [Hid | Hid]; eauto.
Qed.

Definition link_program (p1 p2: program): option program :=
  match link (program_of_program p1) (program_of_program p2) with
  | None => None
  | Some p =>
      match lift_option (link p1.(prog_types) p2.(prog_types)) with
      | inright _ => None
      | inleft (exist typs EQ) =>
          match link_build_composite_env
                  p1.(prog_types) p2.(prog_types) typs
                  p1.(prog_comp_env) p2.(prog_comp_env)
                  p1.(prog_comp_env_eq) p2.(prog_comp_env_eq) EQ with
          | exist env (conj P (conj Q1 Q2)) =>
              let privs := p1.(prog_private) ++ p2.(prog_private) in
              match list_norepet_dec peq
                      ((map fst privs ++ map fst p.(AST.prog_defs))) with
              | right _ => None
              | left H =>
                  Some {| prog_private := privs;
                         prog_defs := p.(AST.prog_defs);
                         prog_public := p.(AST.prog_public);
                         prog_main := p.(AST.prog_main);
                         prog_types := typs;
                         prog_comp_env := env;
                         prog_comp_env_eq := P;
                         prog_norepet := H;
                         prog_priv_ok :=
                           link_pvars_ok
                             p1.(prog_private) p2.(prog_private)
                             p1.(prog_comp_env) p2.(prog_comp_env) env Q1 Q2
                             (Ctypes.build_composite_env_consistent _ _ p1.(prog_comp_env_eq))
                             (Ctypes.build_composite_env_consistent _ _ p2.(prog_comp_env_eq))
                             p1.(prog_priv_ok) p2.(prog_priv_ok);
                       |}
              end
          end
      end
  end.

Definition linkorder_program (p1 p2: program) : Prop :=
  linkorder (program_of_program p1) (program_of_program p2)
  /\ (forall id co, p1.(prog_comp_env)!id = Some co -> p2.(prog_comp_env)!id = Some co)
  /\ (forall id v, (PTree_Properties.of_list p1.(prog_private))!id = Some v ->
             (PTree_Properties.of_list p2.(prog_private))!id = Some v).

Program Instance clightp_linker: Linking.Linker program :=
  {
    link := link_program;
    linkorder := linkorder_program;
  }.
Next Obligation.
  split. apply linkorder_refl.
  split; auto.
Qed.
Next Obligation.
  destruct H as (A1 & B1 & C1).
  destruct H0 as (A2 & B2 & C2).
  split. eapply linkorder_trans; eauto.
  split; intros; eauto.
Qed.
Next Obligation.
  revert H. unfold link_program.
  destruct (link (program_of_program x) (program_of_program y)) as [p|] eqn:LP; try discriminate.
  destruct (lift_option (link (prog_types x) (prog_types y))) as [[typs EQ]|EQ]; try discriminate.
  destruct (link_build_composite_env (prog_types x) (prog_types y) typs
              (prog_comp_env x) (prog_comp_env y) (prog_comp_env_eq x)
              (prog_comp_env_eq y) EQ) as (env & P & Q & R).
  destruct list_norepet_dec; try discriminate.
  destruct (link_linkorder _ _ _ LP).
  intros X; inv X.
  split; split; auto. 1-2: split; auto; cbn.
  - intros * Hx. rewrite ptree_of_list_app_none; eauto.
    destruct ((PTree_Properties.of_list (prog_private y)) ! id)
      eqn: Hw; eauto.
    exfalso.
    apply PTree_Properties.in_of_list in Hx.
    apply PTree_Properties.in_of_list in Hw.
    apply list_norepet_append_left in l.
    rewrite map_app in l.
    apply list_norepet_app in l as (A1 & A2 & A3).
    eapply list_disjoint_notin. apply A3. instantiate (1 := id).
    apply in_map_iff. eexists (_, _). split; eauto. easy.
    apply in_map_iff. eexists (_, _). split; eauto. easy.
  - intros * Hx. erewrite ptree_of_list_app; eauto.
Qed.

Transparent Linker_prog.

Lemma globdef_linkorder_erase:
  forall v1 v2 : globdef fundef type,
    linkorder v1 v2 -> linkorder (erase_globdef v1) (erase_globdef v2).
Proof.
  intros * H. inv H.
  (* fundef *)
  - apply linkorder_refl.
  - cbn. constructor. inv H0.
    constructor. apply linkorder_refl.
    cbn. eauto.
Qed.

(* Lemma ptree_of_list_map {A B} (f: A -> B) xs id b: *)
(*   (PTree_Properties.of_list *)
(*      (map (fun '(id, x) => (id, f x)) xs)) ! id = Some b <-> *)
(*     (exists a, (PTree_Properties.of_list xs) ! id = Some a /\ f a = b). *)
(* Proof. *)
(*   induction xs as [| [id' a]]. *)
(*   - cbn. split. intros. inv H. intros (a & Ha & ?). inv Ha. *)
(*   - cbn. destruct (ListDec.In_dec PTree.elt_eq id (map fst xs)). *)
(*     + setoid_rewrite ptree_of_list1; eauto. *)
(*       apply in_map_iff in i as ((x & y) & Hx & Hy). cbn in *. subst. *)
(*       apply in_map_iff. eexists (_, _); split; eauto. reflexivity. *)
(*       apply in_map_iff. eexists (_, _); split; eauto. *)
(*     + setoid_rewrite ptree_of_list2; eauto. *)
(*       * destruct (peq id id'). *)
(*         -- subst. setoid_rewrite PTree.gss. split. *)
(*            ++ intros. inv H. eexists; split; eauto. *)
(*            ++ intros (a' & Ha & Hb). subst. congruence. *)
(*         -- setoid_rewrite PTree.gso; eauto. *)
(*            setoid_rewrite PTree.gempty. *)
(*            split; intros; try congruence. *)
(*            destruct H; easy. *)
(*       * intros c. apply n. *)
(*         apply in_map_iff in c as ((x & y) & Hx & Hy). cbn in *. subst. *)
(*         apply in_map_iff in Hy as ((x & z) & Hx & Hz). inv Hx. *)
(*         apply in_map_iff. eexists (_, _); split; eauto. reflexivity. *)
(* Qed. *)

Import PTree_Properties.

Lemma linkorder_erase:
  forall (p q: program), linkorder p q ->
  linkorder (clightp_erase_program p) (clightp_erase_program q).
Proof.
  intros * ((A1 & A2 & A3) & B & C).
  split. apply A1. split. apply A2.
  intros * H1. destruct p, q.
  unfold prog_defmap in *. cbn in *.
  unfold prog_defmap in *. cbn in *.
  rewrite of_list_elements in *.
  destruct ((of_list prog_defs0) ! id) eqn: Hw;
    destruct ((of_list prog_private0) ! id) eqn: Hu;
    rewrite PTree.gcombine in H1 by reflexivity;
    rewrite Hw in H1; rewrite Hu in H1; cbn in H1; inv H1.
  (* normal variables *)
  - specialize (A3 _ _ Hw) as (x & Hx1 & Hx2 & Hx3).
    exists (erase_globdef x). split. 2: split.
    + rewrite PTree.gcombine. 2: reflexivity.
      rewrite Hx1.
      destruct ((of_list prog_private1) ! id) eqn: Hy.
      * exfalso.
        apply list_norepet_app in prog_norepet1 as (?&?&Ha).
        eapply Ha; eauto. instantiate (1 := id).
        apply in_of_list in Hy. apply in_map_iff.
        eexists (_, _). split; eauto. reflexivity.
        apply in_of_list in Hx1. apply in_map_iff.
        eexists (_, _). split; eauto. reflexivity.
      * reflexivity.
    + apply globdef_linkorder_erase; eauto.
    + intros Hp. rewrite Hx3; eauto.
  (* private variable *)
  - specialize (C _ _ Hu).
    eexists (clightp_erase_privvar p). split. 2: split.
    + rewrite PTree.gcombine. 2: reflexivity.
      rewrite C.
      destruct ((of_list prog_defs1) ! id) eqn: Hy.
      * exfalso.
        apply list_norepet_app in prog_norepet1 as (?&?&Ha).
        eapply Ha; eauto. instantiate (1 := id).
        apply in_of_list in C. apply in_map_iff.
        eexists (_, _). split; eauto. reflexivity.
        apply in_of_list in Hy. apply in_map_iff.
        eexists (_, _). split; eauto. reflexivity.
      * reflexivity.
    + reflexivity.
    + easy.
Qed.

Inductive clightp_link_rel:
  option privvar -> option privvar ->
  option (globdef fundef type) -> option (globdef fundef type) -> Prop :=
| clightp_link_rel0: clightp_link_rel None None None None
| clightp_link_rel1 p: clightp_link_rel (Some p) None None None
| clightp_link_rel2 p: clightp_link_rel None (Some p) None None
| clightp_link_rel3 p: clightp_link_rel None None (Some p) None
| clightp_link_rel4 p: clightp_link_rel None None None (Some p)
| clightp_link_rel5 p1 p2: clightp_link_rel None None (Some p1) (Some p2).

Hint Resolve in_of_list.

Lemma clightp_link_rel_intro (p1 p2: program):
  (forall id g1 g2,
      (of_list (prog_defs p1)) ! id = Some g1 ->
      (of_list (prog_defs p2)) ! id = Some g2 ->
      (exists g, link g1 g2 = Some g)) ->
  list_norepet
    (map fst (prog_private p1 ++ prog_private p2) ++
       map fst
       (PTree.elements
          (PTree.combine link_prog_merge (prog_defmap p1) (prog_defmap p2)))) ->
  forall id : positive,
    clightp_link_rel (of_list (prog_private p1)) ! id
      (of_list (prog_private p2)) ! id
      (of_list (prog_defs p1)) ! id
      (of_list (prog_defs p2)) ! id.
Proof.
  intros Hg H id.
  assert
    (HX: forall a b c d,
      (of_list (prog_private p1)) ! id = Some a \/
      (of_list (prog_private p2)) ! id = Some b ->
      (of_list (prog_defs p1)) ! id = Some c \/
      (of_list (prog_defs p2)) ! id = Some d -> False).
  {
    intros * Hp Hd.
    assert (In id (map fst (PTree.elements (PTree.combine link_prog_merge (prog_defmap p1) (prog_defmap p2))))).
    {
      Ltac link_rel_solve1 H1 H2 :=
        split; eauto;
        apply PTree.elements_correct;
        rewrite PTree.gcombine by reflexivity;
        setoid_rewrite H1;
        setoid_rewrite H2; eauto.
      destruct ((of_list (prog_defs p1)) ! id) eqn: Hd1;
        destruct ((of_list (prog_defs p2)) ! id) eqn: Hd2.
      - specialize (Hg _ _ _ Hd1 Hd2) as (gx & Hg).
        apply in_map_iff. eexists (id, gx).
        link_rel_solve1 Hd1 Hd2.
      - destruct Hd; try congruence. inv H0.
        apply in_map_iff. eexists (id, c).
        link_rel_solve1 Hd1 Hd2.
      - destruct Hd; try congruence. inv H0.
        apply in_map_iff. eexists (id, d).
        link_rel_solve1 Hd1 Hd2.
      - destruct Hd; congruence.
    }
    assert (In id (map fst (prog_private p1 ++ prog_private p2))).
    {
      rewrite map_app. apply in_or_app.
      destruct Hp; [ left | right ]; apply in_map_iff.
      - eexists (id, a). split; eauto.
      - eexists (id, b). split; eauto.
    }
    apply list_norepet_app in H as (A & B & C).
    eapply C; eauto.
  }
  Ltac lr_solve H :=
    exfalso; eapply H; solve [ left; eauto | right; eauto ].
  destruct ((of_list (prog_private p1)) ! id) eqn: Hp1;
    destruct ((of_list (prog_private p2)) ! id) eqn: Hp2.
  - exfalso. apply list_norepet_app in H as (A & B & C).
    rewrite map_app in A.
    apply list_norepet_app in A as (A1 & A2 & A3).
    eapply A3; eauto; apply in_map_iff.
    + eexists (id, p). split; eauto.
    + eexists (id, p0). split; eauto.
  - destruct ((of_list (prog_defs p1)) ! id) eqn: Hd1;
      destruct ((of_list (prog_defs p2)) ! id) eqn: Hd2;
      try lr_solve HX.
    constructor.
  - destruct ((of_list (prog_defs p1)) ! id) eqn: Hd1;
      destruct ((of_list (prog_defs p2)) ! id) eqn: Hd2;
      try lr_solve HX.
    constructor.
  - destruct ((of_list (prog_defs p1)) ! id) eqn: Hd1;
      destruct ((of_list (prog_defs p2)) ! id) eqn: Hd2;
      constructor.
Unshelve. all: eauto.
Qed.

Lemma link_clightp_erase (p1 p2 p: program):
  link p1 p2 = Some p ->
  link (clightp_erase_program p1) (clightp_erase_program p2) =
    Some (clightp_erase_program p).
Proof.
  intros Hp. unfold link in *. cbn in *.
  unfold link_program in Hp.
  destruct link eqn: H1; try congruence.
  destruct lift_option as [[x H2]|]; try congruence.
  destruct link_build_composite_env as (env & H3 & H4 & H5).
  destruct list_norepet_dec; try congruence.
  apply link_prog_inv in H1 as (Hmain & Hdef & Hp0).
  rewrite link_prog_succeeds.
  - inv Hp. f_equal.
    unfold clightp_erase_program. cbn in *. f_equal.
    unfold prog_defmap. cbn.
    apply PTree.elements_extensional. intros id.
    rewrite !PTree.gcombine by reflexivity.
    rewrite !of_list_elements.
    rewrite !PTree.gcombine by reflexivity.
    apply clightp_link_rel_intro with (id:=id) in l.
    2: { intros * Hx Hy. eapply Hdef; eauto. }
    Ltac rewrite_none H :=
      rewrite ptree_of_list_app_none; eauto; rewrite <- H.
    inv l; cbn; try (rewrite_none H0; reflexivity).
    + erewrite ptree_of_list_app; eauto. reflexivity.
    + rewrite_none H0. cbn.
      exploit Hdef. 1-2: symmetry; eauto.
      intros (?&?&(gd & Hgd)). rewrite Hgd.
      apply link_erase_globdef; eauto.
  - apply Hmain.
  - unfold clightp_erase_program, prog_defmap. cbn.
    setoid_rewrite of_list_elements.
    intros * HA HB.
    subst p0. cbn in l. clear Hp.
    apply clightp_link_rel_intro with (id:=id) in l.
    2: { intros * Hx Hy. eapply Hdef; eauto. }
    rewrite PTree.gcombine in HA, HB by reflexivity.
    inv l; cbn; rewrite <- H0 in HA; rewrite <- H in HB;
      rewrite <- H6 in HA; rewrite <- H7 in HB;
      cbn in *; try congruence.
    exploit Hdef. 1-2: symmetry; eauto.
    intros (A & B & (gd & Hgd)). repeat split; eauto.
    inv HA; inv HB.
    apply link_erase_globdef in Hgd; eauto.
    rewrite Hgd. discriminate.
Qed.
