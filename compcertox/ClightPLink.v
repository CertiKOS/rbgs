From compcert Require Import
     Integers Coqlib Maps
     Memory AST Values
     Globalenvs Linking Ctypes.
From compcertox Require Import
  ClightP PEnv.

Import ClightP.

Set Asymmetric Patterns.

Definition link_privvar (v1 v2: list (ident * privvar))
  (vs: list (ident * globdef fundef type))
  : True + { v | v = v1 ++ v2
              /\ list_disjoint (map fst v1) (map fst v2)
              /\ list_disjoint (map fst v) (map fst vs) }.
Proof.
  destruct (list_disjoint_dec ident_eq (map fst v1) (map fst v2)).
  destruct (list_disjoint_dec ident_eq (map fst (v1 ++ v2)) (map fst vs)).
  - right. eexists (v1 ++ v2). split; eauto.
  - left. easy.
  - left. easy.
Defined.

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
          | exist env (conj P Q) =>
              match link_privvar p1.(prog_private) p2.(prog_private) p.(AST.prog_defs) with
              | inl _ => None
              | inr (exist privs (conj _ (conj p1 p2))) =>
                  Some {| prog_private := privs;
                         prog_defs := p.(AST.prog_defs);
                         prog_public := p.(AST.prog_public);
                         prog_main := p.(AST.prog_main);
                         prog_types := typs;
                         prog_comp_env := env;
                         prog_comp_env_eq := P;
                         prog_disjoint := p2;
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
  destruct (link_privvar (prog_private x) (prog_private y)) as [l|] eqn:LV; try discriminate.
  destruct (link_linkorder _ _ _ LP).
  intros X; inv X.
  unfold link_privvar in LV.
  destruct (list_disjoint_dec ident_eq (map fst (prog_private x)) (map fst (prog_private y))); try discriminate.
  destruct (list_disjoint_dec ident_eq (map fst (prog_private x ++ prog_private y)) (map fst (AST.prog_defs p))); try discriminate.
  inv LV. inv H2.
  split; split; auto. 1-2: split; auto.
  - cbn -[PTree_Properties.of_list].
    intros * Hx. rewrite ptree_of_list_app_none; eauto.
    destruct (lift_option ((PTree_Properties.of_list (prog_private y)) ! id)) as [[w Hw]|]; eauto.
    exfalso.
    apply PTree_Properties.in_of_list in Hx.
    apply PTree_Properties.in_of_list in Hw.
    eapply list_disjoint_notin. apply l. instantiate (1 := id).
    apply in_map_iff. eexists (_, _). split; eauto. easy.
    apply in_map_iff. eexists (_, _). split; eauto. easy.
  - cbn -[PTree_Properties.of_list].
    intros * Hx. erewrite ptree_of_list_app; eauto.
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

Lemma ptree_of_list_map {A B} (f: A -> B) xs id b:
  (PTree_Properties.of_list
     (map (fun '(id, x) => (id, f x)) xs)) ! id = Some b <->
    (exists a, (PTree_Properties.of_list xs) ! id = Some a /\ f a = b).
Proof.
  induction xs as [| [id' a]].
  - cbn. split. intros. inv H. intros (a & Ha & ?). inv Ha.
  - cbn. destruct (ListDec.In_dec PTree.elt_eq id (map fst xs)).
    + setoid_rewrite ptree_of_list1; eauto.
      apply in_map_iff in i as ((x & y) & Hx & Hy). cbn in *. subst.
      apply in_map_iff. eexists (_, _); split; eauto. reflexivity.
      apply in_map_iff. eexists (_, _); split; eauto.
    + setoid_rewrite ptree_of_list2; eauto.
      * destruct (peq id id').
        -- subst. setoid_rewrite PTree.gss. split.
           ++ intros. inv H. eexists; split; eauto.
           ++ intros (a' & Ha & Hb). subst. congruence.
        -- setoid_rewrite PTree.gso; eauto.
           setoid_rewrite PTree.gempty.
           split; intros; try congruence.
           destruct H; easy.
      * intros c. apply n.
        apply in_map_iff in c as ((x & y) & Hx & Hy). cbn in *. subst.
        apply in_map_iff in Hy as ((x & z) & Hx & Hz). inv Hx.
        apply in_map_iff. eexists (_, _); split; eauto. reflexivity.
Qed.

Lemma linkorder_erase:
  forall (p q: program), linkorder p q ->
  linkorder (clightp_erase_program p) (clightp_erase_program q).
Proof.
  intros * ((A1 & A2 & A3) & B & C).
  split. apply A1. split. apply A2.
  intros *  H1. destruct p, q.
  unfold prog_defmap in *.
  cbn -[PTree_Properties.of_list] in *.
  destruct (lift_option ((PTree_Properties.of_list (map (fun '(id, g) => (id, erase_globdef g)) prog_defs0)) ! id)) as [[w Hw]|].
  (* normal variables *)
  - erewrite ptree_of_list_app in H1; eauto. inv H1.
    apply ptree_of_list_map in Hw as (v & Hv1 & Hv2). subst.
    specialize (A3 _ _ Hv1).
    destruct A3 as (u & Hu1 & Hu2 & Hu3).
    exists (erase_globdef u). split. 2: split.
    + erewrite ptree_of_list_app; eauto.
      eapply ptree_of_list_map. eexists; split; eauto.
    + apply globdef_linkorder_erase; eauto.
    + intros Hp. rewrite Hu3; eauto.
  (* private variable *)
  - erewrite ptree_of_list_app_none in H1; eauto.
    apply ptree_of_list_map in H1 as (v & Hv1 & Hv2). subst.
    specialize (C _ _ Hv1).
    eexists (clightp_erase_privvar v). split. 2: split.
    + erewrite ptree_of_list_app_none.
      * apply ptree_of_list_map. eexists; split; eauto.
      * apply PTree_Properties.in_of_list in C.
        assert (D: In id (map fst prog_private1)).
        apply in_map_iff. eexists (_, _); split; eauto. reflexivity.
        destruct (lift_option (PTree_Properties.of_list (map (fun '(id0, g) => (id0, erase_globdef g)) prog_defs1)) ! id) as [[q Hq]|]; eauto.
        exfalso.
        apply PTree_Properties.in_of_list in Hq.
        apply in_map_iff in Hq as ((id' & x) & Hr1 & Hr2). inv Hr1.
        eapply prog_disjoint1.
        apply in_map_iff. eexists (_, _); split; eauto.
        apply in_map_iff. eexists (_, _); split; eauto.
        reflexivity.
    + apply linkorder_refl.
    + intros. reflexivity.
Qed.
