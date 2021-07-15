Require Import AST.
Require Import Coqlib.
Require Import Integers.
Require Import Globalenvs.
Require Import Memory.
Require Import LanguageInterface.
Require Import Smallstep.
Require Import Linking.
Require Import SmallstepLinking.
Require Import Values.
Require Import Maps.

Require Import Clight.
Require Import Ctypes.

Inductive linked {A} `{Linker A} : option A -> option A -> option A -> Prop :=
| linked_n : linked None None None
| linked_l a : linked (Some a) None (Some a)
| linked_r a : linked None (Some a) (Some a)
| linked_lr a b c : link a b = Some c -> linked (Some a) (Some b) (Some c).

Lemma find_def_link se (p1 p2 p: Clight.program) b:
  link p1 p2 = Some p ->
  linked (Genv.find_def (Genv.globalenv se p1) b)
         (Genv.find_def (Genv.globalenv se p2) b)
         (Genv.find_def (Genv.globalenv se p) b).
Proof.
  intros Hp.
  assert (Hp': link (program_of_program p1) (program_of_program p2) =
               Some (program_of_program p)).
  {
    Local Transparent Linker_program.
    cbn in *. unfold link_program in *.
    destruct link; try congruence.
    destruct lift_option. destruct s.
    destruct link_build_composite_env. destruct a.
    f_equal. unfold program_of_program. inv Hp. cbn.
    destruct p0. reflexivity. congruence.
  } clear Hp.
  apply (@link_prog_inv _ _ _ _ p1 p2 p) in Hp' as (_ & Hdefs & Hp).
  rewrite !Genv.find_def_spec.
  destruct Genv.invert_symbol; try constructor.
  rewrite Hp. (* subst p.  *)
  rewrite prog_defmap_elements, PTree.gcombine; auto.
  destruct (prog_defmap p1)!i eqn:H1, (prog_defmap p2)!i eqn:H2; try constructor.
  edestruct Hdefs as (_ & _ & gd & Hgd); eauto.
  cbn. rewrite Hgd. constructor; auto.
Qed.

Lemma find_def_linkorder se (p p': Clight.program) b gd:
  linkorder p p' ->
  Genv.find_def (Genv.globalenv se p) b = Some gd ->
  exists gd',
    Genv.find_def (Genv.globalenv se p') b = Some gd' /\
    linkorder gd gd'.
Proof.
  rewrite !Genv.find_def_spec. destruct Genv.invert_symbol; try discriminate.
  intros [(_ & _ & Hdefs) _] Hgd. edestruct Hdefs as (gd' & Hgd' & Hgg' & _); eauto.
Qed.

Lemma find_funct_ptr_linkorder se (p p': Clight.program) b fd:
  Genv.find_funct_ptr (Genv.globalenv se p) b = Some fd ->
  linkorder p p' ->
  exists fd',
    Genv.find_funct_ptr (Genv.globalenv se p') b = Some fd' /\
    linkorder fd fd'.
Proof.
  intros. unfold Genv.find_funct_ptr in *; cbn in *.
  destruct (Genv.find_def (Genv.globalenv se p)) eqn:Hf; try discriminate.
  edestruct find_def_linkorder as (fd' & Hfd & Hlo); eauto. rewrite Hfd.
  destruct g; try discriminate. inv Hlo. inv H. eauto.
Qed.

Lemma find_internal_ptr_linkorder se (p p': Clight.program) b f:
  Genv.find_funct_ptr (Genv.globalenv se p) b = Some (Internal f) ->
  linkorder p p' ->
  Genv.find_funct_ptr (Genv.globalenv se p') b = Some (Internal f).
Proof.
  intros. edestruct find_funct_ptr_linkorder as (? & ? & ?); eauto.
  inv H2. eauto.
Qed.

Lemma find_funct_linkorder se (p p': Clight.program) vf fd:
  Genv.find_funct (Genv.globalenv se p) vf = Some fd ->
  linkorder p p' ->
  exists fd',
    Genv.find_funct (Genv.globalenv se p') vf = Some fd' /\
    linkorder fd fd'.
Proof.
  intros. unfold Genv.find_funct in *.
  destruct vf; try discriminate.
  destruct Ptrofs.eq_dec; try discriminate.
  eapply find_funct_ptr_linkorder; eauto.
Qed.

Lemma find_internal_linkorder se (p p': Clight.program) vf f:
  Genv.find_funct (Genv.globalenv se p) vf = Some (Internal f) ->
  linkorder p p' ->
  Genv.find_funct (Genv.globalenv se p') vf = Some (Internal f).
Proof.
  intros. unfold Genv.find_funct in *.
  destruct vf; try discriminate.
  destruct Ptrofs.eq_dec; try discriminate.
  eapply find_internal_ptr_linkorder; eauto.
Qed.

Section linking.
  Context (p1 p2 p: Clight.program) (Hp: link p1 p2 = Some p).
  Let p_ i := match i with true => p1 | false => p2 end.
  Let L i := semantics1 (p_ i).

  Lemma p_linkorder i:
    linkorder (p_ i) p.
  Proof.
    apply link_linkorder in Hp as [? ?].
    destruct i; cbn; auto.
  Qed.
  Hint Resolve p_linkorder.

  Section se.
    Context (se: Genv.symtbl).

    Inductive match_cont: list (frame L) -> cont -> cont -> Prop :=
    | match_Kstop:
        match_cont nil Kstop Kstop
    | match_Kseq ks s k k':
        match_cont ks k k' ->
        match_cont ks (Kseq s k) (Kseq s k')
    | match_Kloop1 ks s1 s2 k k':
        match_cont ks k k' ->
        match_cont ks (Kloop1 s1 s2 k) (Kloop1 s1 s2 k')
    | match_Kloop2 ks s1 s2 k k':
        match_cont ks k k' ->
        match_cont ks (Kloop2 s1 s2 k) (Kloop2 s1 s2 k')
    | match_Kswitch ks k k':
        match_cont ks k k' ->
        match_cont ks (Kswitch k) (Kswitch k')
    | match_Kcall ks optid f e le k k':
        match_cont ks k k' ->
        match_cont ks (Kcall optid f e le k) (Kcall optid f e le k')
    | match_frame i vf args k k' m ks:
        match_cont ks k k' ->
        match_cont (st L i (Callstate vf args k m) :: ks) Kstop k'.

    Inductive match_states: list (frame L) -> state -> Prop :=
    | State_match i f s k k' e le m ks:
        match_cont ks k k' ->
        match_states (st L i (State f s k e le m) :: ks) (State f s k' e le m)
    | Callstate_match i vf args k k' m ks:
        match_cont ks k k' ->
        match_states (st L i (Callstate vf args k m) :: ks) (Callstate vf args k' m)
    | Returnstate_match i res k k' m ks:
        match_cont ks k k' ->
        match_states (st L i (Returnstate res k m) :: ks) (Returnstate res k' m).

    (* types are well formed
       in particular, the type of a pointer has to be either a primitive or a type in scope *)
    Variable tyck: composite_env -> expr -> Prop.
    Hypothesis tyck_sizeof:
      forall ce ce' e (extends: forall id co, ce!id = Some co -> ce'!id = Some co),
        tyck ce e -> sizeof ce (typeof e) = sizeof ce' (typeof e).
    Hypothesis tyck_sizeof_pointer:
      forall ce ce' e ty attr (extends: forall id co, ce!id = Some co -> ce'!id = Some co),
        tyck ce e -> typeof e = Tpointer ty attr ->
        sizeof ce ty = sizeof ce' ty.

    Ltac DestructCases :=
      match goal with
      | [H: match match ?x with _ => _ end with _ => _ end = Some _ |- _ ] => destruct x eqn:?; DestructCases
      | [H: match ?x with _ => _ end = Some _ |- _ ] => destruct x eqn:?; DestructCases
      | [H: Some _ = Some _ |- _ ] => inv H; DestructCases
      | [H: None = Some _ |- _ ] => discriminate
      | _ => idtac
      end.

    Ltac DestructMatch :=
      match goal with
      | [ H: match match ?x with _ => _ end with _ => _ end = _ |- _] => destruct x eqn:?; DestructMatch
      | [ |- match match ?x with _ => _ end with _ => _ end ] => destruct x; DestructMatch
      | [ |- match ?x with _ => _ end ] => destruct x; DestructMatch
      | _ => idtac
      end.

    Lemma l1 i t1 t2 ty si:
      Cop.classify_add (typeof t1) (typeof t2) = Cop.add_case_pi ty si ->
      sizeof (prog_comp_env p) ty = sizeof (prog_comp_env (p_ i)) ty.
    Proof.
      intros H. unfold Cop.classify_add in H. unfold typeconv in H.
      (* DestructMatch; cbn in *; try inv H; DestructMatch; cbn in *; try inv H1; try easy. *)
      (* - admit. *)
      (* - admit. *)
      destruct (typeof t1) eqn: Ht1; destruct (typeof t2) eqn: Ht2;
        cbn in *; try destruct i1; try destruct i0; inv H; auto.

    Admitted.

    Lemma eval_expr_lvalue_match i env le m:
      (forall e v, eval_expr (globalenv se (p_ i)) env le m e v ->
              eval_expr (globalenv se p) env le m e v)
      /\
      (forall e b ofs, eval_lvalue (globalenv se (p_ i)) env le m e b ofs ->
                  eval_lvalue (globalenv se p) env le m e b ofs).
    Proof.
      apply eval_expr_lvalue_ind; intros; try now econstructor.
      - econstructor; eauto.
      - econstructor; eauto.
        destruct op; auto.
        + cbn in *.
          unfold Cop.sem_add in *.
          destruct Cop.classify_add eqn: Hadd; auto.
          * unfold Cop.sem_add_ptr_int in *.
            destruct v1; destruct v2; try congruence.
            -- destruct Archi.ptr64; try congruence.
               inv H3. do 5 f_equal.
               eapply l1. eauto.
            -- admit.
            -- admit.
          * admit.
          * admit.
          * admit.
        + admit.
      - econstructor; eauto.
      - admit.
      - admit.
      - econstructor; eauto.
      - econstructor; eauto.
        admit. admit.
      - admit.
    Admitted.

    Lemma assign_loc_match i e m loc ofs v m':
      assign_loc (globalenv se (p_ i)) (typeof e) m loc ofs v m' ->
      assign_loc (globalenv se p) (typeof e) m loc ofs v m'.
    Proof.
      inversion 1. subst.
      - eapply assign_loc_value; eauto.
      - eapply assign_loc_copy; subst; eauto.
        admit.
    Admitted.

    Lemma eval_exprlist_match i e le m es tys vs:
      eval_exprlist (globalenv se (p_ i)) e le m es tys vs ->
      eval_exprlist (globalenv se p) e le m es tys vs.
    Proof.
      induction 1; econstructor; eauto.
      eapply eval_expr_lvalue_match. eauto.
    Qed.

    Lemma step_match i s k s' s1 t:
      match_states (st L i s :: k) s' ->
      step1 (globalenv se (p_ i)) s t s1 ->
      exists (s1' : state),
        step1 (globalenv se p) s' t s1' /\
        match_states (st L i s1 :: k) s1'.
    Proof.
      intros Hs Hstep. inv Hs.
      - inv Hstep.
        + eexists. split.
          econstructor; eauto.
          eapply eval_expr_lvalue_match. eauto.
          eapply eval_expr_lvalue_match. eauto.
          eapply assign_loc_match; eauto.
          constructor; auto.
        + eexists. split.
          econstructor; eauto.
          eapply eval_expr_lvalue_match; eauto.
          constructor; auto.
        + eexists. split.
          eapply find_funct_linkorder in H11 as (fd' & Hfd & Hfdlk); eauto.
          econstructor; eauto.
          eapply eval_expr_lvalue_match. eauto.
          eapply eval_exprlist_match. eauto.
          (* The external call in one component that matches an internal call in
             the other component has to have the same signature with it *)
          (* But we don't know this information from link order... *)
          (* It's an interesting scenario if the types don't match. Component A
             has an external call f with signature s and component B has an
             internalfunction f with signature t. Both are fine when they are
             separate but if we try to link them together, it has undefined
             behavior when A calls f on both semantics linking and syntactic
             linking. But there is still some subtle difference: on semantics
             linking, the call state prepares arguments according to signature s
             and fails once transferred to the other component, whereas the
             linked one fails on preparing the callstate, for example. *)
          (* By preparing the arguments, I meant casting the arguments to the
             desired types *)
          unfold linkorder in Hfdlk.
    Admitted.

  End se.
  Definition measure (S : Genv.symtbl * list (frame L)): nat :=
    match S with
    | (_, nil) => 0
    | (se, st i (State _ _ _ _ _ _) :: _) => 0
    | (se, st i (Callstate vf _ _ _) :: k) =>
      length k +
      match Genv.find_funct (globalenv se (p_ i)) vf with
      | Some (External _ _ _ _) => 2
      | _ => 0
      end
    | (se, st i (Returnstate _ _ _) :: k) => length k
    end.

  Lemma clight_linking:
    forward_simulation cc_id cc_id (semantics L (erase_program p)) (semantics1 p).
  Proof.
    constructor.
    eapply Forward_simulation with
        (fsim_order := ltof _ measure)
        (fsim_match_states :=
           fun se1 se2 w idx s1 s2 =>
             idx = (se1, s1) /\ match_states s1 s2); auto.

    intros se _ [ ] [ ] Hse. econstructor.
    - (* valid_query *)
      intros q _ [ ]. cbn. unfold valid_query. cbn.
      unfold Genv.is_internal, Genv.find_funct, Genv.find_funct_ptr.
      destruct cq_vf; auto. destruct Ptrofs.eq_dec; auto.
      eapply (find_def_link se p1 p2 p b) in Hp.
      unfold Clight.fundef.
      destruct Hp; rewrite ?orb_false_l, ?orb_false_r; auto.
      Local Transparent Linker_def Linker_fundef.
      destruct c as [[|]|], a as [[|]|], b0 as [[|]|]; inv H; try discriminate;
        cbn in *; auto.
      + destruct external_function_eq.
        destruct (_ && _); discriminate.
        destruct (_ && _); discriminate.
      + destruct link; discriminate.
      + destruct e1; discriminate.
      + destruct e1; discriminate.
      + destruct e0; discriminate.
      + destruct e0; discriminate.
    - (* initial states *)
      intros q _ s1 [ ] Hs1. destruct Hs1 as [i s Hq Hs]. cbn in *.
      eexists _, s. inv Hs. intuition eauto.
      + cbn in *. econstructor; eauto.
        eapply find_internal_linkorder; eauto.
      + constructor. constructor.
    - (* final states *)
      intros _ s1 s2 r1 [_ Hs] Hr1. inv Hr1. inv Hs; inv H.
      eexists. split. cbn. inv H4. econstructor. constructor.
    - (* external states *)
      intros _ s1 s2 qx [_ Hs] Hqx. cbn in *.
      exists tt, qx. inv Hs; inv Hqx; inv H4.
      repeat apply conj; auto.
      + subst f. econstructor.
        edestruct find_funct_linkorder as (? & ? & ?); eauto.
        eapply H7. inv H1; eauto.
        pose proof (H5 false). pose proof (H5 true).
        clear - H0 H1 H2 Hp. cbn in *.
        unfold Genv.is_internal, Genv.find_funct, Genv.find_funct_ptr in *.
        destruct vf; try discriminate.
        destruct Ptrofs.eq_dec; try discriminate.
        unfold Clight.fundef in *.
        destruct (find_def_link se p1 p2 p b Hp); try discriminate.
        * destruct a; try discriminate. inv H0. discriminate.
        * destruct a; try discriminate. inv H0. discriminate.
        * destruct c; try discriminate. inv H0.
          destruct a as [[|]|], b0 as [[|]|]; cbn in *; try discriminate.
          destruct external_function_eq; try discriminate.
          destruct (_ && _); try discriminate.
          destruct link; try discriminate.
      + intros r _ s' <- Hs'. inv Hs'. cbn in *. inv H6.
        eexists _, (Returnstate vres _ m'). repeat apply conj; auto.
        * constructor.
        * constructor. auto.
          (* - (* simulation *) *)
          (*   intros s1 t s1' Hstep1 idx s2 [Hidx Hs]. subst. cbn in *. *)
          (*   inv Hstep1; cbn in *. *)
          (*   + (* internal step *) *)
          (*     edestruct step_match as (? & ? & ?); eauto. *)
          (*     eexists _, _. intuition eauto. *)
          (*   + (* push *) *)
          (*     inv H. inv H1. inv Hs. cbn in *. *)
          (*     eexists _, _. repeat apply conj; eauto. *)
          (*     right. split. *)
          (*     * eapply star_refl. *)
          (*     * red. cbn. rewrite H2. rewrite H6. subst f. red. xomega. *)
          (*     * constructor. constructor. auto. *)
          (*   + (* pop *) *)
          (*     inv H. inv H0. inv Hs. *)
          (*     eexists _, _. repeat apply conj; eauto. *)
          (*     right. split. *)
          (*     * eapply star_refl. *)
          (*     * red. cbn. xomega. *)
          (*     * constructor. inv H5. auto. *)
          (* - apply well_founded_ltof. *)

  Admitted.
End linking.
