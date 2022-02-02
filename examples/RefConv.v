From Coq Require Import
     Relations RelationClasses
     FunctionalExtensionality
     PropExtensionality.
Require Import IntSpec.
From structures Require Import
     Effects Lattice.
Require Import LanguageInterface.
From lattices Require Import
     Upset Downset FCD.
Import ISpec.

Local Obligation Tactic := idtac.

(** * Adjunctions in Interaction Specification *)

(** An adjunction A ⇆ B is a pair or morphisms which can "cancel" each other *)
(* TODO: a more general formalization of adjunctions? *)
(* A is the high level specification; B is the low level implementation *)
Class poset_adjunction (A B: esig) :=
  {
    left_arrow : A ~> B;
    right_arrow : B ~> A;
    epsilon : left_arrow @ right_arrow [= identity;
    eta : identity [= right_arrow @ left_arrow;
  }.
Arguments left_arrow {_ _}.
Arguments right_arrow {_ _}.
Arguments epsilon {_ _}.
Arguments eta {_ _}.

Infix "<~>" := poset_adjunction (at level 50).

(** ** Composition and identity of adjunctions *)

Program Definition adj_compose {A B C} (phi: A <~> B) (psi: B <~> C) :=
  {|
    left_arrow := left_arrow psi @ left_arrow phi;
    right_arrow := right_arrow phi @ right_arrow psi;
  |}.
Next Obligation.
  intros *. etransitivity.
  instantiate (1 := (left_arrow psi @ (left_arrow phi @ right_arrow phi) @ right_arrow psi)).
  rewrite !compose_assoc. reflexivity.
  rewrite epsilon. rewrite compose_unit_l. apply epsilon.
Qed.
Next Obligation.
  intros *. etransitivity.
  instantiate (1 := right_arrow phi @ (right_arrow psi @ left_arrow psi) @ left_arrow phi).
  rewrite <- eta. rewrite compose_unit_l. apply eta.
  rewrite !compose_assoc. reflexivity.
Qed.

Program Definition adj_id {A: esig} :=
  {|
    left_arrow := @identity A;
    right_arrow := @identity A;
  |}.
Next Obligation.
  intros *. rewrite compose_unit_l. reflexivity.
Qed.
Next Obligation.
  intros *. rewrite compose_unit_l. reflexivity.
Qed.

(** * Refinement Conventions *)

(** The motivation behind the category of refinement convention is to solve the
  problem of data marshalling between language interfaces and effect signatures
  with minimal elementary structures. Previously, the connection between the
  high level representation and the low level one is defined in term of an
  abstraction relation. In the FCD-enriched semantics model, the abstraction
  relations are generalized to adjunctions. Therefore, we'd like to have the
  adjunction [E#S ⇆ liC@mem] that translates one representation to another.

  However, with the goal of minimal elementary structures in mind, we'd like the
  adjunction to be derived from some relational structure between E and liC with
  some another relational structure between S and mem because the arguments
  within an event/query is orthogonal to the state/memory. For the latter, we
  simply use the ordinary binary relation [S -> mem -> Prop]. For the formal
  structure, we have several choices: an adjunction [E ⇆ liC], a calling
  convention [E ⇔ liC], or an ordinary binary relation [E -> liC -> Prop]. None of
  them are satisfactory (but theoretically all of them should work probably).
  Therefore, we introduce a new structure to solve the issue.  *)

(** ** Refinement Convention as Generalized Simulation Convention  *)

(* Note: don't use [rel ar1 ar2], otherwise there will be issues with the universe *)
Definition rc_rel (E F: esig) := forall ar1, E ar1 -> forall ar2, F ar2 -> (ar1 -> ar2 -> Prop) -> Prop.
(* Note: the coercion would not work if we fold the definition of [rc_rel] *)
Record refconv (E F: esig) :=
  mk_refconv {
      refconv_rel :> forall ar1, E ar1 -> forall ar2, F ar2 -> (ar1 -> ar2 -> Prop) -> Prop;
      refconv_clo ar1 m1 ar2 m2:
        Proper (subrel ++> impl) (refconv_rel ar1 m1 ar2 m2);
    }.

Instance refconv_eqrel {E F} (rc: rc_rel E F) ar1 m1 ar2 m2:
  Proper (eqrel ==> iff) (rc ar1 m1 ar2 m2).
Proof.
  intros x y Heq. replace y with x. reflexivity.
  extensionality a. extensionality b.
  apply propositional_extensionality.
  split; apply Heq.
Qed.

Infix "<=>" := refconv (at level 50) : type_scope.

(** *** Order on Refinement Conventions  *)

Definition rc_ref {E F} (rc1 rc2: E <=> F) :=
  forall ar1 m1 ar2 m2 R1,
    rc1 ar1 m1 ar2 m2 R1 ->
    exists R2, rc2 ar1 m1 ar2 m2 R2 /\ subrel R2 R1.

Instance rc_ref_antisym (E F: esig):
  Antisymmetric (@refconv E F) eq rc_ref.
Proof.
  intros [ rc1 Hclo1 ] [ rc2 Hclo2 ] H1 H2.
  red in H1, H2. cbn in *.
  assert (rc1 = rc2).
  {
    extensionality ar1. extensionality m1.
    extensionality ar2. extensionality m2. extensionality R.
    apply propositional_extensionality. split; intros.
    - edestruct H1 as (R' & Hx & Hy). eauto.
      eapply Hclo2; eauto.
    - edestruct H2 as (R' & Hx & Hy). eauto.
      eapply Hclo1; eauto.
  }
  subst. f_equal. apply proof_irrelevance.
Qed.

(** *** Calculating the upward closure *)
Program Definition normalize_rc {E F: esig} (rc: rc_rel E F) : E <=> F :=
  {|
    refconv_rel ar1 m1 ar2 m2 R := exists R', rc _ m1 _ m2 R' /\ subrel R' R;
  |}.
Next Obligation.
  intros * x y Hxy H.
  destruct H as [ R' [ ? ? ] ].
  exists R'; split; auto.
  etransitivity; eauto.
Qed.

Definition rc_normalize_idemp {E F} (rc: rc_rel E F):
  normalize_rc (normalize_rc rc) = normalize_rc rc.
Proof.
  apply antisymmetry; intros ar1 m1 ar2 m2 R1 Hrc1;
    exists R1; split; try easy.
  - destruct Hrc1 as (Rx & Hrc2 & Hrx).
    destruct Hrc2 as (Ry & Hrc3 & Hry).
    exists Ry; split; try easy.
    etransitivity; eauto.
  - destruct Hrc1 as (Rx & Hrc2 & Hrx).
    exists Rx. split; try easy. exists Rx. split; easy.
Qed.

Coercion normalize_rc: rc_rel >-> refconv.

Tactic Notation "rc_elim" tactic(tac) hyp(H) :=
  match type of H with
  | refconv_rel _ _ (normalize_rc _) _ _ _ _ _ =>
      let R := fresh "R" in
      let Hrel := fresh "Hrel" in
      let Hsub := fresh "Hsub" in
      destruct H as (R & Hrel & Hsub); tac Hrel
  end.
Ltac destr H := destruct H.
Tactic Notation "rc_destruct" hyp(H) := rc_elim (destr) H.
Ltac destr_pat p H := destruct H as p.
Tactic Notation "rc_destruct" hyp(H) "as" simple_intropattern(p) := rc_elim (destr_pat p) H.
Ltac inver H := inversion H.
Tactic Notation "rc_inversion" hyp(H) := rc_elim (inver) H.
Ltac inver_pat p H := inversion H as p.
Tactic Notation "rc_inversion" hyp(H) "as" simple_intropattern(p) := rc_elim (inver_pat p) H.

Tactic Notation "rc_intro" tactic(tac) :=
  match goal with
  | [ |- refconv_rel _ _ (normalize_rc _) _ _ _ _ ?R ] =>
      exists R; split; [ tac | reflexivity ]
  end.
Ltac rc_econstructor := rc_intro econstructor.
Ltac rc_eapply H := rc_intro (eapply H).

(** *** Categorical Structures of Refinment Conventions *)
Inductive rc_id {E} : rc_rel E E :=
| rc_id_intro ar m: rc_id ar m ar m eq.

Inductive rc_compose {E F G} (rc1: E <=> F) (rc2: F <=> G) : rc_rel E G :=
| rc_compose_intro ar1 ar2 ar3 m1 m2 m3 R R':
  rc1 ar1 m1 ar2 m2 R -> rc2 ar2 m2 ar3 m3 R' ->
  rc_compose rc1 rc2 ar1 m1 ar3 m3 (rel_compose R R').

Definition rc_compose_id_l {E F} (rc: E <=> F):
  @eq (refconv _ _) (rc_compose rc_id rc) rc.
Proof.
  apply antisymmetry; unfold rc_ref; intros * Hrc;
    exists R1; split; try easy.
  - rc_destruct Hrc. rc_destruct H.
    eapply refconv_clo; [ | eauto ].
    intros x y Hxy. apply Hsub.
    eexists; split; eauto.
  - rewrite <- (rel_compose_id_right R1).
    rc_econstructor; eauto. rc_econstructor.
Qed.

Definition rc_compose_id_r {E F} (rc: E <=> F): rc_compose rc rc_id = rc.
Proof.
Admitted.

Definition rc_compose_assoc {E F G H} (rc1: E <=> F) (rc2: F <=> G) (rc3: G <=> H):
  rc_compose (rc_compose rc1 rc2) rc3 = rc_compose rc1 (rc_compose rc2 rc3).
Proof.
Admitted.

(** *** Tensor Product Operator on Refinement Conventions *)

Inductive esig_tens (E F: esig): esig :=
| esig_tens_intro ar1 ar2 :
  E ar1 -> F ar2 -> esig_tens E F (ar1 * ar2)%type.

Arguments esig_tens_intro {_ _ _ _} _ _.
Infix "*" := esig_tens: esig_scope.
Infix "*" := esig_tens_intro: event_scope.
Delimit Scope event_scope with event.

Inductive rc_prod {E1 E2 F1 F2} (rc1: E1 <=> F1) (rc2: E2 <=> F2) : rc_rel (E1 * E2) (F1 * F2) :=
| rc_prod_intro ar1 m1 ar1' m1' ar2 m2 ar2' m2' R1 R2:
  rc1 ar1 m1 ar1' m1' R1 -> rc2 ar2 m2 ar2' m2' R2 ->
  rc_prod rc1 rc2 _ (m1 * m2)%event _ (m1' * m2')%event (R1 * R2)%rel.

Infix "*" := rc_prod: rc_scope.
Delimit Scope rc_scope with rc.
Bind Scope rc_scope with refconv.

Lemma rel_prod_compose {S1 S2 S3 T1 T2 T3}
      (R1: S1 -> S2 -> Prop) (R2: S2 -> S3 -> Prop) (R3: T1 -> T2 -> Prop) (R4: T2 -> T3 -> Prop):
  (rel_compose R1 R2 * rel_compose R3 R4)%rel =
    (rel_compose (R1 * R3) (R2 * R4))%rel.
Proof.
  unfold rel_compose, prod_rel.
  apply functional_extensionality. intros [? ?].
  apply functional_extensionality. intros [? ?].
  apply propositional_extensionality.
  split; firstorder. cbn in *. eexists (_, _); eauto.
Qed.

Lemma rc_prod_compose {E1 E2 F1 F2 G1 G2}
      (rca1: E1 <=> F1) (rca2: E2 <=> F2) (rcb1: F1 <=> G1) (rcb2: F2 <=> G2):
  @eq (refconv _ _)
      (rc_compose rca1 rcb1 * rc_compose rca2 rcb2)%rc
      (rc_compose (rca1 * rca2) (rcb1 * rcb2)).
Proof.
  apply antisymmetry; intros ? [ ? ? me1 me2 ] ? [ ? ? mg1 mg2 ] R H.
  - rc_destruct H.
    rc_destruct H as  [ ? ? ? ? ? ? Ra Rb ].
    rc_destruct H0 as  [ ? ? ? ? ? ? Rc Rd ].
    exists (rel_compose (Ra * Rc) (Rb * Rd)). split.
    + rc_econstructor; rc_econstructor; eauto.
    + rewrite <- rel_prod_compose.
      etransitivity; eauto.
      apply prod_subrel; eauto.
  - rc_destruct H.
    rc_destruct H as [ ? ? ? ? ? ? ? ? Ra Rb ].
    rc_inversion H0 as [ ? ? ? ? ? ? ? ? Rc Rd ]. depsubst.
    exists ((rel_compose Ra Rc) * (rel_compose Rb Rd))%rel. split.
    + rc_econstructor; rc_econstructor; eauto.
    + rewrite rel_prod_compose.
      etransitivity; eauto.
      apply rel_compose_subrel; eauto.
Qed.

(** ** Functor from RC to ADJ(Ispec) *)
Section RC_ADJ.
  Context {E F} (rc: E <=> F).

(* The choice of the relations on the return values is essentially the choice of
   worlds in the case of calling convention *)
  Definition rc_adj_left : E ~> F :=
    fun ar m =>
      sup ar' m', sup { R | rc ar' m' ar m R },
      int m' >>= (fun n' => inf { n | R n' n }, ret n).

  Definition rc_adj_right : F ~> E :=
    fun ar m =>
      inf ar' m', inf { R | rc ar m ar' m' R },
      int m' >>= (fun n' => sup { n | R n n' }, ret n).

  Lemma rc_adj_epsilon : rc_adj_left @ rc_adj_right [= identity.
  Proof.
    intros ar m. unfold rc_adj_left, rc_adj_right, compose, identity.
    rewrite Sup.mor. apply sup_iff. intros ar'.
    rewrite Sup.mor. apply sup_iff. intros m'.
    unfold fsup. rewrite Sup.mor. apply sup_iff.
    intros [R Hrc]. cbn. intm.
    rewrite Inf.mor. apply (inf_at ar).
    rewrite Inf.mor. apply (inf_at m).
    unfold finf. rewrite Inf.mor. eapply (inf_at (exist _ R _)).
    cbn. Unshelve.
    2: { cbn; apply Hrc. }
    unfold int. rewrite !Sup.mor. apply sup_iff. intros [n|].
    - setoid_rewrite FCD.ext_ana. cbn.
      rewrite Sup.mor_join. apply join_lub.
      + setoid_rewrite FCD.ext_ana. cbn.
        apply (sup_at None). reflexivity.
      + rewrite !Sup.mor. apply sup_iff. intros [n' Hr]. cbn.
        setoid_rewrite FCD.ext_ana.
        setoid_rewrite FCD.ext_ana. cbn.
        apply join_lub.
        * apply (sup_at None). reflexivity.
        * rewrite !Inf.mor. apply (inf_at (exist _ n Hr)). cbn.
          setoid_rewrite FCD.ext_ana. cbn.
          apply (sup_at (Some n)).
          setoid_rewrite FCD.ext_ana. reflexivity.
    - setoid_rewrite FCD.ext_ana. cbn.
      setoid_rewrite FCD.ext_ana. cbn.
      apply (sup_at None). reflexivity.
  Qed.

  Lemma rc_adj_eta : identity [= rc_adj_right @ rc_adj_left.
  Admitted.

  Definition rc_adj : E <~> F :=
    {|
      left_arrow := rc_adj_left;
      right_arrow := rc_adj_right;
      epsilon := rc_adj_epsilon;
      eta := rc_adj_eta;
    |}.

End RC_ADJ.
  (* TODO: functoriality *)
Section PROPS.
  Context {E F G} (rc1: E <=> F) (rc2: F <=> G).
  Local Opaque normalize_rc.
  Lemma rc_adj_left_compose:
    rc_adj_left rc2 @ rc_adj_left rc1 = rc_adj_left (rc_compose rc1 rc2).
  Proof.
    unfold rc_adj_left, compose.
    apply antisymmetry; intros ar1 m1; cbn.
    - rewrite !Sup.mor. apply sup_iff. intros ar2.
      rewrite !Sup.mor. apply sup_iff. intros m2.
      unfold fsup at 2. rewrite !Sup.mor.
      apply sup_iff. intros [ R Hr ]. intm.
      rewrite !Sup.mor. apply sup_iff. intros ar3.
      rewrite !Sup.mor. apply sup_iff. intros m3.
      unfold fsup at 2. rewrite !Sup.mor.
      apply sup_iff. intros [ R' Hr' ].
      apply (sup_at ar3). apply (sup_at m3).
      eapply (sup_at (exist _ (fun x z => exists y, R' x y /\ R y z) _)).
      cbn. Unshelve. 2: { cbn. rc_econstructor; eauto. }
      unfold int at 2. rewrite !Sup.mor.
      apply sup_iff. intros [ n3 | ].
      + setoid_rewrite FCD.ext_ana. cbn.
        rewrite Sup.mor_join. apply join_lub.
        * setoid_rewrite FCD.ext_ana. cbn.
          unfold int. setoid_rewrite Sup.mor.
          apply (sup_at None).
          setoid_rewrite FCD.ext_ana. cbn.
          reflexivity.
        * unfold int at 2. rewrite Sup.mor.
          apply (sup_at (Some n3)).
          setoid_rewrite FCD.ext_ana. cbn.
          apply join_r.
          unfold finf. rewrite !Inf.mor.
          apply inf_iff. intros [ n1 [ n2 [ H2 H1 ] ] ]. cbn.
          eapply (inf_at (exist _ n2 H2)). cbn.
          repeat setoid_rewrite FCD.ext_ana. cbn.
          apply join_lub.
          -- rstep. constructor.
          -- rewrite !Inf.mor. eapply (inf_at (exist _ n1 H1)). cbn.
             intm. setoid_rewrite FCD.ext_ana. reflexivity.
      + setoid_rewrite FCD.ext_ana. cbn.
        setoid_rewrite FCD.ext_ana. cbn.
        unfold int. rewrite !Sup.mor. apply (sup_at None).
        setoid_rewrite FCD.ext_ana. cbn. reflexivity.
    - apply sup_iff. intros ar3.
      apply sup_iff. intros m3.
      apply sup_iff. intros [ R Hr ].
      rc_destruct Hr.
      rewrite !Sup.mor. apply (sup_at ar2).
      rewrite !Sup.mor. apply (sup_at m2).
      unfold fsup at 2. rewrite !Sup.mor.
      eapply (sup_at (exist _ R' _)). Unshelve.
      2: { cbn. assumption. } cbn. intm.
      rewrite !Sup.mor. apply (sup_at ar1).
      rewrite !Sup.mor. apply (sup_at m1).
      unfold fsup at 2. rewrite !Sup.mor.
      eapply (sup_at (exist _ R0 _)). Unshelve.
      2: { cbn. assumption. } cbn.
      unfold int at 1. rewrite Sup.mor. apply sup_iff. intros [ n1 | ].
      + setoid_rewrite FCD.ext_ana. cbn.
        apply join_lub.
        * unfold int at 2. rewrite !Sup.mor.
          apply (sup_at None).
          setoid_rewrite FCD.ext_ana. cbn.
          setoid_rewrite FCD.ext_ana. cbn. reflexivity.
        * unfold int at 2. rewrite !Sup.mor.
          apply (sup_at (Some n1)).
          setoid_rewrite FCD.ext_ana. cbn.
          rewrite Sup.mor_join. apply join_r.
          unfold finf. rewrite !Inf.mor.
          apply inf_iff. intros [ n2 H2 ]. cbn.
          repeat setoid_rewrite FCD.ext_ana. cbn.
          apply join_r.
          rewrite !Inf.mor. apply inf_iff. intros [ n3 H3 ]. cbn.
          intm. setoid_rewrite FCD.ext_ana.
          eapply (inf_at (exist _ n3 _)). Unshelve.
          2: { cbn. apply Hsub. eexists; split; eauto. } cbn.
          reflexivity.
      + setoid_rewrite FCD.ext_ana. cbn.
        unfold int. rewrite !Sup.mor. apply (sup_at None).
        setoid_rewrite FCD.ext_ana. cbn.
        setoid_rewrite FCD.ext_ana. cbn.
        reflexivity.
  Qed.

  Lemma rc_adj_right_compose:
    rc_adj_right rc1 @ rc_adj_right rc2 = rc_adj_right (rc_compose rc1 rc2).
  Proof.
  Admitted.

  Lemma rc_adj_left_identity:
    rc_adj_left (@rc_id E) = identity.
  Proof.
    unfold rc_adj_left. apply antisymmetry; intros ar m; cbn.
    - apply sup_iff. intros ar'.
      apply sup_iff. intros m'.
      apply sup_iff. intros [ R Hr ]. rc_destruct Hr. cbn.
      unfold identity, int.
      rewrite Sup.mor. apply sup_iff.
      intros [ n | ].
      + setoid_rewrite FCD.ext_ana. cbn.
        apply join_lub.
        * apply (sup_at None). reflexivity.
        * apply (sup_at (Some n)).
          unfold finf. rewrite Inf.mor.
          eapply (inf_at (exist _ n _)). cbn.
          Unshelve. 2: { cbn. now apply Hsub. }
          setoid_rewrite FCD.ext_ana.
          reflexivity.
      + setoid_rewrite FCD.ext_ana. cbn.
        apply (sup_at None). reflexivity.
    - apply (sup_at ar). apply (sup_at m).
      apply (fsup_at (@eq ar)). rc_econstructor.
      unfold identity, int. apply sup_iff. intros [ n | ].
      + rewrite Sup.mor. apply (sup_at (Some n)).
        setoid_rewrite FCD.ext_ana. cbn.
        apply join_r. unfold finf. rewrite Inf.mor.
        apply inf_iff. intros [ n' <- ]. cbn.
        setoid_rewrite FCD.ext_ana. reflexivity.
      + rewrite Sup.mor. apply (sup_at None).
        setoid_rewrite FCD.ext_ana. reflexivity.
  Qed.

  Lemma rc_adj_right_identity:
    rc_adj_right (@rc_id E) = identity.
  Admitted.

End PROPS.
Coercion rc_adj : refconv >-> poset_adjunction.

(** ** Functor from SC to RC *)

(** *** Embed Language Interfaces *)
Section SIG.

  Variable li: language_interface.
  (* May need to consider the symbol table in the future *)
  Inductive sig: esig :=
  | li_sig: query li -> sig (reply li).

End SIG.

Arguments li_sig {_} _.
Coercion sig: language_interface >-> esig.
Coercion li_sig: query >-> sig.

(** The primitive operator that triggers a query *)
Definition query_int {li} (q: query li): ispec li _ := @int (sig li) _ q.
(* The expected type of the first argument of @int is a general type constructor
   E: Type -> Type instead of [esig], so the coercion does not work *)

(** *** Embed Calling Conventions  *)
Inductive cc_rc {liA liB} (cc: callconv liA liB) : rc_rel liA liB :=
| cc_rc_intro q1 q2 w:
  match_query cc w q1 q2 ->
  cc_rc cc _ (li_sig q1) _ (li_sig q2) (match_reply cc w).

(** *** Properties of the embedding from SC to RC  *)
Lemma cc_rc_id {liA}:
  @eq (refconv _ _) (cc_rc (@cc_id liA)) rc_id.
Proof.
Admitted.

Lemma cc_rc_compose {liA liB liC} (cc1: callconv liA liB) (cc2: callconv liB liC):
  @eq (refconv _ _) (cc_rc (cc_compose cc1 cc2))
      (rc_compose (cc_rc cc1) (cc_rc cc2)).
Proof.
Admitted.

Coercion cc_refconv {liA liB} (cc: callconv liA liB): refconv liA liB :=
  normalize_rc (cc_rc cc).

(** ** Functor from Rel to RC *)
Inductive s_esig (S: Type) : esig :=
| state_event: S -> s_esig S S.
Arguments state_event {_} _.

Inductive rel_rc {S T} (R: S -> T -> Prop) : rc_rel (s_esig S) (s_esig T) :=
| rel_rc_intro m1 m2:
  R m1 m2 -> rel_rc R _ (state_event m1) _ (state_event m2) R.

(** *** Properties of the embedding from Rel to RC *)
Lemma rel_rc_id {S}:
  @eq (refconv _ _) (rel_rc (@eq S)) rc_id.
Proof.
Admitted.

Lemma rel_rc_compose {X Y Z} (S: X -> Y -> Prop) (T: Y -> Z -> Prop):
  @eq (refconv _ _) (rel_rc (rel_compose S T)) (rc_compose (rel_rc S) (rel_rc T)).
Proof.
Admitted.

(** *** Lifting Effect Signatures with States  *)
Definition state_sig (E : esig) (S : Type) : esig := E * s_esig S.
Definition st {E S ar} (m : E ar) (k : S) : state_sig E S (ar * S)%type :=
  esig_tens_intro m (state_event k).

Infix "#" := state_sig (at level 40, left associativity) : esig_scope.

(* TODO: move this to other files *)
Ltac fcd_simpl :=
  repeat (setoid_rewrite FCD.ext_ana; cbn).

Lemma fsup_mor {L M: cdlattice} {f: L -> M} `{Sup.Morphism _ _ f}:
  forall {I} (P : I -> Prop) (M: I -> L), f (sup {x | P x}, M x) = sup {x | P x}, f (M x).
Proof. intros. unfold fsup. eapply Sup.mor. Qed.

Lemma finf_mor {L M: cdlattice} {f: L -> M} `{Inf.Morphism _ _ f}:
  forall {I} (P : I -> Prop) (M: I -> L), f (inf {x | P x}, M x) = inf {x | P x}, f (M x).
Proof. intros. unfold finf. eapply Inf.mor. Qed.

Lemma sup_fsup {L: cdlattice} {I J: Type} (P: J -> Prop) (c: I -> J -> L):
  sup i, sup {j | P j}, c i j = sup {j | P j}, sup i, c i j.
Proof. unfold fsup. apply sup_sup. Qed.

Ltac sup_mor :=
  rewrite !Sup.mor || rewrite !fsup_mor || rewrite !Sup.mor_join || rewrite Sup.mor_bot ||
  setoid_rewrite Sup.mor || setoid_rewrite fsup_mor || setoid_rewrite Sup.mor_join.

Ltac inf_mor :=
  rewrite !Inf.mor || rewrite !finf_mor || rewrite !Inf.mor_meet ||
  setoid_rewrite Inf.mor || setoid_rewrite finf_mor || setoid_rewrite Inf.mor_meet.

Lemma finf_iff {L: cdlattice} {I} (P: I -> Prop) (M: I -> L) x:
  x [= inf { j | P j}, M j <-> forall i: { j | P j }, x [= M (proj1_sig i).
Proof. unfold finf. apply inf_iff. Qed.

Lemma fsup_iff {L: cdlattice} {I} (P: I -> Prop) (M: I -> L) x:
  sup { j | P j}, M j [= x <-> forall i: { j | P j }, M (proj1_sig i) [= x.
Proof. unfold fsup. apply sup_iff. Qed.

Tactic Notation "inf_intro" simple_intropattern(p) :=
  inf_mor; (apply finf_iff || apply inf_iff) ; intros p; cbn.

Tactic Notation "sup_intro" simple_intropattern(p) :=
  sup_mor; (apply fsup_iff || apply sup_iff) ; intros p; cbn.
