From Coq Require Import
     Relations RelationClasses
     FunctionalExtensionality
     PropExtensionality.
From structures Require Import
     Effects Lattice.
Require Import ISpecAdjunction.
Require Import CompCertIntSpec.
Require Import LanguageInterface.
Require Import CAL.
Require Import IntSpec.
From lattices Require Import
     Upset Downset FCD.
Import ISpec.

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
Definition refconv (E F: esig) :=
  forall ar1, E ar1 -> forall ar2, F ar2 -> (ar1 -> ar2 -> Prop) -> Prop.
Infix "<=>" := refconv (at level 50).

(** *** Order on Refinement Conventions  *)
Definition rc_ref {E F} (rc1 rc2: E <=> F) :=
  forall ar1 m1 ar2 m2 R1,
    rc1 ar1 m1 ar2 m2 R1 ->
    exists R2, rc2 ar1 m1 ar2 m2 R2 /\ subrel R2 R1.

Definition rc_eqv {E F} (rc1 rc2: E <=> F) := rc_ref rc1 rc2 /\ rc_ref rc2 rc1.

Instance refconv_eqrel {E F} (rc: E <=> F) ar1 m1 ar2 m2:
  Proper (eqrel ==> iff) (rc ar1 m1 ar2 m2).
Proof.
  intros x y Heq. replace y with x. reflexivity.
    unfold rel in *.
    apply functional_extensionality. intros a.
    apply functional_extensionality. intros b.
    apply propositional_extensionality.
    unfold eqrel, subrel, rel_inter, flip in Heq.
    split; apply Heq.
Qed.

(** *** Categorical Structures of Refinment Conventions *)
Inductive rc_id {E} : E <=> E :=
| rc_id_intro ar m: rc_id ar m ar m eq.

Inductive rc_compose {E F G} (rc1: E <=> F) (rc2: F <=> G) : E <=> G :=
| rc_compose_intro ar1 ar2 ar3 m1 m2 m3 R R':
  rc1 ar1 m1 ar2 m2 R -> rc2 ar2 m2 ar3 m3 R' ->
  rc_compose rc1 rc2 ar1 m1 ar3 m3 (rel_compose R R').

Definition rc_compose_id_l {E F} (rc: E <=> F): rc_eqv (rc_compose rc_id rc) rc.
Proof.
  split; unfold rc_ref; intros * Hrc.
  - destruct Hrc. destruct H.
    exists R'; split; auto.
    rewrite rel_compose_id_right.
    reflexivity.
  - exists R1; split; auto.
    + rewrite <- (rel_compose_id_right R1).
      econstructor; eauto. constructor.
    + reflexivity.
Qed.

Definition rc_compose_id_r {E F} (rc: E <=> F): rc_eqv (rc_compose rc rc_id) rc.
Proof.
Admitted.

Definition rc_compose_assoc {E F G H} (rc1: E <=> F) (rc2: F <=> G) (rc3: G <=> H):
  rc_eqv (rc_compose (rc_compose rc1 rc2) rc3) (rc_compose rc1 (rc_compose rc2 rc3)).
Proof.
Admitted.

(** *** Tensor Product Operator on Refinement Conventions *)
Inductive esig_prod (E F: esig): esig :=
| esig_prod_intro ar1 ar2 :
  E ar1 -> F ar2 -> esig_prod E F (ar1 * ar2)%type.
Arguments esig_prod_intro {_ _ _ _} _ _.
Infix "*" := esig_prod: esig_scope.
Infix "*" := esig_prod_intro: event_scope.
Delimit Scope event_scope with event.

Inductive rc_prod {E1 E2 F1 F2} (rc1: E1 <=> F1) (rc2: E2 <=> F2) : E1 * E2 <=> F1 * F2 :=
| rc_prod_intro ar1 m1 ar1' m1' ar2 m2 ar2' m2' R1 R2:
  rc1 ar1 m1 ar1' m1' R1 -> rc2 ar2 m2 ar2' m2' R2 ->
  rc_prod rc1 rc2 (ar1 * ar2)%type (m1 * m2)%event
          (ar1' * ar2')%type (m1' * m2')%event (R1 * R2)%rel.
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
      rc_eqv (rc_compose rca1 rcb1 * rc_compose rca2 rcb2)
             (rc_compose (rca1 * rca2) (rcb1 * rcb2)).
Proof.
  split; intros ? [ ? ? me1 me2 ] ? [ ? ? mg1 mg2 ] R H; exists R.
  - split; try reflexivity.
    destruct H. destruct H. destruct H0.
    rewrite rel_prod_compose.
    econstructor; econstructor; eauto.
  - split; try reflexivity.
    destruct H.
    destruct m1. destruct m2. destruct m3.
    inversion H. subst. depsubst.
    inversion H0. subst. depsubst.
    rewrite <- rel_prod_compose.
    constructor; econstructor; eauto.
Qed.

(** ** Functor from RC to ADJ(Ispec) *)
Section RC_ADJ.
  Context {E F} (rc: E <=> F).

(* The choice of the relations on the return values is essentially the choice of
   worlds in the case of calling convention *)
  Definition rc_adj_left : E ~> F :=
    fun ar m =>
      sup ar', sup m', sup { R | rc ar' m' ar m R },
      int m' >>= (fun n' => inf { n | R n' n }, ret n).

  Definition rc_adj_right : F ~> E :=
    fun ar m =>
      inf ar', inf m', inf { R | rc ar m ar' m' R },
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

  (* TODO: functoriality *)
End RC_ADJ.
Coercion rc_adj : refconv >-> poset_adjunction.

(** ** Functor from SC to RC *)
Inductive cc_rc {liA liB} (cc: callconv liA liB) : liA <=> liB :=
| cc_rc_intro q1 q2 w:
  match_query cc w q1 q2 ->
  cc_rc cc _ (li_sig q1) _ (li_sig q2) (match_reply cc w).
Coercion cc_rc : callconv >-> refconv.

(** *** Properties of the embedding from SC to RC  *)
Lemma cc_rc_id {liA}: rc_eqv (@cc_id liA) rc_id.
Proof.
Admitted.

Lemma cc_rc_compose {liA liB liC} (cc1: callconv liA liB) (cc2: callconv liB liC):
  rc_eqv (cc_compose cc1 cc2) (rc_compose cc1 cc2).
Proof.
Admitted.

(** ** Functor from Rel to RC *)
Inductive s_esig (S: Type) : esig :=
| state_event: S -> s_esig S S.
Coercion s_esig: Sortclass >-> esig.
Arguments state_event {_} _.

Inductive rel_rc {S T} (R: S -> T -> Prop) : S <=> T :=
| rel_rc_intro m1 m2:
  R m1 m2 -> rel_rc R _ (state_event m1) _ (state_event m2) R.

(** *** Properties of the embedding from Rel to RC *)
Lemma rel_rc_id {S}:
  rc_eqv (rel_rc (@eq S)) rc_id.
Proof.
Admitted.

Lemma rel_rc_compose {X Y Z} (S: X -> Y -> Prop) (T: Y -> Z -> Prop):
  rc_eqv (rel_rc (rel_compose S T)) (rc_compose (rel_rc S) (rel_rc T)).
Proof.
Admitted.

(** ** States in the Specifications *)
Definition CALspec_mor' {E S} (L : CALspec E S) : 0 ~> E * S :=
  fun _ '(esig_prod_intro _ _ m s_ev) =>
    match s_ev with
    | state_event s => L _ m s
    end.

Require Import CModule.
From compcert Require Import
     Memory AST Values
     Clight Ctypes
     LanguageInterface
     Events Globalenvs
     Smallstep.

(** The language interface "C simple" which does not include the memory *)
Record c_query :=
  cq {
      cq_vf: val;
      cq_sg: signature;
      cq_args: list val;
    }.

Record c_reply :=
  cr { cr_retval: val; }.

Canonical Structure li_c :=
  {|
    query := c_query;
    reply := c_reply;
    entry := cq_vf;
  |}.

Notation li_cmem := LanguageInterface.li_c.
Notation cqmem := LanguageInterface.cq.
Notation crmem := LanguageInterface.cr.

(** Some auxiliary definitions *)
Definition slift {E F: esig} {S: Type} (f: E ~> F): E * S ~> F * S. Admitted.
Definition iota {S: Type}: li_cmem * S ~> li_c * (mem * S)%type. Admitted.
Definition umem: li_c ~> li_cmem. Admitted.

(** ** Construction of a certified abstraction layer *)
(* L2 is the overlay *)
Record certi_layer {E1 E2: esig} {S1 S2: Type} se :=
  {
    L1: 0 ~> E1 * S1;
    L1_rc: E1 <=> li_c;
    L2: 0 ~> E2 * S2;
    L2_rc: E2 <=> li_c;
    module: list Clight.program;
    sk: AST.program unit unit;
    abs_rel: S2 -> mem * S1 -> Prop;

    layer_rel:
    L2 [= right_arrow (L2_rc * (rel_rc abs_rel))%rc (** C@(mem@S1) ~> E2@S2 *)
       @ iota                                      (** (C@mem)@S1 ~> C@(mem*S1)  *)
       @ slift (ang_lts_spec (CModule.semantics module sk se)) (** (C@mem)@S1 ~> (C@mem)@S1 *)
       @ slift (umem @ left_arrow L1_rc)                       (** E1@S1 ~> (C@mem)@S1 *)
       @ L1;                                                   (** 0 ~> E1@S1 *)
  }.
