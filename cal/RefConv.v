From Coq Require Import
     Relations RelationClasses
     FunctionalExtensionality
     PropExtensionality.
From models Require Import IntSpec.
From structures Require Import
     Effects Lattice.
From lattices Require Import
     Upset Downset FCD.
From compcert Require Import LanguageInterface.
Import ISpec.

Local Obligation Tactic := idtac.

(* TODO: move this to other files *)
Ltac fcd_simpl :=
  repeat (setoid_rewrite FCD.ext_ana; cbn).

Lemma fsup_mor {L M: cdlattice} {f: L -> M} `{Sup.Morphism _ _ f}:
  forall {I} (P : I -> Prop) (M: I -> L), f (sup {x | P x}, M x) = sup {x | P x}, f (M x).
Proof. intros. unfold fsup. eapply Sup.mor. Qed.

Lemma finf_mor {L M: cdlattice} {f: L -> M} `{Inf.Morphism _ _ f}:
  forall {I} (P : I -> Prop) (M: I -> L), f (inf {x | P x}, M x) = inf {x | P x}, f (M x).
Proof. intros. unfold finf. eapply Inf.mor. Qed.

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

Ltac clear_hyp :=
  repeat match goal with
         | [ H : (?t = ?t)%type |- _ ] => clear H
         end.

Module M.

  Inductive t (E: esig) : Type -> Type :=
    | Sup {I A}: (I -> t E A) -> t E A
    | Inf {I A}: (I -> t E A) -> t E A
    | Int {A}: E A -> t E A
    | Ret {A}: A -> t E A
    | Bind {A B}: t E A -> (A -> t E B) -> t E B.
  Arguments Sup {E I A} _.
  Arguments Inf {E I A} _.
  Arguments Int {E A} _.
  Arguments Ret {E A} _.
  Arguments Bind {E A B} _ _.

  Fixpoint exec {E A} (m: t E A): ISpec.t E A :=
    match m with
    | Sup f => sup i, exec (f i)
    | Inf f => inf i, exec (f i)
    | Int m => ISpec.int m
    | Ret x => ret x
    | Bind x k => ISpec.bind (fun v => exec (k v)) (exec x)
    end.
  Coercion exec0 {E A} := @exec E A.

  Definition subst (E F: esig) := forall A, F A -> @t E A.
  Coercion subst0 {E F} (s: subst E F): ISpec.subst E F := fun _ m => s _ m.

  Definition ref {E A} (x y: t E A) := x [= y.
  Definition ref_ {E F} (x y: subst E F) := forall A m, (x A m) [= (y A m).
  Definition eq {E A} (x y: t E A) := exec x = exec y.
  Definition eq_ {E F} (x y: subst E F) := forall A m, exec (x A m) = exec (y A m).

  Fixpoint apply {E F} (s: subst E F) {A} (x: @t F A): @t E A :=
    match x with
    | Sup f => Sup (fun i => apply s (f i))
    | Inf f => Inf (fun i => apply s (f i))
    | Int m => s _ m
    | Ret x => Ret x
    | Bind x k => Bind (apply s x) (fun v => apply s (k v))
    end.

  Instance ref_preo {E A} : PreOrder (@ref E A).
  Proof.
    unfold ref. split.
    - intros x. reflexivity.
    - intros x y z Hxy Hyz. etransitivity; eauto.
  Qed.
  Instance ref_preo_ {E A} : PreOrder (@ref_ E A).
  Proof.
    unfold ref. split.
    - intros x ? ?. reflexivity.
    - intros x y z Hxy Hyz ? ?. etransitivity; eauto.
  Qed.

  Instance eq_equiv {E A} : Equivalence (@eq E A).
  Proof.
    split.
    - intros x. reflexivity.
    - intros x y Hxy. symmetry. eauto.
    - intros x y z Hxy Hyz. etransitivity; eauto.
  Qed.
  Instance eq_equiv_ {E A} : Equivalence (@eq_ E A).
  Proof.
    split.
    - intros x ? ?. reflexivity.
    - intros x y Hxy ? ?. symmetry. eauto.
    - intros x y z Hxy Hyz ? ?. etransitivity; eauto.
  Qed.

  Instance ref_po {E A} : Antisymmetric _ (@eq E A) (@ref E A).
  Proof. intros x y ? ?. unfold eq. apply antisymmetry; eauto. Qed.
  Instance ref_po_ {E A} : Antisymmetric _ (@eq_ E A) (@ref_ E A).
  Proof. intros x y ? ? ? ?. apply antisymmetry; eauto. Qed.

  Instance bind_proper_eq {E A B}:
    Proper (eq ==> (pointwise_relation _ eq) ==> eq) (@Bind E A B).
  Proof.
    intros x1 x2 Hx k1 k2 Hk. unfold eq. cbn.
    rewrite Hx. unfold pointwise_relation in Hk.
    f_equal. extensionality v. apply Hk.
  Qed.

  Definition compose {E F G} (s: subst F G) (t: subst E F): subst E G :=
    fun A m => apply t (s A m).
  Definition identity {E: esig}: subst E E := fun A m => Int m.

  Lemma compose_int_l {E F} (s: subst E F):
    eq_ (compose (@Int F) s) s.
  Proof. unfold compose. intros A m; reflexivity. Qed.
  Lemma compose_int_r {E F} (s: subst E F):
    eq_ (compose s (@Int E)) s.
  Proof.
    intros A m. unfold compose. generalize (s A m) as x. clear m.
    induction x; cbn; try reflexivity.
    - setoid_rewrite H. reflexivity.
    - setoid_rewrite H. reflexivity.
    - rewrite IHx. setoid_rewrite H. reflexivity.
  Qed.
  Lemma apply_assoc {E F G} (s: subst G F) (t: subst F E) {A} (x: @M.t _ A):
    eq (apply s (apply t x)) (apply (compose t s) x).
  Proof.
    induction x; cbn; try reflexivity; unfold eq; cbn.
    - f_equal. extensionality i. apply H.
    - f_equal. extensionality i. apply H.
    - rewrite IHx. f_equal. extensionality i. apply H.
  Qed.

  Lemma compose_unit_l {E F} (s: subst E F):
    eq_ (compose identity s) s.
  Proof. apply compose_int_l. Qed.
  Lemma compose_unit_r {E F} (s: subst E F):
    eq_ (compose s identity) s.
  Proof. apply compose_int_r. Qed.
  Lemma compose_assoc {E F G H} (s: subst G H) (t: subst F G) (u: subst E F):
    eq_ (compose (compose s t) u) (compose s (compose t u)).
  Proof.
    cbn. intros A m. unfold compose.
    generalize (s A m) as x. clear m. intros x.
    apply apply_assoc.
  Qed.

  Definition fsup {E A} {I} (P : I -> Prop) (f : I -> t E A) :=
    Sup (I := sig P) (fun x => f (proj1_sig x)).
  Definition finf {E A} {I} (P : I -> Prop) (f : I -> t E A) :=
    Inf (I := sig P) (fun x => f (proj1_sig x)).

End M.

(* -------- M.spec -------- *)

Declare Scope mspec_scope.
Delimit Scope mspec_scope with mspec.
Bind Scope mspec_scope with M.t.

Notation "⊔ i .. j , M" := (M.Sup (fun i => .. (M.Sup (fun j => M)) .. ))
  (at level 65, i binder, j binder, right associativity).
Notation "⊓ i .. j , M" := (M.Inf (fun i => .. (M.Inf (fun j => M)) .. ))
  (at level 65, i binder, j binder, right associativity).
Notation "⊔ { x | P } , M" := (M.fsup (fun x => P) (fun x => M))
  (at level 65, x ident, right associativity).
Notation "⊔ { x : A | P } , M" := (M.fsup (fun x : A => P) (fun x : A => M))
  (at level 65, A at next level, x ident, right associativity).
Notation "⊓ { x | P } , M" := (M.finf (fun x => P) (fun x => M))
  (at level 65, x ident, right associativity).
Notation "⊓ { x : A | P } , M" := (M.finf (fun x : A => P) (fun x : A => M))
  (at level 65, x ident, right associativity).

Notation "x ⊑ y" := (M.ref x%mspec y%mspec) (at level 70, no associativity, only printing).
Notation "x ⊑ y" := (M.ref_ x%mspec y%mspec) (at level 70, no associativity).
Notation "x ≡ y" := (M.eq x%mspec y%mspec) (at level 70, only printing) : mspec_scope.
Notation "x ≡ y" := (M.eq_ x%mspec y%mspec) (at level 70) : mspec_scope.

Infix "⤳" := M.subst (at level 99).
Notation "x ≫= k" := (M.Bind x k) (at level 40, left associativity).
Notation "v ← x ; M" := (M.Bind (fun v => M) x) (at level 65, right associativity).
Notation "x // f" := (M.apply f x) (at level 70).
Infix "∘" := M.compose.

(** * Adjunctions in Interaction Specification *)

(** An adjunction A ⇆ B is a pair or morphisms which can "cancel" each other *)
(* TODO: a more general formalization of adjunctions? *)
(* A is the high level specification; B is the low level implementation *)
Class poset_adjunction (A B: esig) :=
  {
    left_arrow : A ⤳ B;
    right_arrow : B ⤳ A;
    epsilon : left_arrow ∘ right_arrow ⊑ M.identity;
    eta : M.identity ⊑ right_arrow ∘ left_arrow;
  }.
Arguments left_arrow {_ _}.
Arguments right_arrow {_ _}.
Arguments epsilon {_ _}.
Arguments eta {_ _}.

Infix "<~>" := poset_adjunction (at level 50).

(** ** Composition and identity of adjunctions *)

(* TODO:
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
*)

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

(** ** Definition *)

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

(** ** Order on Refinement Conventions  *)

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

(** ** Calculating the upward closure *)
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
Global Opaque normalize_rc.

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

(** ** Categorical Structures of Refinment Conventions *)
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

Definition rc_compose_id_r {E F} (rc: E <=> F):
  @eq (refconv _ _) (rc_compose rc rc_id) rc.
Proof.
  apply antisymmetry; unfold rc_ref; intros * Hrc;
    exists R1; split; try easy.
  - rc_destruct Hrc. rc_destruct H0.
    eapply refconv_clo; [ | eauto ].
    intros x y Hxy. apply Hsub.
    eexists; split; eauto.
  - rewrite <- (rel_compose_id_left R1).
    rc_econstructor; eauto. rc_econstructor.
Qed.

Definition rc_compose_assoc {E F G H} (rc1: E <=> F) (rc2: F <=> G) (rc3: G <=> H):
  @eq (refconv _ _) (rc_compose (rc_compose rc1 rc2) rc3)
      (rc_compose rc1 (rc_compose rc2 rc3)).
Proof.
  apply antisymmetry; unfold rc_ref; intros * Hrc;
    exists R1; split; try easy.
  - rc_destruct Hrc. rc_destruct H0.
    eapply refconv_clo.
    2: {
      rc_econstructor; eauto.
      rc_econstructor; eauto.
    }
    rewrite <- rel_compose_assoc.
    etransitivity; eauto.
    apply rel_compose_subrel; eauto. reflexivity.
  - rc_destruct Hrc. rc_destruct H1.
    eapply refconv_clo.
    2: {
      rc_econstructor; eauto.
      rc_econstructor; eauto.
    }
    rewrite rel_compose_assoc.
    etransitivity; eauto.
    apply rel_compose_subrel; eauto. reflexivity.
Qed.

(** ** Tensor Product on Refinement Conventions *)

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

(** * Functor from RC to ADJ(Ispec) *)

(** ** Definition *)

Section RC_ADJ.
  (* E is the source level signature *)
  Context {E F} (rc: E <=> F).

  (* The choice of the relations on the return values is essentially the choice
     of worlds in the case of calling convention *)
  Definition rc_adj_left : E ⤳ F :=
    fun ar m =>
      ⊔ ar' m', ⊔ { R | rc ar' m' ar m R }, M.Int m' ≫=
        (fun n' => ⊓ { n | R n' n }, M.Ret n).

  Definition rc_adj_right : F ⤳ E :=
    fun ar m =>
      ⊓ ar' m', ⊓ { R | rc ar m ar' m' R }, M.Int m' ≫=
        (fun n' => ⊔ { n | R n n' }, M.Ret n).

  Lemma rc_adj_epsilon : rc_adj_left ∘ rc_adj_right ⊑ M.identity.
  Proof.
    intros ar m. cbn.
    apply sup_iff. intros ar'. apply sup_iff. intros m'.
    apply sup_iff. intros [R Hrc]. cbn.
    rewrite Inf.mor. apply (inf_at ar).
    rewrite Inf.mor. apply (inf_at m).
    rewrite Inf.mor. apply (inf_at (exist _ R Hrc)).
    unfold int. rewrite !Sup.mor.
    apply sup_iff. intros [n|].
    - apply (sup_at (Some n)). fcd_simpl.
      rewrite Sup.mor_join. apply join_lub.
      + setoid_rewrite FCD.ext_ana. cbn.
        rstep. constructor.
      + rewrite !Sup.mor. apply sup_iff. intros [n' Hr]. cbn.
        setoid_rewrite FCD.ext_ana.
        setoid_rewrite FCD.ext_ana. cbn.
        apply join_lub.
        * rstep. constructor.
        * rewrite !Inf.mor. apply (inf_at (exist _ n Hr)). cbn.
          setoid_rewrite FCD.ext_ana. reflexivity.
    - apply (sup_at None). fcd_simpl. reflexivity.
  Qed.

  Lemma rc_adj_eta : M.identity ⊑ rc_adj_right ∘ rc_adj_left.
    intros ar m. cbn.
    apply inf_iff. intros ar'. apply inf_iff. intros m'.
    apply inf_iff. intros [R Hrc]. cbn.
    sup_mor. apply (sup_at ar).
    sup_mor. apply (sup_at m).
    sup_mor. apply (sup_at (exist _ R Hrc)). cbn.
    unfold int. rewrite !Sup.mor.
    apply sup_iff. intros [n|].
    - apply (sup_at (Some n)). fcd_simpl.
      rewrite Sup.mor_join. apply join_r.
      rewrite !Inf.mor. apply inf_iff. intros [n' Hr]. cbn.
      fcd_simpl. apply join_r.
      rewrite Sup.mor. apply (sup_at (exist _ n Hr)). cbn.
      fcd_simpl. reflexivity.
    - apply (sup_at None). fcd_simpl. reflexivity.
  Qed.

  Definition rc_adj : E <~> F :=
    {|
      left_arrow := rc_adj_left;
      right_arrow := rc_adj_right;
      epsilon := rc_adj_epsilon;
      eta := rc_adj_eta;
    |}.

End RC_ADJ.

(** ** Functoriality *)

Section FUNCTOR.
  Context {E F G} (rc1: E <=> F) (rc2: F <=> G).

  Lemma left_arrow_compose:
    left_arrow (rc_adj rc2) @ left_arrow (rc_adj rc1) =
      left_arrow (rc_adj (rc_compose rc1 rc2)).
  Proof.
    apply antisymmetry; intros ar1 m1; cbn; unfold compose.
    - unfold rc_adj_left at 2 3.
      rewrite !Sup.mor. apply sup_iff. intros ar2.
      rewrite !Sup.mor. apply sup_iff. intros m2.
      unfold fsup at 1. rewrite !Sup.mor.
      apply sup_iff. intros [ R Hr ]. cbn.
      (* rewrite apply_bind. *)
      rewrite apply_bind_inf_left. intm.
      unfold rc_adj_left.
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
    - unfold rc_adj_left at 1 3.
      apply sup_iff. intros ar3.
      apply sup_iff. intros m3.
      apply sup_iff. intros [ R Hr ].
      rc_destruct Hr.
      rewrite !Sup.mor. apply (sup_at ar2).
      rewrite !Sup.mor. apply (sup_at m2).
      unfold fsup at 1. rewrite !Sup.mor.
      eapply (sup_at (exist _ R' _)). Unshelve.
      2: { cbn. assumption. } cbn.
      rewrite apply_bind_inf_left.
      (* rewrite apply_bind. *)
      intm. unfold rc_adj_left.
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

  Lemma right_arrow_compose:
    right_arrow (rc_adj rc1) @ right_arrow (rc_adj rc2) =
      right_arrow (rc_adj (rc_compose rc1 rc2)).
  Proof.
    apply antisymmetry; intros ar1 m1; cbn; unfold compose.
    - inf_intro ?. inf_intro m2. apply inf_iff. intros [R Hr].
      rc_destruct Hr.
      eapply inf_at. eapply (inf_at m2). inf_mor. eapply (finf_at R0).
      apply r. cbn.
      (* rewrite apply_bind. *)
      rewrite apply_bind_sup_right.
      intm. unfold rc_adj_right.
      inf_mor. eapply inf_at. inf_mor. eapply (inf_at m3).
      inf_mor. eapply (finf_at R'). apply r0. intm.
      sup_intro [n3|].
      + fcd_simpl. apply join_lub.
        * apply (sup_at None). fcd_simpl. reflexivity.
        * apply (sup_at (Some n3)). fcd_simpl. apply join_r.
          rstep.
          sup_intro (n2 & Hn2). fcd_simpl.
          sup_intro (n1 & Hn1). fcd_simpl.
          eapply (fsup_at n1). apply Hsub.
          eexists; split; eauto.
          reflexivity.
      + apply (sup_at None). fcd_simpl. reflexivity.
    - inf_intro ?. inf_intro m2. inf_intro (R1 & HR1).
      rewrite apply_bind_sup_right.
      (* rewrite apply_bind. *)
      intm.
      inf_intro ?. inf_intro m3. inf_intro (R2 & HR2).
      intm.
      eapply inf_at. eapply (inf_at m3). eapply finf_at.
      rc_econstructor; eauto.
      sup_intro [n3|].
      + fcd_simpl. apply join_lub.
        * apply (sup_at None). fcd_simpl. reflexivity.
        * apply (sup_at (Some n3)). fcd_simpl. apply join_r.
          rstep.
          sup_intro (n1 & Hn1). destruct Hn1 as (n2 & Hn1 & Hn2).
          apply (fsup_at n2). apply Hn2. fcd_simpl.
          sup_mor. apply (fsup_at n1). apply Hn1. fcd_simpl.
          reflexivity.
      + apply (sup_at None). fcd_simpl. reflexivity.
  Qed.

  Lemma left_arrow_id:
    left_arrow (rc_adj (@rc_id E)) = identity.
  Proof.
    apply antisymmetry; intros ar m; cbn; unfold rc_adj_left.
    - apply sup_iff. intros ar'.
      apply sup_iff. intros m'.
      apply sup_iff. intros [ R Hr ]. rc_destruct Hr. cbn.
      unfold identity, int. sup_intro [ n | ].
      + fcd_simpl. apply join_lub.
        * apply (sup_at None). reflexivity.
        * apply (sup_at (Some n)).
          inf_mor. eapply (finf_at n). now apply Hsub.
          now fcd_simpl.
      + apply (sup_at None). now fcd_simpl.
    - apply (sup_at ar). apply (sup_at m).
      apply (fsup_at (@eq ar)). rc_econstructor.
      unfold identity, int. apply sup_iff. intros [ n | ].
      + rewrite Sup.mor. apply (sup_at (Some n)).
        fcd_simpl. apply join_r.
        inf_intro [ n' <- ]. now fcd_simpl.
      + sup_mor. apply (sup_at None). now fcd_simpl.
  Qed.

  Lemma right_arrow_id:
    right_arrow (rc_adj (@rc_id E)) = identity.
  Proof.
    unfold rc_adj_right. apply antisymmetry; intros ar m; cbn.
    - apply (inf_at ar). apply (inf_at m).
      apply (finf_at (@eq ar)). rc_econstructor.
      unfold identity, int. sup_intro [ n | ].
      + fcd_simpl. apply join_lub.
        ** apply (sup_at None). reflexivity.
        ** apply (sup_at (Some n)).
           sup_intro [ n' <- ]. now fcd_simpl.
      + apply (sup_at None). now fcd_simpl.
    - apply inf_iff. intros ar'.
      apply inf_iff. intros m'.
      apply inf_iff. intros [ R Hr ]. rc_destruct Hr. cbn.
      unfold identity, int. sup_intro [ n | ].
      + apply (sup_at (Some n)). fcd_simpl.
        apply join_r. sup_mor.
        eapply (fsup_at n). now apply Hsub.
          now fcd_simpl.
      + apply (sup_at None). now fcd_simpl.
  Qed.

End FUNCTOR.

(** ** Order Preserving *)

Lemma int_ref {E A B} (x: E A) (f g: A -> t E B):
  (forall a, f a [= g a) ->
  a <- int x; f a [= a <- int x; g a.
Proof.
  intros H. sup_intro [a|].
  - fcd_simpl. apply join_lub.
    + apply (sup_at None). fcd_simpl. reflexivity.
    + apply (sup_at (Some a)). fcd_simpl.
      apply join_r. rewrite (H a). reflexivity.
  - apply (sup_at None). fcd_simpl. reflexivity.
Qed.

Section ORDER.

  Context {E F} (rc1 rc2: E <=> F) (H: rc_ref rc1 rc2).

  Lemma left_arrow_monotonic:
    left_arrow (rc_adj rc1) [= left_arrow (rc_adj rc2).
  Proof.
    intros ? e. cbn. unfold rc_adj_left.
    apply sup_iff. intros ?. apply sup_iff. intros f.
    apply sup_iff. intros [R1 H1].
    unfold rc_ref in H. edestruct H as [R2 [HR2 HX]]. exact H1.
    apply (sup_at i). apply (sup_at f).
    eapply (fsup_at R2). exact HR2. cbn.
    apply int_ref. intros a.
    apply inf_iff. intros [z Hz].
    eapply (finf_at z). apply HX. exact Hz. reflexivity.
  Qed.

  Lemma right_arrow_monotonic:
    right_arrow (rc_adj rc2) [= right_arrow (rc_adj rc1).
  Proof.
    intros ? e. cbn. unfold rc_adj_right.
    apply inf_iff. intros ?. apply inf_iff. intros f.
    apply inf_iff. intros [R1 H1].
    unfold rc_ref in H. edestruct H as [R2 [HR2 HX]]. exact H1.
    apply (inf_at i). apply (inf_at f).
    eapply (finf_at R2). exact HR2. cbn.
    apply int_ref. intros a.
    apply sup_iff. intros [z Hz].
    eapply (fsup_at z). apply HX. exact Hz. reflexivity.
  Qed.

End ORDER.

Coercion rc_adj : refconv >-> poset_adjunction.

(** * Functor from SC to RC *)

Require Import Globalenvs.

(** ** Embed Language Interfaces *)
Section SIG.

  Variable li: language_interface.

  Inductive eli: esig :=
  | eli_intro: query li -> Genv.symtbl -> eli (reply li).

End SIG.

Arguments eli_intro {_} _ _.
Coercion eli: language_interface >-> esig.

(** The primitive operator that triggers a query *)
Definition query_int {li} (q: query li) se: ispec li _ := @int (eli li) _ (eli_intro q se).
(* The expected type of the first argument of @int is a general type constructor
   E: Type -> Type instead of [esig], so the coercion does not work *)

(** ** Embed Calling Conventions  *)
Inductive cc_rc {liA liB} (cc: callconv liA liB) : rc_rel liA liB :=
| cc_rc_intro q1 q2 se1 se2 w:
  match_senv cc w se1 se2 ->
  match_query cc w q1 q2 ->
  cc_rc cc _ (eli_intro q1 se1) _ (eli_intro q2 se2) (match_reply cc w).

(** ** Functoriality *)
Lemma cc_rc_id {liA}:
  @eq (refconv _ _) (cc_rc (@cc_id liA)) rc_id.
Proof.
  apply antisymmetry; unfold rc_ref; intros * Hrc.
  - rc_destruct Hrc. cbn in *. subst.
    exists eq. split; eauto.
    exists eq. split; [ constructor | reflexivity ].
  - rc_destruct Hrc.
    exists eq. split; eauto.
    exists eq. split; [ | reflexivity ].
    destruct m.
    replace eq with (@match_reply liA liA 1 tt) by reflexivity.
    constructor; reflexivity.
Qed.

Lemma cc_rc_compose {liA liB liC} (cc1: callconv liA liB) (cc2: callconv liB liC):
  @eq (refconv _ _) (cc_rc (cc_compose cc1 cc2))
      (rc_compose (cc_rc cc1) (cc_rc cc2)).
Proof.
  apply antisymmetry; unfold rc_ref; intros * Hrc.
  - rc_destruct Hrc. destruct w as [[se' w1] w2].
    destruct H as [Hse1 Hse2]. destruct H0 as [q' [Hq1 Hq2]].
    exists (match_reply (cc1 @ cc2) (se', w1, w2)). split; eauto.
    exists (match_reply (cc1 @ cc2) (se', w1, w2)). split; [ | reflexivity ].
    apply rc_compose_intro with (m2 := (eli_intro q' se')).
    + exists (match_reply cc1 w1). split; [ | reflexivity ].
      constructor; eauto.
    + exists (match_reply cc2 w2). split; [ | reflexivity ].
      constructor; eauto.
  - rc_destruct Hrc. rc_destruct H.
    rc_inversion H0. depsubst. clear Hrel.
    exists (rel_compose R R'). split; eauto.
    exists (rel_compose (match_reply cc1 w) (match_reply cc2 w0)). split.
    + replace (rel_compose (match_reply cc1 w) (match_reply cc2 w0))
        with (match_reply (cc1 @ cc2) (se2, w, w0)).
      * constructor; [ | eexists ]; split; eauto.
      * reflexivity.
    + apply rel_compose_subrel; eauto.
Qed.

Require CallconvAlgebra.

(** ** Order *)
Lemma cc_rc_ref {liA liB} (cc1 cc2: callconv liA liB):
  CallconvAlgebra.ccref cc1 cc2 ->
  rc_ref (cc_rc cc1) (cc_rc cc2).
Proof.
  intros H. unfold rc_ref. intros * H1.
  rc_inversion H1. depsubst. clear_hyp.
  edestruct H as (z & Hq & Hse & Hr); eauto.
  exists (match_reply cc2 z). split.
  - rc_econstructor; eauto.
  - intros r1 r2 ?. eauto.
Qed.

Coercion cc_refconv {liA liB} (cc: callconv liA liB): refconv liA liB :=
  normalize_rc (cc_rc cc).

(** * Functor from Rel to RC *)

(** ** Definition *)
Inductive rel_rc {S T} (R: S -> T -> Prop) : rc_rel (est S) (est T) :=
| rel_rc_intro m1 m2:
  R m1 m2 -> rel_rc R _ (est_intro m1) _ (est_intro m2) R.

(** ** Functoriality *)
Lemma rel_rc_id {S}:
  @eq (refconv _ _) (rel_rc (@eq S)) rc_id.
Proof.
  apply antisymmetry; unfold rc_ref; intros * Hrc.
  - rc_destruct Hrc. subst.
    exists eq. split; eauto.
    exists eq. split; [ constructor | reflexivity ].
  - rc_destruct Hrc.
    exists eq. split; eauto.
    exists eq. split; [ | reflexivity ].
    destruct m. constructor. reflexivity.
Qed.

Lemma rel_rc_compose {X Y Z} (S: X -> Y -> Prop) (T: Y -> Z -> Prop):
  @eq (refconv _ _) (rel_rc (rel_compose S T)) (rc_compose (rel_rc S) (rel_rc T)).
Proof.
  apply antisymmetry; unfold rc_ref; intros * Hrc.
  - rc_destruct Hrc.
    exists (rel_compose S T). split; eauto.
    destruct H as (? & H1 & H2).
    exists (rel_compose S T). split; [ econstructor | reflexivity ].
    exists S. split; [ econstructor | reflexivity ]; eauto.
    exists T. split; [ econstructor | reflexivity ]; eauto.
  - rc_destruct Hrc. rc_destruct H.
    rc_inversion H0. depsubst. clear Hrel.
    exists (rel_compose R R'). split; eauto.
    exists (rel_compose S R0). split.
    econstructor. eexists; split; eauto.
    apply rel_compose_subrel; eauto.
Qed.
