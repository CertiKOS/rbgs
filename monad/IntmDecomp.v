Require Import coqrel.LogicalRelations.
Require Import Classical.
Require Import IntmDef.
Require Import IntmTactics.

Local Obligation Tactic := cbn; eauto.

Module Intm.
  Import IntmDef.Intm.
  Import IntmTactics.Intm.

  (** * Decomposition *)

  (** ** Components *)

  Program Definition phi {M N P Q A B} (x : t M N A) : t P Q B :=
    {|
      has t := has x undef;
    |}.

  Program Definition nu {M N P Q A} (x : t M N A) : t P Q A :=
    {|
      has t := (exists v, has x (val v) /\ t = val v) \/ has x undef;
    |}.
  Next Obligation.
    firstorder. subst. inversion H0. eauto.
  Qed.

  Program Definition rho {M N P Q A} (x : t M N A) : t P Q A :=
    {|
      has t :=
        (exists v, has x (val v) /\ t = val v) \/
        (has x div /\ t = div) \/
        has x undef;
    |}.
  Next Obligation.
    firstorder; subst; inversion H0; eauto.
  Qed.

  Program Definition mu {M N P Q A} (x : t M N A) : t P Q M :=
    {|
      has t := (exists m, has x (move m) /\ t = val m) \/ has x undef;
    |}.
  Next Obligation.
    firstorder. subst. inversion H0. eauto.
  Qed.

  Program Definition delta {M N A} (x : t M N A) (m : M) (n : N) : t M N A :=
    {| has t := has x (tcons m n t) |}.
  Next Obligation.
    eauto using closed.
  Qed.

  (** ** Relational properties *)

  Global Instance phi_ref :
    Monotonic
      (@phi)
      (forallr -, forallr -, forallr -, forallr -, forallr -, forallr -,
        ref ++> ref).
  Proof.
    firstorder.
  Qed.

  Global Instance nu_ref :
    Monotonic
      (@nu)
      (forallr -, forallr -, forallr -, forallr -, forallr -, ref ++> ref).
  Proof.
    firstorder.
  Qed.

  Global Instance rho_ref :
    Monotonic
      (@rho)
      (forallr -, forallr -, forallr -, forallr -, forallr -, ref ++> ref).
  Proof.
    firstorder.
  Qed.

  Global Instance mu_ref :
    Monotonic
      (@mu)
      (forallr -, forallr -, forallr -, forallr -, forallr -, ref ++> ref).
  Proof.
    firstorder.
  Qed.

  Global Instance delta_ref :
    Monotonic
      (@delta)
      (forallr -,forallr -,forallr -, ref ++> eq ==> eq ==> ref).
  Proof.
    repeat rstep; subst; firstorder.
  Qed.

  (** ** Various properties *)

  Lemma rho_decr {M N A} (x : t M N A) :
    ref (rho x) x.
  Proof.
    destruct 1; firstorder subst; eauto using closed.
  Qed.

  Lemma phi_decr {M N A} (x : t M N A) :
    ref (phi x) x.
  Proof.
    red. cbn. eauto using closed.
  Qed.

  Hint Resolve rho_decr phi_decr : monad. (* sort out *)

  Lemma decompose {M N A} (x : t M N A) :
    x = (rho x \/ mu x >>= fun m => interact m >>= delta x m)%beh.
  Proof.
    apply antisymmetry.
    - intros t Ht. simpl.
      destruct t; eauto 20.
      + right. exists (val m). intuition eauto.
        constructor. simpl. eauto.
      + right. exists (val m). intuition eauto using closed.
        constructor. simpl. eauto.
        exists (tcons m n (val n)). intuition eauto.
    - repeat apply join_lub.
      + apply rho_decr.
      + intros t (s & [(m & Hm & Hs) | H] & Hst); subst; eauto using closed.
        inversion Hst; clear Hst; subst. simpl in H0.
        destruct H0 as (? & [? | (? & ?)] & Hst); subst.
        * inversion Hst; auto.
        * inversion Hst; clear Hst; subst.
          inversion H3; clear H3; subst.
          simpl in H0. auto.
  Qed.

  (** ** Components of various constructions *)

  (** [ret] *)

  Lemma phi_ret {M N P Q A B} (v : A) :
    @phi M N P Q A B (ret v) = bot.
  Proof.
    apply antisymmetry; red; cbn; firstorder congruence.
  Qed.

  Lemma nu_ret {M N P Q A} (v : A) :
    @nu M N P Q A (ret v) = ret v.
  Proof.
    apply antisymmetry; try firstorder congruence.
    red; cbn; eauto.
  Qed.

  Lemma rho_ret {M N P Q A} (v : A) :
    @rho M N P Q A (ret v) = ret v.
  Proof.
    apply antisymmetry; red; cbn; firstorder (subst; eauto; try congruence).
  Qed.

  Lemma mu_ret {M N P Q A} (v : A) :
    @mu M N P Q A (ret v) = bot.
  Proof.
    apply antisymmetry; red; cbn; firstorder congruence.
  Qed.

  Lemma delta_ret {M N A} (v : A) (m : M) (n : N) :
    delta (ret v) m n = bot.
  Proof.
    apply antisymmetry; firstorder congruence.
  Qed.

  Hint Rewrite @phi_ret @nu_ret @rho_ret @mu_ret @delta_ret : monad.

  (** [bind] *)

  Hint Extern 1 (has _ _) => progress cbn.

  Lemma phi_bind {M N P Q A B C} (x : t M N A) (f : A -> t M N B) :
    @phi M N P Q B C (x >>= f) = nu x >>= fun a => phi (f a).
  Proof.
    apply antisymmetry.
    - intro t. firstorder subst. inversion H0; clear H0; subst; eauto 20.
    - intro t. firstorder subst; eauto 20. inversion H0; clear H0; subst; eauto.
  Qed.

  Lemma nu_bind {M N P Q A B} (x : t M N A) (f : A -> t M N B) :
    nu (P:=P) (Q:=Q) (x >>= f) = nu x >>= fun a => nu (f a).
  Proof.
    apply antisymmetry.
    - intros t Ht. cbn in *.
      destruct Ht as [(v & (s & Hs & Hsv) & Ht) | (s & Hs & Hsv)]; subst;
      inversion Hsv; clear Hsv; subst; eauto 20.
    - intros t (s & [(v & Hv & Hsv) | H] & Hst); subst; cbn; eauto.
      inversion Hst; clear Hst; subst; cbn in *. firstorder.
  Qed.

  Lemma rho_bind {M N P Q A B} (x : t M N A) (f : A -> t M N B) :
    rho (P:=P) (Q:=Q) (x >>= f) = rho x >>= fun a => rho (f a).
  Proof.
    apply antisymmetry.
    - intros t Ht. cbn in *.
      destruct Ht as [(v & (s & Hs & Hsv) & Ht) |
                      [[(s & Hs & Hsv) Ht] | (s & Hs & Hsv)]]; subst;
      inversion Hsv; clear Hsv; subst; eauto 20.
    - intros t (s & [(v & Hv & Hsv) | [[H Ht] | H]] & Hst); subst; cbn; eauto;
      inversion Hst; clear Hst; subst; cbn in *; firstorder.
  Qed.

  Lemma mu_bind {M N P Q A B} (x : t M N A) (f : A -> t M N B) :
    mu (P:=P) (Q:=Q) (x >>= f) =
    join (mu x) (nu x >>= fun a => mu (f a)).
  Proof.
    apply antisymmetry.
    - intros t [(m & (s & Hs & Hst) & Ht) | (s & Hs & Hst)]; subst;
      inversion Hst; clear Hst; subst; eauto 20.
    - apply join_lub.
      + intros t [(m & Hm & Ht) | H]; subst; cbn; eauto 10.
      + intros t (s & [(v & Hv & Ht) | H] & Hst); subst; eauto 10.
        inversion Hst; clear Hst; subst. firstorder.
  Qed.

  Lemma delta_bind {M N A B} (x : t M N A) (f : A -> t M N B) m n :
    delta (x >>= f) m n =
    join (delta x m n >>= f) (nu x >>= fun a => delta (f a) m n).
  Proof.
    apply antisymmetry.
    - intros t (s & Hs & Hst).
      destruct s; inversion Hst; clear Hst; subst; cbn; eauto 10.
    - intros t [(s & Hs & Hst) | (s & Hs & Hst)]; cbn in *; firstorder.
      subst. inversion Hst; clear Hst; subst. cbn in *. eauto.
  Qed.

  Hint Rewrite @phi_bind @nu_bind @rho_bind @mu_bind @delta_bind : monad.

  (** [interact] *)

  Lemma phi_interact {M N P Q A} m :
    @phi M N P Q N A (interact m) = bot.
  Proof.
    apply antisymmetry; firstorder congruence.
  Qed.

  Lemma nu_interact {M N P Q} m :
    @nu M N P Q N (interact m) = bot.
  Proof.
    apply antisymmetry; firstorder congruence.
  Qed.

  Lemma rho_interact {M N P Q} m :
    @rho M N P Q N (interact m) = bot.
  Proof.
    apply antisymmetry; firstorder congruence.
  Qed.

  Lemma mu_interact {M N P Q} m :
    @mu M N P Q N (interact m) = ret m.
  Proof.
    apply antisymmetry; try firstorder congruence.
    intros _ [ ]. eauto 10.
  Qed.

  Lemma delta_interact {M N} (m m' : M) (n : N) :
    delta (interact m) m' n = guard (m = m') >>= fun _ => ret n.
  Proof.
    apply antisymmetry.
    - intros t [Htm | (n' & Htmn)].
      + congruence.
      + inversion Htmn; clear Htmn; subst. eauto 10.
    - intros t (s & [Hm Hs] & Hst). subst.
      inversion Hst; clear Hst; subst.
      destruct H0. eauto.
  Qed.

  Hint Rewrite
    @phi_interact
    @nu_interact
    @rho_interact
    @mu_interact
    @delta_interact
    : monad.

  (** [join] *)

  Lemma phi_join {M N P Q A B} (x y : t M N A) :
    @phi M N P Q A B (join x y) = join (phi x) (phi y).
  Proof.
    apply antisymmetry; firstorder.
  Qed.

  Lemma nu_join {M N P Q A} (x y : t M N A) :
    @nu M N P Q A (join x y) = join (nu x) (nu y).
  Proof.
    apply antisymmetry; firstorder.
  Qed.

  Lemma rho_join {M N P Q A} (x y : t M N A) :
    @rho M N P Q A (join x y) = join (rho x) (rho y).
  Proof.
    apply antisymmetry; firstorder.
  Qed.

  Lemma mu_join {M N P Q A} (x y : t M N A) :
    @mu M N P Q A (join x y) = join (mu x) (mu y).
  Proof.
    apply antisymmetry; firstorder.
  Qed.

  Lemma delta_join {M N A} (x y : t M N A) m n :
    @delta M N A (join x y) m n = join (delta x m n) (delta y m n).
  Proof.
    apply antisymmetry; firstorder.
  Qed.

  Hint Rewrite @phi_join @nu_join @rho_join @mu_join @delta_join : monad.

  (** [meet] *)

  Lemma phi_meet {M N P Q A B} (x y : t M N A) :
    @phi M N P Q A B (meet x y) = meet (phi x) (phi y).
  Proof.
    apply antisymmetry; firstorder.
  Qed.

  Lemma nu_meet {M N P Q A} (x y : t M N A) :
    @nu M N P Q A (meet x y) = meet (nu x) (nu y).
  Proof.
    apply antisymmetry; firstorder subst; try congruence; eauto 10 using closed.
  Qed.

  Lemma rho_meet {M N P Q A} (x y : t M N A) :
    @rho M N P Q A (meet x y) = meet (rho x) (rho y).
  Proof.
    apply antisymmetry; firstorder subst; try congruence; eauto 10 using closed.
  Qed.

  Lemma mu_meet {M N P Q A} (x y : t M N A) :
    @mu M N P Q A (meet x y) = meet (mu x) (mu y).
  Proof.
    apply antisymmetry; firstorder subst; try congruence; eauto using closed.
  Qed.

  Lemma delta_meet {M N A} (x y : t M N A) m n :
    @delta M N A (meet x y) m n = meet (delta x m n) (delta y m n).
  Proof.
    apply antisymmetry; firstorder.
  Qed.

  Hint Rewrite @phi_meet @nu_meet @rho_meet @mu_meet @delta_meet : monad.

  (** [bot] *)

  Lemma phi_bot {M N P Q A B} :
    @phi M N P Q A B bot = bot.
  Proof.
    apply antisymmetry; firstorder.
  Qed.

  Lemma nu_bot {M N P Q A} :
    @nu M N P Q A bot = bot.
  Proof.
    apply antisymmetry; firstorder.
  Qed.

  Lemma rho_bot {M N P Q A} :
    @rho M N P Q A bot = bot.
  Proof.
    apply antisymmetry; firstorder.
  Qed.

  Lemma mu_bot {M N P Q A} :
    @mu M N P Q A bot = bot.
  Proof.
    apply antisymmetry; firstorder.
  Qed.

  Lemma delta_bot {M N A} m n :
    @delta M N A bot m n = bot.
  Proof.
    apply antisymmetry; firstorder.
  Qed.

  Hint Rewrite @phi_bot @nu_bot @rho_bot @mu_bot @delta_bot : monad.

  (** [top] *)

  Lemma phi_top {M N P Q A B} :
    @phi M N P Q A B top = top.
  Proof.
    apply antisymmetry; firstorder.
  Qed.

  Lemma nu_top {M N P Q A} :
    @nu M N P Q A top = top.
  Proof.
    apply antisymmetry; firstorder.
  Qed.

  Lemma rho_top {M N P Q A} :
    @rho M N P Q A top = top.
  Proof.
    apply antisymmetry; firstorder.
  Qed.

  Lemma mu_top {M N P Q A} :
    @mu M N P Q A top = top.
  Proof.
    apply antisymmetry; firstorder.
  Qed.

  Lemma delta_top {M N A} m n :
    @delta M N A top m n = top.
  Proof.
    apply antisymmetry; firstorder.
  Qed.

  Hint Rewrite @phi_top @nu_top @rho_top @mu_top @delta_top : monad.

  (** [sup] *)

  Lemma phi_sup {M N P Q A B I} (x : I -> t M N A) :
    @phi M N P Q A B (sup x) = sup (fun i => phi (x i)).
  Proof.
    apply antisymmetry; firstorder.
  Qed.

  Lemma nu_sup {M N P Q A I} (x : I -> t M N A) :
    @nu M N P Q A (sup x) = sup (fun i => nu (x i)).
  Proof.
    apply antisymmetry; firstorder.
  Qed.

  Lemma rho_sup {M N P Q A I} (x : I -> t M N A) :
    @rho M N P Q A (sup x) = sup (fun i => rho (x i)).
  Proof.
    apply antisymmetry; firstorder.
  Qed.

  Lemma mu_sup {M N P Q A I} (x : I -> t M N A) :
    @mu M N P Q A (sup x) = sup (fun i => mu (x i)).
  Proof.
    apply antisymmetry; firstorder.
  Qed.

  Lemma delta_sup {M N A I} (x : I -> t M N A) m n :
    @delta M N A (sup x) m n = sup (fun i => delta (x i) m n).
  Proof.
    apply antisymmetry; firstorder.
  Qed.

  Hint Rewrite @phi_sup @nu_sup @rho_sup @mu_sup @delta_sup : monad.

  (** [phi] *)

  Lemma phi_phi {M N P Q R S A B C} (x : t M N A) :
    @phi P Q R S B C (@phi M N P Q A B x) = phi x.
  Proof.
    apply antisymmetry; firstorder congruence.
  Qed.

  Lemma nu_phi {M N P Q R S A B} (x : t M N A) :
    @nu P Q R S B (@phi M N P Q A B x) = phi x.
  Proof.
    apply antisymmetry; firstorder congruence.
  Qed.

  Lemma rho_phi {M N P Q R S A B} (x : t M N A) :
    @rho P Q R S B (@phi M N P Q A B x) = phi x.
  Proof.
    apply antisymmetry; firstorder congruence.
  Qed.

  Lemma mu_phi {M N P Q R S A B} (x : t M N A) :
    @mu P Q R S B (@phi M N P Q A B x) = phi x.
  Proof.
    apply antisymmetry; firstorder congruence.
  Qed.

  Lemma delta_phi {M N P Q A B} (x : t M N A) m n :
    delta (@phi M N P Q A B x) m n = phi x.
  Proof.
    apply antisymmetry; firstorder congruence.
  Qed.

  Hint Rewrite @phi_phi @nu_phi @rho_phi @mu_phi @delta_phi : monad.

  (** [nu] *)

  Lemma phi_nu {M N P Q R S A B} (x : t M N A) :
    @phi P Q R S A B (@nu M N P Q A x) = phi x.
  Proof.
    apply antisymmetry; firstorder congruence.
  Qed.

  Lemma nu_nu {M N P Q R S A} (x : t M N A) :
    @nu P Q R S A (@nu M N P Q A x) = @nu M N R S A x.
  Proof.
    apply antisymmetry; firstorder congruence.
  Qed.

  Lemma rho_nu {M N P Q R S A} (x : t M N A) :
    @rho P Q R S A (@nu M N P Q A x) = @nu M N R S A x.
  Proof.
    apply antisymmetry; firstorder congruence.
  Qed.

  Lemma mu_nu {M N P Q R S A} (x : t M N A) :
    @mu P Q R S A (@nu M N P Q A x) = phi x.
  Proof.
    apply antisymmetry; firstorder congruence.
  Qed.

  Lemma delta_nu {M N P Q A} (x : t M N A) m n :
    delta (@nu M N P Q A x) m n = phi x.
  Proof.
    apply antisymmetry; firstorder congruence.
  Qed.

  Hint Rewrite @phi_nu @nu_nu @rho_nu @mu_nu @delta_nu : monad.

  (** [rho] *)

  Lemma phi_rho {M N P Q R S A B} (x : t M N A) :
    @phi P Q R S A B (@rho M N P Q A x) = phi x.
  Proof.
    apply antisymmetry; firstorder congruence.
  Qed.

  Lemma nu_rho {M N P Q R S A} (x : t M N A) :
    @nu P Q R S A (@rho M N P Q A x) = @nu M N R S A x.
  Proof.
    apply antisymmetry; firstorder congruence.
  Qed.

  Lemma rho_rho {M N P Q R S A} (x : t M N A) :
    @rho P Q R S A (@rho M N P Q A x) = @rho M N R S A x.
  Proof.
    apply antisymmetry; firstorder congruence.
  Qed.

  Lemma mu_rho {M N P Q R S A} (x : t M N A) :
    @mu P Q R S A (@rho M N P Q A x) = phi x.
  Proof.
    apply antisymmetry; firstorder congruence.
  Qed.

  Lemma delta_rho {M N P Q A} (x : t M N A) m n :
    delta (@rho M N P Q A x) m n = phi x.
  Proof.
    apply antisymmetry; firstorder congruence.
  Qed.

  Hint Rewrite @phi_rho @nu_rho @rho_rho @mu_rho @delta_rho : monad.

  (** [mu] *)

  Lemma phi_mu {M N P Q R S A} (x : t M N A) :
    @phi P Q R S M A (@mu M N P Q A x) = phi x.
  Proof.
    apply antisymmetry; firstorder congruence.
  Qed.

  Lemma nu_mu {M N P Q R S A} (x : t M N A) :
    @nu P Q R S M (@mu M N P Q A x) = mu x.
  Proof.
    apply antisymmetry; firstorder congruence.
  Qed.

  Lemma rho_mu {M N P Q R S A} (x : t M N A) :
    @rho P Q R S M (@mu M N P Q A x) = mu x.
  Proof.
    apply antisymmetry; firstorder congruence.
  Qed.

  Lemma mu_mu {M N P Q R S A} (x : t M N A) :
    @mu P Q R S M (@mu M N P Q A x) = phi x.
  Proof.
    apply antisymmetry; firstorder congruence.
  Qed.

  Lemma delta_mu {M N P Q A} x m n :
    delta (@mu M N P Q A x) m n = phi x.
  Proof.
    apply antisymmetry; firstorder congruence.
  Qed.

  Hint Rewrite @phi_mu @nu_mu @rho_mu @mu_mu @delta_mu : monad.

  (** Bind and bot *)

  Lemma bind_phi {M N P Q A B C} (x : t M N A) (f : B -> t P Q C) :
    (phi x >>= f) = phi x.
  Proof.
    apply antisymmetry; intro; firstorder. eauto 10.
  Qed.

  Lemma bind_nu_bot {M N P Q A B} (x : t M N A) :
    (nu x >>= fun _ => @bot P Q B) = phi x.
  Proof.
    apply antisymmetry; intro; firstorder subst.
    - inversion H0; contradiction.
    - cbn in *. eauto.
  Qed.

  Lemma bind_mu_bot {M N P Q A B} (x : t M N A) :
    (mu x >>= fun _ => @bot P Q B) = phi x.
  Proof.
    apply antisymmetry; intro; firstorder subst.
    - inversion H0; contradiction.
    - cbn in *. eauto.
  Qed.

  Hint Rewrite @bind_phi @bind_nu_bot @bind_mu_bot : monad.


  (** * Trace-based decomposition *)

  (** ** Definition *)

  Program Definition pref {M N A} (t : trace M N A) :=
    {|
      has s := prefix s t;
    |}.
  Next Obligation.
    intros. rauto.
  Qed.

  Lemma pref_decomp {M N A} (x : t M N A) :
    x = sup (fun t => pref (proj1_sig (P := has x) t)).
  Proof.
    apply antisymmetry.
    - intros t Ht. exists (exist _ t Ht). cbn. reflexivity.
    - intros t [[s Hs] Hst]. cbn in *. eauto using closed.
  Qed.

  (** ** Equational properties *)

  Lemma pref_val {M N A} (a : A) :
    @pref M N A (val a) = ret a.
  Proof.
    apply antisymmetry; intros t Ht; cbn in *; inversion Ht; reflexivity.
  Qed.

  Lemma pref_div {M N A} :
    @pref M N A div = diverge.
  Proof.
    apply antisymmetry; intros t Ht; cbn in *; inversion Ht; reflexivity.
  Qed.

  Lemma pref_undef {M N A} :
    @pref M N A undef = top.
  Proof.
    apply antisymmetry; intros t Ht; cbn in *; inversion Ht; auto.
  Qed.

  Lemma pref_move {M N A} (m : M) :
    @pref M N A (move m) = interact m >>= fun _ => bot.
  Proof.
    apply antisymmetry; intros t Ht; cbn in *; firstorder.
    - inversion Ht; clear Ht; subst. eauto 10.
    - subst. inversion H0; clear H0; subst. auto.
    - subst. inversion H0; clear H0; subst. inversion H4. contradiction.
  Qed.

  Lemma pref_tcons {M N A} (m : M) (n : N) (t : trace M N A) :
    @pref M N A (tcons m n t) =
    interact m >>= fun n' => guard (n = n') >>= fun _ => pref t.
  Proof.
    apply antisymmetry.
  Admitted.

  Hint Rewrite @pref_val @pref_div @pref_undef @pref_move @pref_tcons : monad.

  (** ** Induction *)

  (** Based on the decomposition above, we can introduce the following
    reasoning principle. *)

  Lemma sup_empty {M N A} (f : Empty_set -> t M N A) :
    sup f = bot.
  Proof.
    apply antisymmetry; monad.
    apply sup_lub; intros [ ].
  Qed.

  Lemma delta_diverge {M N A} m n :
    @delta M N A diverge m n = bot.
  Proof.
    apply antisymmetry; monad.
    discriminate.
  Qed.

  Hint Rewrite @delta_diverge : monad.

  Lemma ind_sup {M N A} (P : t M N A -> Prop) :
    (forall I (f : I -> t M N A), (forall i, P (f i)) -> P (sup f)) ->
    P top ->
    (forall x, (forall m n, P (delta x m n)) -> P x) ->
    (forall x, P x).
  Proof.
    intros Hsup Htop Hstep x.
    assert (Hbot : P bot) by (rewrite <- (sup_empty (fun _ => top)); auto).
    rewrite (pref_decomp x). apply Hsup.
    intros [t Ht]. cbn.
    revert x Ht. induction t; intros; apply Hstep; intros; monad.
    - destruct (classic (m = m0)); monad.
    - destruct (classic (m = m0)); monad.
      destruct (classic (n = n0)); monad.
      eapply (IHt (delta x m n)). cbn. auto.
  Qed.

End Intm.

(*
Global Instance subrel_subrelation {A} (R R' : relation A) :
  RAuto (subrel R R') -> subrelation R R'.
Proof.
  firstorder.
Qed.
*)
