Require Import Classical.
Require Import LogicalRelations.
Require Import Quiver.


(** * Bimorphic lenses *)

Module Lens.

  (** ** Objects *)

  (** A bimorphic lens can be understood as a simple game
    consisting of one question and one answer. *)

  Record t :=
    {
      question : Type;
      answer : Type;
    }.

  (** ** Morphisms *)

  (** We will then consider components exhibiting behaviors
    of the shape [†(†A ⊸ B)]. *)

  Module Hom.
    Section HOM.
    Context {A B : t}.

    Variant position :=
      | ready
      | running
      | suspended.

    Inductive move : position -> position -> Type :=
      | oq (m : question B) : move ready running
      | pa (n : answer B) : move running ready
      | pq (q : question A) : move running suspended
      | oa (r : answer A) : move suspended running.

    Record ts :=
      {
        state : position -> Type;
        step {p q} : path move p q -> state p -> state q -> Prop;
        init : state ready;
      }.

    Inductive star f {p} : forall {q}, path move p q -> state f p -> state f q -> Prop :=
      | star_refl (u : state f p) :
          @star f p p [] u u
      | star_step {q r} (s : _ p q) (t : _ q r) (u : state f p) (v : state f q) (w : state f r) :
          step f s u v ->
          @star f q r t v w ->
          @star f p r (s ++ t) u w.

    Lemma star_one f {p q} (m : path move p q) s s' :
      step f m s s' ->
      star f m s s'.
    Proof.
      rewrite <- (papp_pnil_r m) at 2.
      eauto using star_step, star_refl.
    Qed.

    Lemma star_trans f {p q r} (mpq : path move p q) (mqr : path move q r) s s' s'' :
      star f mpq s s' ->
      star f mqr s' s'' ->
      star f (mpq ++ mqr) s s''.
    Proof.
      induction 1; auto. intro.
      rewrite papp_assoc.
      eauto using star_step.
    Qed.

    End HOM.
  End Hom.

  Import Hom.
  Arguments ts : clear implicits.

  (** ** Simulations *)

  Class Sim {A B} (f g : ts A B) (R : forall {p}, rel (state f p) (state g p)) : Prop :=
    {
      sim_step (p q : position) (m : path move p q) :
        Related (step f m) (star g m) (R ++> set_le R);
      sim_init :
        Related (init f) (init g) R;
    }.

  Lemma sim_star `(HR : Sim) p q (m : path move p q) :
    Related (star f m) (star g m) (R p ++> set_le (R q)).
  Proof.
    intros s1 s2 Hs s1' Hs1'.
    revert s2 Hs.
    induction Hs1' as [ | p q r mpq mqr s1 s1' s1'' Hs1' Hs1''] .
    - eauto using star_refl.
    - intros s2 Hs.
      edestruct sim_step as (s2' & Hs2' & Hs'); eauto.
      edestruct (IHHs1'' s2') as (s2'' & Hs2'' & Hs''); eauto.
      eauto using star_trans.
  Qed.

  Definition sim {A B} (f g : ts A B) : Prop :=
    exists R, Sim f g R.

  Instance sim_refl {A B} :
    Reflexive (@sim A B).
  Proof.
    intros f.
    exists (fun _ => eq).
    split.
    - intros p q m s _ [] s' Hs'.
      eauto using star_one.
    - reflexivity.
  Qed.

  Lemma sim_trans {A B} :
    Transitive (@sim A B).
  Proof.
    intros f g h [Rfg Hfg] [Rgh Hgh].
    exists (fun p => rel_compose (Rfg p) (Rgh p)).
    split.
    - intros p q m s1 s3 (s2 & Hs12 & Hs23) s1' Hs1'.
      edestruct (sim_step (R:=Rfg)) as (s2' & Hs2' & Hs12'); eauto 10.
      edestruct (sim_star (R:=Rgh)) as (s3' & Hs3' & Hs23'); eauto 10.
    - exists (init g). split; apply sim_init.
  Qed.

  (** ** Compositional structure *)

  (** *** Identity component *)

  Module Id.
    Section ID.
      Context {A : t}.

      Variant state : position -> Type :=
        | Y : state ready
        | S : state suspended.

      Variant step : forall {p q}, path move p q -> state p -> state q -> Prop :=
        | q (m : question A) : step [oq m, pq m] Y S
        | a (n : answer A)   : step [oa n, pa n] S Y.

    End ID.
  End Id.

  Canonical Structure id (A : t) :=
    {|
      state := Id.state;
      step := @Id.step A;
      init := Id.Y;
    |}.

  (** *** Composition operator *)

  Module Comp.
    Section COMP.
      Context {A B C} {g : ts B C} {f : ts A B}.
      Generalizable All Variables.
      Open Scope path_scope.

      (** First, we give an indexed quiver for the shape of interactions.
        The indices correspond the positions and moves respectively
        observed by the left-hand side component, the right-hand side
        component, and the environment. *)

      Variant ipos : position -> position -> position -> Type :=
        | Y : ipos ready     ready     ready
        | L : ipos running   ready     running
        | R : ipos suspended running   running
        | S : ipos suspended suspended suspended.

      Variant imove :
        forall {pl pr px ql qr qx}, path _ pl ql -> path _ pr qr -> path _ px qx ->
          ipos pl pr px -> ipos ql qr qx -> Type
       :=
        | oq (m : question C) :  imove  [oq m]   []    [oq m]  Y L
        | lq (m : question B) :  imove  [pq m] [oq m]    []    L R
        | rq (m : question A) :  imove    []   [pq m]  [pq m]  R S
        | oa (n : answer A)   :  imove    []   [oa n]  [oa n]  S R
        | ra (n : answer B)   :  imove  [oa n] [pa n]    []    R L
        | la (n : answer C)   :  imove  [pa n]   []    [pa n]  L Y.

      (** The paths within this indexed quiver are as follows. *)

      Inductive itrace :
        forall {pl pr px ql qr qx}, path _ pl ql -> path _ pr qr -> path _ px qx ->
          ipos pl pr px -> ipos ql qr qx -> Type
       :=
        | inil {pl pr px} p :
            @itrace pl pr px pl pr px [] [] [] p p
        | icons {pl pr px ql qr qx rl rr rx p q r ml mr mx sl sr sx} :
            @imove   pl pr px  ql qr qx  ml mr mx  p q ->
            @itrace  ql qr qx  rl rr rx  sl sr sx  q r ->
            itrace (ml ++ sl) (mr ++ sr) (mx ++ sx) p r.

      (** With this combinatorial data encoded as above, defining
        composition becomes extremly straightfoward. A state is simply
        a pair of states of the underlying components with compatible
        positions. Likewise a trajectory is given by a path through
        [imove] which projects out to trajectories of the components
        as well as the externally observable trajectory. *)

      Variant state : Hom.position -> Type :=
        | st {pl pr px} (p : ipos pl pr px) : Hom.state g pl -> Hom.state f pr -> state px.
      
      Variant step {px qx} (mx : path Hom.move px qx) : state px -> state qx -> Prop :=
        | step_intro
            `(m : @itrace pl pr px ql qr qx ml mr mx p q)
            `(Hg : star g ml x x')
            `(Hf : star f mr y y')
          : step mx (st p x y) (st q x' y').

    End COMP.
  End Comp.

  Arguments Comp.state {A B C} g f.

  Definition compose {A B C} (g : ts B C) (f : ts A B) :=
    {|
      state := Comp.state g f;
      step := (@Comp.step _ _ _ g f);
      init := Comp.st Comp.Y (init g) (init f);
    |}.

  (** *** Monotonicity of composition *)

  Ltac xsubst :=
    repeat
      match goal with
      | H : ?x = ?x |- _ =>
        clear H
      | H : existT _ _ _ = existT _ _ _ |- _ =>
        apply inj_pair2 in H
      end;
    subst.

  Module CompSim.
    Section COMPSIM.
      Context {A B C : t}.
      Context {g1 g2 : ts B C} Rg `{Hg : !Sim g1 g2 Rg}.
      Context {f1 f2 : ts A B} Rf `{Hf : !Sim f1 f2 Rf}.

      Variant state_rel px : Comp.state g1 f1 px -> Comp.state g2 f2 px -> Prop :=
        | st_rel {pl pr} (p : Comp.ipos pl pr px) sg1 sg2 sf1 sf2 :
            Rg pl sg1 sg2 ->
            Rf pr sf1 sf2 ->
            state_rel px (Comp.st p sg1 sf1) (Comp.st p sg2 sf2).

      Instance state_sim :
        Sim (compose g1 f1) (compose g2 f2) state_rel.
      Proof.
        split.
        - intros px qx mx s1 s2 Hs.
          destruct Hs as [pl pr p sg1 sg2 sf1 sf2 Hsg Hsf].
          intros s1' Hs1'.
          (* Inverse the step *)
          inversion Hs1' as [xpl xpr ql qr ml mr xp q m xsg1 sg1' Hsg1' xsf1 sf1' Hsf1'].
          clear Hs1'. xsubst.
          (* Use the simulation hypotheses *)
          edestruct (sim_star (R:=Rg)) as (sg2' & Hsg2' & Hsg'); eauto.
          edestruct (sim_star (R:=Rf)) as (sf2' & Hsf2' & Hsf'); eauto.
          exists (Comp.st q sg2' sf2').
          split.
          + apply star_one. econstructor; eauto.
          + constructor; auto.
        - apply (st_rel _ Comp.Y);
          apply sim_init.
      Qed.
    End COMPSIM.
  End CompSim.

  Instance compose_sim :
    Monotonic (@compose) (forallr -, forallr -, forallr -, sim ++> sim ++> sim).
  Proof.
    intros A B C g1 g2 [Rg Hg] f1 f2 [Rf Hf].
    exists (CompSim.state_rel Rg Rf).
    apply CompSim.state_sim; auto.
  Qed.

  (** *** Categorical properties *)

  (** To show that the identity component is a left/right unit for composition,
    we can show that the positions, moves and transitions of [f] expand into
    those of [id ∘ f] and [f ∘ id]. *)

Variant image {A B} (f : A -> B) : rel A B :=
  | image_at (x : A) : image f x (f x).

Variant preimage {A B} (f : A -> B) : rel B A :=
  | preimage_at (x : A) : preimage f (f x) x.

  (** NB : this is where deifning projections for ml, mr, mx
    etc would create a problem because we'd have the non-convertible
    inverse issue *)

  Module CompId.

    (** First, we characterize the traces which can be generated by
      the identity transition system. *)
    Section IDTRACE.
      Context {A : t}.

      Inductive id_trace : forall {p q}, path (@move A A) p q -> Prop :=
        | id_nil {p} :
            @id_trace p p []
        | id_cons_q m {p} (s : path move _ p) :
            id_trace s ->
            id_trace (oq m :: pq m :: s)
        | id_cons_a n {p} (s : path move _ p) :
            id_trace s ->
            id_trace (oa n :: pa n :: s).

      Lemma id_state {p} (s : Id.state p) :
        match p with
          | ready => eq Id.Y
          | running => fun _ => True
          | suspended => eq Id.S
        end s.
      Proof.
        destruct s; auto.
      Qed.

      Lemma id_star_trace {p q} (m : path move p q) s t :
        star (id A) m s t <-> id_trace m.
      Proof.
        split.
        - induction 1.
          + constructor.
          + destruct H; constructor; auto.
        - pose proof (id_state s) as Hs.
          pose proof (id_state t) as Ht.
          induction 1; cbn in *; subst.
          + destruct s; subst; constructor.
          + eapply (star_step _ [oq m, pq m]); eauto.
            constructor.
          + eapply (star_step _ [oa n, pa n]); eauto.
            constructor.
      Qed.
    End IDTRACE.

    Section COMPID.
      Context {A B} {f : ts A B}.
      Open Scope path_scope.

      (** When a position and move is observed for the composite
        transition system, we know that [f] is in that same position,
        and that it performs that same move. We can also reconstruct
        what happens for the copycat component when it appears on the
        left or right. *)

      Definition lpos (p : position) : position :=
        match p with running => suspended | _ => p end.

      Definition ltrace : qmor lpos (@move A B) (path (@move B B)) :=
        fun p q e =>
          match e with
            | oq m => [oq m, pq m]
            | pa n => [oa n, pa n]
            | _ => []
          end.

      Definition rpos (p : position) : position :=
        match p with running => ready | _ => p end.

      Definition rtrace : qmor rpos (@move A B) (path (@move A A)) :=
        fun p q e =>
          match e with
            | pq m => [oq m, pq m]
            | oa n => [oa n, pa n]
            | _ => []
          end.

      (** Then we show that we can reconstruct the interaction
        which gives rise to these projected positions and moves. *)

      Definition lipos (p : position) : Comp.ipos (lpos p) p p :=
        match p with
          | ready => Comp.Y
          | running => Comp.R
          | suspended => Comp.S
        end.

      Definition litr {p q} (t : path move p q) :
        Comp.itrace (pbind ltrace p q t) t t (lipos p) (lipos q).
      Proof.
        induction t as [ | u v w m t IHt]; [constructor | ].
        destruct m; cbn.
        - apply (Comp.icons (Comp.oq m)).
          apply (Comp.icons (Comp.lq m)).
          apply IHt.
        - apply (Comp.icons (Comp.ra n)).
          apply (Comp.icons (Comp.la n)).
          apply IHt.
        - apply (Comp.icons (Comp.rq q)).
          apply IHt.
        - apply (Comp.icons (Comp.oa r)).
          apply IHt.
      Qed.

      Definition ripos (p : position) : Comp.ipos p (rpos p) p :=
        match p with
          | ready => Comp.Y
          | running => Comp.L
          | suspended => Comp.S
        end.

      Definition ritr {p q} (t : path (@move A B) p q) :
        Comp.itrace t (pbind rtrace p q t) t (ripos p) (ripos q).
      Proof.
        induction t as [ | u v w m t IHt]; [constructor | ].
        destruct m; cbn.
        - apply (Comp.icons (Comp.oq m)).
          apply IHt.
        - apply (Comp.icons (Comp.la n)).
          apply IHt.
        - apply (Comp.icons (Comp.lq q)).
          apply (Comp.icons (Comp.rq q)).
          apply IHt.
        - apply (Comp.icons (Comp.oa r)).
          apply (Comp.icons (Comp.ra r)).
          apply IHt.
      Qed.

      (** With this, proving the simulations is straightforward *)

      Definition lstate (p : position) : state (id B) (lpos p) :=
        match p with ready => Id.Y | _ => Id.S end.

      Definition listate {p} (s : state f p) : state (compose (id B) f) p :=
        Comp.st (lipos p) (lstate p) s.

      Instance sim_l_fw :
        Sim f (compose (id B) f) (fun p => image listate).
      Proof.
        split; [ | constructor].
        intros p q t _ _ [s] s' Hs'.
        exists (listate s').
        split; [ | constructor].
        apply star_one.
        apply (Comp.step_intro _ (litr t)); auto using star_one.
        clear.
        induction t; cbn; [constructor | ].
        destruct e; eauto.
        - apply (star_step _ _ _ _ _ _ (Id.q m)); auto.
        - apply (star_step _ _ _ _ _ _ (Id.a n)); auto.
      Qed.

      Definition rstate (p : position) : state (id A) (rpos p) :=
        match p with suspended => Id.S | _ => Id.Y end.

      Definition ristate {p} (s : state f p) : state (compose f (id A)) p :=
        Comp.st (ripos p) s (rstate p).

      Instance sim_r_fw :
        Sim f (compose f (id A)) (fun p => image ristate).
      Proof.
        split; [ | constructor].
        intros p q t _ _ [s] s' Hs'.
        exists (ristate s').
        split; [ | constructor].
        apply star_one.
        apply (Comp.step_intro _ (ritr t)); auto using star_one.
        clear.
        induction t; cbn; [constructor | ].
        destruct e; eauto.
        - apply (star_step _ _ _ _ _ _ (Id.q q)); auto.
        - apply (star_step _ _ _ _ _ _ (Id.a r)); auto.
      Qed.


Lemma foo pl pr ql qr ml mr mx (p : Comp.ipos pl pr pr) (q : Comp.ipos ql qr qr) s s' :
  Comp.itrace ml mr mx p q ->
  id_trace ml ->
  step f mr s s' ->
  step f mx s s'.
Proof.
  intros H. revert s s'.
  induction H.

      Instance sim_bw :
        Sim (compose (id B) f) f (fun p => preimage listate).
      Proof.
        split; cbn; [ | constructor].
        intros px qx tx _ _ [s] xs' Hs'.
        inversion Hs' as [pl pr ql qr ml mr p q t ? i' Hid ? s' Hf]; clear Hs'; xsubst.
        unfold listate; cbn.
        apply id_star_trace in Hid.



        induction Hf.
        - (* base case: if [f] does not take a step, then [id] must
            not have taken a step either, otherwise the observed trace
            of [f] would not be nil. *)
          inversion Hid; clear Hid; xsubst; xsubst.
          + (* no [id] step is indeed what we expect. We have to show
               that the external interaction is empty as well, so that
               we can simply use no step at all in the target. *)
            inversion t; xsubst; xsubst.
            * exists u. split; [constructor | ].
              assert (q = lipos qx).
              { clear -t.
                inversion t; xsubst; auto.
                inversion X; xsubst; xsubst; cbn in *; congruence. }
              subst q.
              constructor.
            * inversion X; xsubst; xsubst; cbn in *; congruence.
          + (* If [id] takes a step, that is a contradiction because
               the interaction seen by [f] could not be empty. *)
            inversion H2; clear H2; xsubst; xsubst.
            * destruct p; cbn in *; try congruence; xsubst.
              inversion t; clear t; xsubst; xsubst.
              inversion X; clear X; xsubst; xsubst; cbn in *; xsubst.
              inversion H7; clear H7; xsubst.
              inversion X0; clear X0; xsubst.
              inversion X; clear X; xsubst; xsubst; cbn in *; try congruence.
            * destruct p; cbn in *; try congruence; xsubst.
              -- inversion t; clear t; xsubst.
                 inversion X; clear X; xsubst; xsubst; cbn in *; congruence.
              -- inversion t; clear t; xsubst.
                 inversion X; clear X; xsubst; xsubst; cbn in *; congruence.
        - (* Inductive step: if [f] does take a step, we just show
             that [id] must have followed along, hence that same step
             in the target will produce the same externally observable
             behavior. To prove this we must proceed by induction on
             the trace generated by the step of [f]. *)
          apply id_star_trace in Hid.
          Set Printing Implicit.

          induction Hid.

          remember (lstate p) as sl eqn:Hsl.
          revert qx tx r q q0 s t0 t Hsl u v w H Hf IHHf.
          induction Hid.
          remember (lpos p) as pl eqn:Hpl.
          induction Hid.

          inversion t; clear t; xsubst; xsubst.
          + (* base case: no more events in the trace *)
            destruct s; cbn in *; try congruence; subst.
            
            exists v. split; auto using star_one.

 congruence.

 inversion q; cbn in *.

              inversion q; xsubst; cbn in *; xsubst.


            assert (qx = p) by (inversion q; xsubst; cbn in *; congruence); subst qx.
            exists u. split.
            * constructor.

            inversion q; xsubst; cbn in *; xsubst.


            destruct p; cbn in *; inversion q; subst; exists u; split.
            constructor.
            * exists u.
exists u.

 inversion t; xsubst; xsubst.
          + inversion Hid.

 cbn in *.

      Abort. (** Will need a complicated induction on the identity steps *)

      (*
        
      (** One difficulty here is that while [epos (xpos p) = p],
        they are not convertible. This complicates the proof below,
        where our goal is to synthesize an interaction trace using [emove]
        which is then flattened back into its external view [xmove]
        by the constructor of [Comp.step], since the type of traces
        depend on the constructions [epos] and [xpos].

        The following lemmas facilitate reasoning around these difficulties. *)

      Lemma xpos_epos p :
        Comp.xpos (epos p) = p.
      Proof.
        destruct p; reflexivity.
      Qed.

      Lemma xmove_emove {u v} (m : path Hom.move u v) :
        qbind Comp.xmove (qbind emove m) ~= m.
      Proof.
        induction m; cbn.
        - destruct u; auto.
        - rewrite qbind_app.
          destruct e, w; cbn in *; apply JMeq_eq in IHm; rewrite IHm; auto.
      Qed.

       *)
    End COMPID.
  End CompId.

  Lemma compose_id_left {A B} (f : ts A B) :
    sim f (compose (id B) f).
  Proof.
    eexists.
    apply CompId.sim_fw.
  Qed.
