Require Import Classical.
Require Import Program.Equality.
Require Import LogicalRelations.
Require Import Poset.
Require Import Lattice.
Require Import Downset.
Require Import IntStrat.
Require Import Classical_Prop.
Require Import Coqlib.
Require Import Determ.

From compcert.common Require Import LanguageInterface Smallstep Globalenvs.
From compcert.process Require Import Process.
Import Memory Values Integers ListNotations.
Require Import CompCertStrat.
Close Scope list.
Close Scope Z_scope.

Definition P : esig := {| op := unit; ar _ := nat |}.
Inductive F_op : Type := F_read : nat -> F_op | F_write : list byte -> F_op.
Definition F : esig :=
  {|
    op := F_op;
    ar m := match m with F_read _ => list byte | F_write _ => nat end;
  |}.
Definition S : esig := F + F.

Arguments compose_when {E F G}%esig_scope {i j k} p (σ τ)%strat_scope.

Definition Γ_play : @play S P ready :=
  @oq S P tt ::
  @pq S P tt (inr (F_write hello_bytes)) ::
  @oa S P tt (inr (F_write hello_bytes)) 5 ::
  @pa S P tt 0 :: pnil_ready.
Definition Γ : S ->> P := down Γ_play.
Definition Γ_secret_play : @play S P ready :=
  @oq S P tt ::
  @pq S P tt (inr (F_write uryyb_bytes)) ::
  @oa S P tt (inr (F_write uryyb_bytes)) 5 ::
  @pa S P tt 0 :: pnil_ready.
Definition Γ_secret : S ->> P := down Γ_secret_play.
Definition Γ_decode_play : @play S P ready :=
  @oq S P tt ::
  @pq S P tt (inl (F_read 100)) ::
  @oa S P tt (inl (F_read 100)) uryyb_bytes ::
  @pq S P tt (inr (F_write hello_bytes)) ::
  @oa S P tt (inr (F_write hello_bytes)) 5 ::
  @pa S P tt 0 :: pnil_ready.
Definition Γ_decode : S ->> P := down Γ_decode_play.
Definition seq_play n1 n2: @play (P + P) P ready :=
  @oq (P+P) P tt ::
  @pq (P+P) P tt (inl tt) ::
  @oa (P+P) P tt (inl tt) n1 ::
  @pq (P+P) P tt (inr tt) ::
  @oa (P+P) P tt (inr tt) n2 ::
  @pa (P+P) P tt n2 :: pnil_ready.
Definition seq : P + P ->> P := sup n1, sup n2, down (seq_play n1 n2).
Inductive fifo_play: list byte -> forall i, @play 0 F i -> Prop :=
| fifo_nil d : fifo_play d ready pnil_ready
| fifo_read n d1 d2 d s
    (Hd: d = app d1 d2) (Hn: n = length d1) (Hs: fifo_play d2 ready s):
  fifo_play d ready (@oq 0 F (F_read n) :: @pa 0 F (F_read n) d1 :: s)
| fifo_read_all n d s (Hn: n > length d) (Hs: fifo_play nil ready s):
  fifo_play d ready (@oq 0 F (F_read n) :: @pa 0 F (F_read n) d :: s)
| fifo_write n d1 d2 d s
    (Hd: d2 = app d d1) (Hn: n = length d1) (Hs: fifo_play d2 ready s):
  fifo_play d ready (@oq 0 F (F_write d1) :: @pa 0 F (F_write d1) n :: s).
Program Definition fifo : 0 ->> F :=
  {|
    Downset.has s := fifo_play nil ready s;
  |}.
Next Obligation.
  cbn.
  generalize (@ready 0 F).
  generalize (nil: list byte).
  intros l p x y Hxy Hy. revert x Hxy.
  dependent induction Hy; intros x Hxy;
    dependent destruction Hxy; try constructor.
  - dependent destruction Hxy; econstructor; eauto.
  - dependent destruction Hxy. eapply fifo_read_all; eauto.
  - dependent destruction Hxy. eapply fifo_write; eauto.
Qed.

Definition pipe (p1 p2: S ->> P) : S ->> P :=
  seq ⊙
  (p1 + p2)%strat ⊙
  α+ ⊙
  (α'+ + id F)%strat ⊙
  (id F + (Δ+ ⊙ fifo) + id F)%strat ⊙
  (ρ'+ + id F)%strat.

Global Hint Constructors comp_has : core.

Lemma ϕ_1 : Γ [= pipe Γ_secret Γ_decode.
Proof.
  intros p Hp. cbn in Hp.
  assert (Downset.has (pipe Γ_secret Γ_decode) Γ_play).
  2: { eauto using Downset.closed. } clear Hp. unfold pipe.
  unfold compose at 1. cbn - [compose].
  eexists _, _. repeat apply conj.
  { exists 0, 0. reflexivity. }
  2: { unfold Γ_play, seq_play.
       apply comp_oq. apply comp_lq. apply comp_ra.
       repeat constructor. }
  Unshelve. 2: refine pnil_ready.
  unfold compose at 1. cbn - [compose].
  eexists _, _. repeat apply conj.
  { eexists _, _. repeat apply conj; try reflexivity.
    apply fcomp_oq_l. repeat constructor. }
  2:{ apply comp_oq.  apply comp_lq.  apply comp_ra.  apply comp_la.
      apply comp_oq.  apply comp_lq.  apply comp_ra.
      repeat constructor. }

  unfold compose at 1. cbn - [compose].
  Unshelve. 2: refine pnil_ready.
  eexists _, _. repeat apply conj.

  (* (F+F) + (F+F) ---> ((F+F)+F) + F *)

  apply falph_question_l. apply falph_answer_l.
  apply falph_question_m. apply falph_answer_m.
  apply falph_question_r. apply falph_answer_r.
  apply falph_ready.

  2: { apply comp_oq. apply comp_lq. apply comp_ra. apply comp_la.
       apply comp_oq. apply comp_lq. apply comp_ra.
       repeat constructor. }

  Unshelve. 2: refine pnil_ready.
  eexists _, _. repeat apply conj.

  (* ((F+F)+F) + F ---> F + (F+F) + F *)

  eexists _, _. repeat apply conj.
  cbn. apply falphr_question_m. apply falphr_answer_m.
  apply falphr_question_r. apply falphr_answer_r. apply falphr_ready.

  cbn. apply id_has_q. apply id_has_a. apply id_has_pnil_ready.

  (* left by default. so this is what we want *)
  repeat constructor.

  2: { repeat constructor. }.

  Unshelve. 2: refine pnil_ready.
  eexists _, _. repeat apply conj.

  (* F + (F+F) + F ---> F + 0 + F *)
  eexists _, _. repeat apply conj.
  2: { cbn. apply id_has_q. apply id_has_a. apply id_has_pnil_ready. }
  eexists _, _. repeat apply conj. apply id_has_pnil_ready.

  eexists _, _. repeat apply conj.
  cbn. apply fdel_question_l. apply fdel_answer_l. apply fdel_question_r. apply fdel_answer_r. apply fdel_ready.
  cbn. eapply fifo_write with (d1 := uryyb_bytes).
  rewrite app_nil_l. reflexivity. cbn. reflexivity.
  eapply fifo_read_all with (n := 100). cbn. lia. apply fifo_nil.

  repeat constructor.
  repeat constructor.
  repeat constructor.
  2: repeat constructor.

  (* F + 0 + F ---> F + F *)

  Unshelve. 2: refine pnil_ready.
  eexists _, _. repeat apply conj.
  cbn. apply frhor_ready.
  cbn. apply id_has_q with (m := F_write hello_bytes).
  apply id_has_a with (n := 5). apply id_has_pnil_ready.

  eapply fcomp_oq_r.
  eapply (fcomp_pq_r (E1 := F) (E2 := F)).
  eapply (fcomp_oa_r (E1 := F) (E2 := F)).
  eapply (fcomp_pa_r (E1 := F) (E2 := F)).
  constructor.
Qed.
