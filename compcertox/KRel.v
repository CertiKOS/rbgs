From Coq Require Import
     Relations RelationClasses List.
From compcertox Require Import
     Lifting AbstractStateRel.
From compcert.lib Require Import
     Coqlib.
From compcert.common Require Import
     LanguageInterface Events
     Globalenvs Smallstep
     Linking Memory Values.
From compcert.cklr Require Import
     CKLR Extends Clightrel.
From compcert.cfrontend Require Import
     SimplLocalsproof Clight.

Definition blocks (se: Genv.symtbl) (names: ident -> Prop) : block -> Z -> Prop :=
  fun b ofs => exists v, names v /\ Genv.find_symbol se v = Some b.

(** The relation Rr is parametrized by the symbol table so that we do not have
    to bind the variables being abstracted to particular blocks *)
Record krel {K1 K2: Type}: Type :=
  mk_krel {
      krel_rel (se: Genv.symtbl):> K2 -> mem * K1 -> Prop;
      (** the names of the static variables being abstracted *)
      vars : ident -> Prop;
      (** other variables *)
      others := fun i => ~ vars i;

      (** the abstraction relation is not affected by other variables *)
      G_unchanged: forall se k1 k2 m m',
        krel_rel se k2 (m, k1) -> Mem.unchanged_on (blocks se vars) m m' -> krel_rel se k2 (m', k1);
      (** the abstraction relation only focuses on valid blocks, i.e. those have
          been allocated *)
      G_valid: forall se k1 k2 m b ofs,
        krel_rel se k2 (m, k1) -> (blocks se vars) b ofs -> Mem.valid_block m b;
    }.
Arguments krel: clear implicits.

Section KREL_KCC.

  Context {K1 K2} (R: krel K2 K1).
  Context (se: Genv.symtbl).

  Inductive krel_kcc_query: query (li_c @ K1) -> query (li_c @ K2) -> Prop :=
    krel_kcc_query_intro vf1 vf2 sg vargs1 vargs2 m1 m2 k1 k2:
      Val.inject inject_id vf1 vf2 -> Val.inject_list inject_id vargs1 vargs2 ->
      Mem.extends m1 m2 -> vf1 <> Vundef -> no_perm_on m1 (blocks se (vars R)) ->
      krel_rel R se k1 (m2, k2) ->
      krel_kcc_query (cq vf1 sg vargs1 m1, k1) (cq vf2 sg vargs2 m2, k2).
  Inductive krel_kcc_reply: reply (li_c @ K1) -> reply (li_c @ K2) -> Prop :=
    krel_kcc_reply_intro vres1 m1 vres2 m2 k1 k2:
      Val.inject inject_id vres1 vres2 ->
      Mem.extends m1 m2 -> no_perm_on m1 (blocks se (vars R)) ->
      krel_rel R se k1 (m2, k2) ->
      krel_kcc_reply (cr vres1 m1, k1) (cr vres2 m2, k2).

  (* Instance symtbl_kf: KripkeFrame unit Genv.symtbl := *)
  (*   {| acc _ := eq; |}. *)

  Program Definition krel_kcc: callconv (li_c @ K1) (li_c @ K2) :=
    {|
      ccworld := unit;
      match_senv _ := eq;
      match_query _ := krel_kcc_query;
      match_reply _ := krel_kcc_reply;
    |}.
  Next Obligation.
    inv H0. cbn. apply val_inject_id in H4. inv H4; easy.
  Qed.
  Next Obligation.
    inv H. cbn. apply val_inject_id in H4. inv H4; easy.
  Qed.

End KREL_KCC.

Ltac unchanged_implies_solve:=
  eapply Mem.unchanged_on_implies; [eauto | intros b ofs [v [? ?]]; eexists; eauto].

Section COMP.

  (* TODO: Do we need the assumption that R and S do not overlap *)
  Context {K1 K2 K3} (R: krel K1 K2) (S: krel K2 K3).

  Local Obligation Tactic := cbn.
  (* TODO: Promoting to callconv preserves composition *)
  Program Definition krel_comp: krel K1 K3 :=
    {|
      krel_rel se :=
        fun k3 '(m1, k1) => exists k2, S se k3 (m1, k2) /\ R se k2 (m1, k1);
      vars i := vars S i \/ vars R i;
    |}.
  Next Obligation.
    intros se k1 k3 m1 m1' (k2 & HS & HR) H.
    eexists k2. split.
    - eapply G_unchanged; eauto.
      unchanged_implies_solve.
    - eapply G_unchanged; eauto.
      unchanged_implies_solve.
  Qed.
  Next Obligation.
    intros se k1 k3 * (k2 & HS & HR) Hb.
    unfold blocks in Hb. destruct Hb as (v & Hv & ?).
    destruct Hv.
    - eapply G_valid. apply HS.
      exists v; split; auto.
    - eapply G_valid. apply HR.
      exists v; split; auto.
      Unshelve. apply ofs. apply ofs.
  Qed.

End COMP.
