Require Import Relations RelationClasses Relators.
Require Import List Maps.
Require Import Coqlib.
Require Import CallconvAlgebra_.
Require Import LanguageInterface_ Events Globalenvs Smallstep_ CategoricalComp FlatComp.
Require Import Memory Values.
Require Import Linking.
Require Import Lifting.

Section COMP.
  (* TODO: notation precedence *)
  Context {I} (K: I -> Type)
          {liA liB} (L: forall i, semantics (liA@(K i)) (liB@(K i))).

  Notation Ki := (forall i, K i).

  Hypothesis I_dec: forall (i j: I), {i = j} + {i <> j}.

  Definition update_at (k: Ki) (j: I) (kj: K j): Ki.
  Proof.
    intros i. destruct (I_dec i j).
    - subst. exact kj.
    - exact (k i).
  Defined.

  Section WITH_SE.
    Context (se: Genv.symtbl).

    Variant tensor_state :=
      tensor_st (i: I) (s:  Smallstep_.state (L i)) (k: Ki).

    Inductive tensor_step: tensor_state -> trace -> tensor_state -> Prop :=
    | step_intro i s t s' k:
        Step (L i se) s t s' ->
        tensor_step (tensor_st i s k) t (tensor_st i s' k).

    Inductive tensor_initial_state: query (liB@Ki) -> tensor_state -> Prop :=
    | initial_state_intro i s k q:
        initial_state (L i se) (q, k i) s ->
        tensor_initial_state (q, k) (tensor_st i s k).

    Inductive tensor_at_external: tensor_state -> query (liA@Ki) -> Prop :=
    | at_external_intro i s k q kq k':
        (forall j, i <> j -> k j = k' j) -> k' i = kq ->
        at_external (L i se) s (q, kq) ->
        tensor_at_external (tensor_st i s k) (q, k').

    Inductive tensor_after_external:
      tensor_state -> reply (liA@Ki) -> tensor_state -> Prop :=
    | after_external_intro i s s' k k' r kr:
        (forall j, i <> j -> k j = k' j) -> k' i = kr ->
        after_external (L i se) s (r, kr) s' ->
        tensor_after_external (tensor_st i s k) (r, k') (tensor_st i s' k').

    Inductive tensor_final_state: tensor_state -> reply (liB@Ki) -> Prop :=
    | final_state_intro i s k k' r kr:
        (forall j, i <> j -> k j = k' j) -> k' i = kr ->
        final_state (L i se) s (r, kr) ->
        tensor_final_state (tensor_st i s k) (r, k').

  End WITH_SE.

  Program Definition tensor_semantics' sk: semantics (liA@Ki) (liB@Ki) :=
    {|
      activate se :=
        {|
          step ge := tensor_step se;
          initial_state := tensor_initial_state se;
          at_external := tensor_at_external se;
          after_external := tensor_after_external se;
          final_state := tensor_final_state se;
          globalenv := tt;
        |};
      skel := sk;
      footprint id := exists i, footprint (L i) id;
    |}.

End COMP.

(* This module defines tensor produce specific to layers. This is the same as the general one defined above
   where the outgoing language interface replaced by li_null. Later, we expect
   to find a trick to let Coq identify li_null and li_null@K  *)
Module Tensor.
  (* TODO: notation precedence *)
  Section COMP.
    Context {I} (K: I -> Type)
            {li} (L: forall i, semantics li_null (li@(K i))).

    Notation Ki := (forall i, K i).

    Section WITH_SE.
      Context (se: Genv.symtbl).

      Variant tensor_state :=
        tensor_st (i: I) (s:  Smallstep_.state (L i)) (k: Ki).

      Inductive tensor_step: tensor_state -> trace -> tensor_state -> Prop :=
      | step_intro i s t s' k:
          Step (L i se) s t s' ->
          tensor_step (tensor_st i s k) t (tensor_st i s' k).

      Inductive tensor_initial_state: query (li@Ki) -> tensor_state -> Prop :=
      | initial_state_intro i s k q:
          initial_state (L i se) (q, k i) s ->
          tensor_initial_state (q, k) (tensor_st i s k).

      Inductive tensor_at_external: tensor_state -> query li_null -> Prop := .

      Inductive tensor_after_external:
        tensor_state -> reply li_null -> tensor_state -> Prop := .

      Inductive tensor_final_state: tensor_state -> reply (li@Ki) -> Prop :=
      | final_state_intro i s k k' r kr:
          (forall j, i <> j -> k j = k' j) -> k' i = kr ->
          final_state (L i se) s (r, kr) ->
          tensor_final_state (tensor_st i s k) (r, k').

    End WITH_SE.

    Program Definition tensor_semantics' sk: semantics li_null (li@Ki) :=
      {|
      activate se :=
        {|
          step ge := tensor_step se;
          initial_state := tensor_initial_state se;
          at_external := tensor_at_external;
          after_external := tensor_after_external;
          final_state := tensor_final_state se;
          globalenv := tt;
        |};
      skel := sk;
      footprint id := exists i, footprint (L i) id;
      |}.

  End COMP.
End Tensor.
