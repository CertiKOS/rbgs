(** Some experiments with nominal memory model *)
Require Import Coqlib AST Integers.

(** Block *)
Module Type BLOCK.

Parameter block : Type.
Parameter eq_block : forall (x y: block), {x=y} + {x<>y}.

End BLOCK.

Module Sum_Block (BLK1: BLOCK) (BLK2: BLOCK) <: BLOCK.

  Open Scope type_scope.
  Definition block := BLK1.block + BLK2.block.

  Lemma eq_block : forall (x y: block), {x=y} + {x<>y}.
  Proof.
    decide equality. apply BLK1.eq_block. apply BLK2.eq_block.
  Qed.

End Sum_Block.

Inductive glob_block' := Global' : ident -> glob_block'.
Module Glob_Block <: BLOCK.

  Definition block := glob_block'.

  Lemma eq_block : forall (x y: block), {x=y} + {x<>y}.
  Proof. repeat decide equality. Qed.

End Glob_Block.

Definition path := list nat.
Definition fid := option ident. (*None means external function*)
Inductive stack_block' := Stack' : fid -> path -> positive -> stack_block'.

Module Stack_Block <: BLOCK.

  Definition block := stack_block'.

  Lemma eq_block : forall (x y: block), {x=y} + {x<>y}.
  Proof. repeat decide equality. Qed.

End Stack_Block.

Module Block <: BLOCK := Sum_Block Glob_Block Stack_Block.
Definition block := Block.block.

Notation " 'Global' i " := (inl (Global' i)) (at level 1).
Notation " 'Stack' f p i " := (inr (Stack' f p i)) (at level 1).

Goal block. refine (Global 5%positive). Defined.

(* Support *)
Module Type SUP.

Parameter sup: Type.

Parameter sup_empty : sup.

Parameter sup_In : block -> sup -> Prop.
Parameter empty_in: forall b, ~ sup_In b sup_empty.
Parameter sup_dec : forall b s, {sup_In b s} + {~sup_In b s}.

Parameter fresh_block : sup -> block.
Parameter freshness : forall s, ~ sup_In (fresh_block s) s.

Parameter sup_incr : sup -> sup.

Definition sup_include(s1 s2:sup) := forall b, sup_In b s1 -> sup_In b s2.

Parameter sup_incr_in : forall b s, sup_In b (sup_incr s) <-> b = (fresh_block s) \/ sup_In b s.

Theorem sup_incr_in1 : forall s, sup_In (fresh_block s) (sup_incr s).
Proof. intros. apply sup_incr_in. left. auto. Qed.
Theorem sup_incr_in2 : forall s, sup_include s (sup_incr s).
Proof. intros. intro. intro. apply sup_incr_in. right. auto. Qed.

Lemma sup_include_refl : forall s:sup, sup_include s s.
Proof. intro. intro. auto. Qed.

Lemma sup_include_trans:
  forall p q r:sup, sup_include p q -> sup_include q r -> sup_include p r.
Proof. intros. intro. intro.  auto. Qed.

Lemma sup_include_incr:
  forall s, sup_include s (sup_incr s).
Proof. intros. apply sup_incr_in2. Qed.

End SUP.
