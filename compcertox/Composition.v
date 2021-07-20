Require Import Relations RelationClasses Relators.
Require Import List.
Require Import Coqlib.
Require Import LanguageInterface_ Events Globalenvs Smallstep_ CategoricalComp.
Require Import Memory Values.
Require Import Clight_ Linking.
Require Import AbstractStateRel Lifting.
Require Import Maps.

Set Implicit Arguments.
Set Asymmetric Patterns.

Inductive rel_adt: Type -> Type -> Type :=
| empty_rel K: rel_adt K K
| singleton_rel {K1 K2} : krel K1 K2 -> rel_adt K1 K2
| vcomp_rel {K1 K2 K3} : rel_adt K1 K2 -> rel_adt K2 K3 -> rel_adt K1 K3.

(* Why asymmetric patterns flag doesn't work? *)
Fixpoint absrel_to_cc {K1 K2} (rel: rel_adt K1 K2):
  callconv (li_c @ K1) (li_c @ K2) :=
  match rel with
  | empty_rel _ => cc_id
  | singleton_rel _ _ r => kcc_c r
  | vcomp_rel _ _ _ r1 r2 => (absrel_to_cc r1) @ (absrel_to_cc r2)
  end.

Delimit Scope krel_scope with krel.
Bind Scope krel_scope with rel_adt.

Notation "[ R ]" := (singleton_rel R) (at level 30): krel_scope.
Notation "R1 ∘ R2" := (vcomp_rel R1 R2): krel_scope.

Coercion absrel_to_cc : rel_adt >-> callconv.

(* A module is a list of compilation units. Specifically, they are Clight
   programs at this time. Note that in the layer library the modules are
   organized as mapping from identifiers to vars or functions. A module like
   that is transformed into a Clight program by [make_program] because separate
   compilation is not supported. However, here a module is nothing but a list of
   programs and the semantics is given by the horizontal composition of the
   Clight programs *)
Definition cmodule := list Clight_.program.

Fixpoint semantics (cmod: cmodule) sk: semantics li_c li_c :=
  match cmod with
  | nil => id_semantics sk
  | (p :: ps) =>
    let L b := match b with
               | true =>  semantics ps sk
               | false => Clight_.semantics1 p
               end
    in SmallstepLinking_.semantics L sk
  end.

Definition cmod_combine := app.
Notation " M ⊕ N " := (cmod_combine M N) (left associativity, at level 50).

Definition layer_comp {K} (M: cmodule) (L: layer K) sk :=
  comp_semantics' (semantics M sk @ K) L sk.

Definition ksim {K1 K2: Type} (L1: layer K1) (L2: layer K2)
           (M: cmodule) (R: rel_adt K1 K2) :=
  forward_simulation 1 R L1 (layer_comp M L2 (skel L1)).

Section VCOMP.

  Context {K1 K2 K3 L1 L2 L3} {M N: cmodule}
          {R: rel_adt K1 K2} {S: rel_adt K2 K3}
          (HL1: ksim L1 L2 M R) (HL2: ksim L2 L3 N S).

  Theorem layer_vcomp: ksim L1 L3 (M ⊕ N) (R ∘ S).
  Proof.
  Admitted.

End VCOMP.
