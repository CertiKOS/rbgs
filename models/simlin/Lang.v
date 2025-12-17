Require Import models.EffectSignatures.

Module Lang.
  Import SigBase.

  CoInductive Prog {E R} : Type :=
  | Vis (m : op E) (k : ar m -> Prog)
  | Ret (r : R)
  | Tau (p : Prog).
  Arguments Prog : clear implicits.
  Arguments Ret {E R} : rename.
  Arguments Tau {E R} : rename.

  Definition PP {E R} (p : Prog E R) :=
    match p with
    | Vis m k => Vis m k
    | Ret r => Ret r
    | Tau p => Tau p
    end.
  
  Lemma PPid {E R} : forall p : Prog E R, p = PP p.
    intros. destruct p; reflexivity.
  Qed.

  Definition skip {E} := @Ret E unit tt.

  CoFixpoint bindProg {E A B} (p : Prog E A) (k : A -> Prog E B) : Prog E B :=
  match p with
    | Vis e k' => Vis e (fun x => bindProg (k' x) k)
    | Ret a => k a
    | Tau p' => Tau (bindProg p' k)
  end.

  Lemma bindVisUnfold {E A B} : forall e k' (k : A -> Prog E B), bindProg (Vis e k') k = Vis e (fun x => bindProg (k' x) k).
  Proof.
    intros.
    rewrite PPid at 1.
    unfold PP, bindProg. auto.
  Qed.

  Lemma bindRetUnfold {E A B} : forall a (k : A -> Prog E B), bindProg (Ret a) k = k a.
  Proof.
    intros.
    rewrite PPid. rewrite PPid at 1.
    unfold PP, bindProg. auto.
  Qed.

  Lemma bindTauUnfold {E A B} : forall p (k : A -> Prog E B), bindProg (Tau p) k = Tau (bindProg p k).
  Proof.
    intros.
    rewrite PPid at 1.
    unfold PP, bindProg. auto.
  Qed.

  
  Declare Scope prog_scope.
  Bind Scope prog_scope with Prog.
  Delimit Scope prog_scope with Prog.

  Notation "m >= x => p" :=
    (Vis m (fun x => p))
    (at level 70, x binder, right associativity) : prog_scope.
  Notation "p1 ;; x => p2" :=
    (bindProg p1 (fun x => p2))
    (at level 70, x binder, right associativity) : prog_scope.
  Notation "p1 ;; p2" :=
    (bindProg p1 (fun _ => p2))
    (at level 70, right associativity) : prog_scope.

  Section WhileLoop.
    Context {R : Type} (b : R -> bool).
    Context {E} (p : Prog E R).

    CoFixpoint whileAux (p' : Prog E R) : Prog E R :=
      match p' with
      | Vis m k => Vis m (fun x => whileAux (k x))
      | Tau p' => Tau (whileAux p')
      | Ret r => if b r then Tau (whileAux p) else Ret r
      end.

    Lemma whileAuxRetUnfold : forall r, whileAux (Ret r) = if b r then Tau (whileAux p) else Ret r.
    Proof.
      intros.
      rewrite PPid at 1. unfold PP, whileAux at 1.
      destruct (b r) eqn:eq; auto.
    Qed.

    Lemma whileAuxTauUnfold : forall p, whileAux (Tau p) = Tau (whileAux p).
    Proof.
      intros. rewrite PPid at 1. unfold PP, whileAux at 1. auto.
    Qed.

    Lemma whileAuxVisUnfold : forall m k, whileAux (Vis m k) = Vis m (fun x => whileAux (k x)).
    Proof.
      intros. rewrite PPid at 1. unfold PP, whileAux at 1. auto.
    Qed.
    
    Definition doWhile := whileAux p.
    Definition while init := if b init then whileAux p else Ret init.
  End WhileLoop.

  Notation "'Do' '{' p '}' 'While' ( b ) >= x" :=
    (doWhile (fun x => b) p)
    (at level 50, x binder) : prog_scope.
  Notation "'Do' '{' p '}' 'While' ( b ) >= x => k" :=
    (bindProg (doWhile (fun x => b) p) (fun x => k))
    (at level 50, x binder) : prog_scope.
  
  Section SumTypeLoop.
    Context {TT FT : Type}.
    Context {E} (p : Prog E (TT + FT)).

    CoFixpoint loopAux (p' : Prog E (TT + FT)) : Prog E FT :=
      match p' with
      | Vis m k => Vis m (fun x => loopAux (k x))
      | Tau p' => Tau (loopAux p')
      | Ret r =>
                match r with
                | inl _ => Tau (loopAux p)
                | inr v => Ret v
                end
      end.

    Lemma loopAuxRetUnfold : forall r, loopAux (Ret r) = 
                                                        match r with
                                                        | inl _ => Tau (loopAux p)
                                                        | inr v => Ret v
                                                        end.
    Proof.
      intros.
      rewrite PPid at 1. unfold PP, loopAux at 1.
      destruct r eqn:eq; auto.
    Qed.

    Lemma loopAuxTauUnfold : forall p, loopAux (Tau p) = Tau (loopAux p).
    Proof.
      intros. rewrite PPid at 1. unfold PP, loopAux at 1. auto.
    Qed.

    Lemma loopAuxVisUnfold : forall m k, loopAux (Vis m k) = Vis m (fun x => loopAux (k x)).
    Proof.
      intros. rewrite PPid at 1. unfold PP, loopAux at 1. auto.
    Qed.
    
    Definition loop := loopAux p.
  End SumTypeLoop.

  Notation "'Do' '{' p '}' 'Loop'" :=
    (loop p) (at level 50) : prog_scope.
  Notation "'Do' '{' p '}' 'Loop' >= x => k" :=
    (bindProg (loop p) (fun x => k))
    (at level 50, x binder) : prog_scope.
End Lang.


Definition ModuleImpl {E F} := forall m : Sig.op F, Lang.Prog E (Sig.ar m).
Arguments ModuleImpl: clear implicits.
