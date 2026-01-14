Require Import models.EffectSignatures.
Require Import LinCCAL.

Module LTSSpec.
  Import Reg.
  Import LinCCALBase.

  Section LTSDefinition.
    (* signature *)
    Context {E : Op.t}.
    
    Variant Event : Type :=
    | InvEv (op : Sig.op E)
    | ResEv (op : Sig.op E) (ret : Sig.ar op).

    Record ThreadEvent : Type := {
      te_tid : tid;
      te_ev : Event
    }.

    Record LTS : Type := {
      State : Type;
      Step : ThreadEvent -> State -> State -> Prop;
      Error : ThreadEvent -> State -> Prop
    }.

    (*
    Record LTS : Type := {
      State : Type;
      bot : State;
      Step : ThreadEvent -> State -> State -> Prop;
    }.
    *)

    Definition NoError {State} : ThreadEvent -> State -> Prop := fun _ _ => False.
  End LTSDefinition.

  
  Definition tens_lts {E1 E2} (lts1 : @LTS E1) (lts2 : @LTS E2) : @LTS (Sig.Plus.omap E1 E2) :=
    {|
        State := lts1.(State) * lts2.(State);
        Step := fun (te : @ThreadEvent (Sig.Plus.omap E1 E2)) '(s1, s2) '(s1', s2') =>
          match te.(te_ev) with
          | InvEv op => match op with
            | inl op => lts1.(Step) (Build_ThreadEvent te.(te_tid) (InvEv op)) s1 s1' /\ s2 = s2'
            | inr op => lts2.(Step) (Build_ThreadEvent te.(te_tid) (InvEv op)) s2 s2' /\ s1 = s1'
            end
          | ResEv op ret => match op, ret with
            | inl op, ret => lts1.(Step) (Build_ThreadEvent te.(te_tid) (ResEv op ret)) s1 s1' /\ s2 = s2'
            | inr op, ret => lts2.(Step) (Build_ThreadEvent te.(te_tid) (ResEv op ret)) s2 s2' /\ s1 = s1'
            end
          end;
          Error := fun (te : @ThreadEvent (Sig.Plus.omap E1 E2)) '(s1, s2) =>
            match te.(te_ev) with
            | InvEv op => match op with
              | inl op => lts1.(Error) (Build_ThreadEvent te.(te_tid) (InvEv op)) s1
              | inr op => lts2.(Error) (Build_ThreadEvent te.(te_tid) (InvEv op)) s2
              end
            | ResEv op ret => match op, ret with
              | inl op, ret => lts1.(Error) (Build_ThreadEvent te.(te_tid) (ResEv op ret)) s1
              | inr op, ret => lts2.(Error) (Build_ThreadEvent te.(te_tid) (ResEv op ret)) s2
              end
            end;
    |}.
  

  (* TODO: instantiate Jeremie's lts as LTS *)

  Ltac inversion_thread_event_eq :=
  match goal with
  | H : ?e1 = ?e2 |- _ =>
      let T := type of e1 in
      match T with
      | @ThreadEvent _ => inversion H; subst
      end
  end.
End LTSSpec.
