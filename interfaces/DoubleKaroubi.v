Require Import interfaces.Category.
Require Import interfaces.Functor.
Require Import interfaces.DoubleCat.

Module Idempotents (V : CategoryDefinition) (D : DoubleCategory V).
  Import D.
  Import Siso.

  Record idem (a : V.t) :=
    {
      carrier :> hcell a a;
      idempotency : sisocell (carrier ⨀ carrier) carrier;
      idem_coh : (idempotency ⊙ vid carrier) ;; idempotency =
        assoc carrier carrier carrier ;; (vid carrier ⊙ idempotency) ;; idempotency;
    }.

  Program Definition id_idem (a : V.t) :=
    {|
      carrier := hid a;
      idempotency := runit (hid a);
    |}.
  Next Obligation.
    rewrite <- lunit_hid_runit_hid. rewrite <- unit_coh.
    rewrite lunit_hid_runit_hid. reflexivity.
  Defined.

End Idempotents.