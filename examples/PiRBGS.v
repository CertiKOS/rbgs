Require Import models.Pi.Semantics.

(** Compatibility shim: re-export the RBGS-flavoured π semantics from
    [models/Pi/Semantics.v]. *)
Module PiRBGS := PiSemantics.
Export PiSemantics.
