Require Import CatComp.
Require Import Linking.

Definition layer_combine {K} (M: Clight.program) (L: layer K) sk :=
  (* let L' := CatComp.semantics (semantics1 M @ K) (closed_sem_conv L (li_c @ K)) sk *)
  (* in closed_sem_conv L' li_null. *)
  layer_comp (semantics1 M @ K) L sk.
Record prog_ksim {K1 K2: Type} :=
  mk_prog_ksim {
      L1: layer K1;
      L2: layer K2;
      M: Clight.program;
      R: krel K1 K2;
      sk: AST.program unit unit;

      layer_sim: forward_simulation 1 (kcc_ext R) L1 (layer_combine M L2 sk);
      link_sk: link (skel (semantics1 M)) (skel L2) = Some sk;
    }.

Section PROG_SIM.
  Context {K1 K2} (pksim: @prog_ksim K1 K2).
  Program Definition prog_sim_coercion: @Ksim.ksim K1 K2 :=
    {|Ksim.L1 := L1 pksim;
      Ksim.L2 := layer_combine (M pksim) (L2 pksim) (sk pksim);
      Ksim.R := R pksim; |}.
  Next Obligation.
    exact (layer_sim pksim).
  Qed.
End PROG_SIM.
Coercion prog_sim_coercion : prog_ksim >-> Ksim.ksim.

Section VCOMP.

  Context {K1 K2 K3 L1 L2 L3} {M N: Clight.program}
          {R: krel K1 K2} {S: krel K2 K3} {sk1 sk2}
          (Hsk1: link (skel L2) (skel (semantics1 M)) = Some sk1)
          (Hsk2: link (skel L3) (skel (semantics1 N)) = Some sk2)
          (HL1: forward_simulation 1 (kcc_ext R) L1 (layer_combine M L2 sk1))
          (HL2: forward_simulation 1 (kcc_ext S) L2 (layer_combine N L3 sk2)).
  Context (p: Clight.program) (Hlk: link M N = Some p).

  Theorem layer_vcomp:
    forward_simulation 1 (kcc_ext (krel_comp R S)) L1 (layer_combine p L3 sk2).
  Proof.

End VCOMP.

Require Import FlatComp.
