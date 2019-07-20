
Class CDCategory (V : Type) (E : V -> V -> Type) :=
  {
    cdc_lattice :> forall X Y, CDLattice (E X Y);

    id {X} : E X X;
    comp {X Y Z} : E Y Z -> E X Y -> E X Z;

    id_comp {X Y} (f : E X Y) : comp id f = f;
    comp_id {X Y} (f : E X Y) : comp f id = f;

    comp_sup {X Y Z I} (g : E Y Z) (f : I -> E X Y) :
      comp g (sup f) = sup (fun i => comp g (f i));
    comp_inf {X Y Z I} (g : E Y Z) (f : I -> E X Y) :
      comp g (inf f) = inf (fun i => comp g (f i));
  }.
