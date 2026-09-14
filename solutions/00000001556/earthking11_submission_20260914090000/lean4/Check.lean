/-
  Axiom audit for the formalisation in `Main.lean`.

  Run with:
      lake env lean Check.lean

  Every theorem should report only core axioms (`propext`, `Quot.sound`,
  possibly `Classical.choice`); in particular none may report `sorryAx`.
-/

import Main

open Tlmc1556

-- Finite residue checks (pure `decide` computations)
#print axioms D_ok
#print axioms Deuc_ok

-- MAIN: properness of the 5-colouring on the union of both readings
#print axioms color_shift_ne
#print axioms adjacent_colors_ne

-- Properness of the 3-colouring on the Euclidean reading
#print axioms color3_shift_ne

-- Clique certificates (lower bounds)
#print axioms C5_clique
#print axioms C3_clique
