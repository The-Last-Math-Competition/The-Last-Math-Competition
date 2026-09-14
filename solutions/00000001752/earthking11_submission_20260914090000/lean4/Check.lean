/-
  Axiom audit for the formalisation in `Main.lean`.

  Run with:
      lake env lean Check.lean

  Every theorem must report only core axioms (`propext`, `Quot.sound`, possibly
  `Classical.choice`); in particular none may report `sorryAx`.
-/

import Main

open Tlmc1752

-- |S_3| = 6 (kernel computation)
#print axioms perms_length

-- Burnside numerator at k = 1 is 6 (fixed point counts 3,1,1,1,0,0)
#print axioms burnsideSum_eq

-- The conjectured right-hand numerator 1! * S(3,1) = 1
#print axioms formula_val

-- The Burnside average equals the orbit count 1
#print axioms burnside_average_is_one

-- MAIN: 6 ≠ 1, i.e. the Burnside average 1 is not the formula 1/6
#print axioms mismatch

-- The unit-fraction cross-multiplied form: 1 * 6 ≠ 1 * 1 (i.e. 6 ≠ 1)
#print axioms one_ne_one_sixth_cross
