/-
  Axiom audit for the formalisation in `Main.lean`.

  Build/run with:
      lake env lean Check.lean

  Every theorem below must report only core axioms (`propext` and possibly
  `Classical.choice`); in particular none may report `sorryAx`, and none may
  report `Lean.ofReduceBool` (which is why `Main.lean` uses `decide` and never
  `native_decide`).
-/

import Main

open Tlmc437

-- The ascending smallest-prime-factor search and the Möbius function
#print axioms minFac_20
#print axioms minFac_24
#print axioms mu_12
#print axioms mu_30

-- Values of Witt's formula L_n
#print axioms witt_1
#print axioms witt_2
#print axioms witt_6
#print axioms witt_8
#print axioms witt_24

-- Parities of L_n
#print axioms witt_1_even
#print axioms witt_2_odd
#print axioms witt_6_odd
#print axioms witt_8_even

-- The power-of-two flags
#print axioms isPow2_1
#print axioms isPow2_2
#print axioms isPow2_6
#print axioms isPow2_8

-- The refutation
#print axioms witness_1_2_parity
#print axioms fallback_2_8_parity
#print axioms iff_reading_fails
#print axioms parity_not_determined_by_pow2
#print axioms conjecture_00000000437_false
