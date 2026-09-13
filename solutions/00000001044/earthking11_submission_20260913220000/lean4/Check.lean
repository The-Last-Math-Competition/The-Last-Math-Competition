/-
  Axiom audit for the formalisation in `Main.lean`.

  Build/run with:
      lake env lean Check.lean

  Every theorem below must report only core axioms (`propext` and possibly
  `Classical.choice` / `Quot.sound`); in particular none may report `sorryAx`
  and none may depend on Mathlib.
-/

import Main

open Tlmc1044

-- Primary witness (q,n) = (3,2), d = gcd(2,8) = 2 > 1
#print axioms q3n2_d
#print axioms q3n2_d_gt_one
#print axioms q3n2_formula
#print axioms q3n2_a0
#print axioms q3n2_a1
#print axioms q3n2_a2
#print axioms q3n2_a0_is_formula
#print axioms q3n2_a1_ties
#print axioms q3n2_a2_ties
#print axioms q3n2_a1_not_bigger
#print axioms q3n2_a2_not_bigger
#print axioms q3n2_no_a_strictly_bigger
#print axioms q3n2_nonunique
#print axioms q3n2_tie
#print axioms q3n2_min

-- The collected disproof
#print axioms conjecture_00000001044_false

-- Same behaviour at (5,2) and (7,2)
#print axioms q5n2_d
#print axioms q5n2_formula
#print axioms q5n2_all
#print axioms q5n2_min
#print axioms q5n2_tie
#print axioms q5n2_no_a_strictly_bigger
#print axioms q7n2_d
#print axioms q7n2_formula
#print axioms q7n2_all
#print axioms q7n2_min
#print axioms q7n2_tie

-- The reversal at (7,3)
#print axioms q7n3_d
#print axioms q7n3_formula
#print axioms q7n3_a0
#print axioms q7n3_a1
#print axioms q7n3_reversal
#print axioms q7n3_a0_exceeds_formula
#print axioms q7n3_a0_largest
#print axioms q7n3_nonzero_beats

-- Further breakages
#print axioms q5n3_a0_permutes
#print axioms q5n3_d_not_dvd
#print axioms q5n3_min
#print axioms q5n4_d
#print axioms q5n4_a0
#print axioms q5n4_a2
#print axioms q5n4_beats
#print axioms q5n4_min
#print axioms q5n4_no_a_attains_formula
#print axioms q3n4_d
#print axioms q3n4_tie
#print axioms q3n4_d_not_dvd

-- Machine-checked tables
#print axioms table_3_2
#print axioms table_5_2
#print axioms table_7_2
#print axioms table_7_3
#print axioms table_5_4
