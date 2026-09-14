/-
  Axiom audit for the formalisation in `Main.lean`.

  Run with:
      lake env lean Check.lean

  Every theorem must report only core axioms (`propext`, `Quot.sound`); in
  particular none may report `sorryAx`, so the audit also certifies that no
  `sorry` and no Mathlib dependency is present.
-/

import Main

open Tlmc1737

-- The smoothness test on concrete values
#print axioms isSmooth_sound
#print axioms isSmooth_one
#print axioms isSmooth_two
#print axioms isSmooth_three
#print axioms isSmooth_four
#print axioms isSmooth_eight
#print axioms isSmooth_nine
#print axioms isSmooth_five
#print axioms isSmooth_seven
#print axioms not_isSmooth_five
#print axioms not_isSmooth_seven

-- Faithfulness of the S-integrality predicate
#print axioms sIntegral_sound

-- The Boolean checks over the 21-element list
#print axioms integralAll_eq
#print axioms distinctAll_eq

-- Every listed point is S-integral; the listed points are pairwise distinct
#print axioms all_integral
#print axioms all_distinct

-- The numerical facts about the witness list
#print axioms pts_length
#print axioms twelve_lt_length

-- MAIN: the conjecture is false (21 > 12 witnesses for S = {2,3})
#print axioms conjecture_00000001737_false
#print axioms more_than_twelve_points
#print axioms not_max_le_twelve
