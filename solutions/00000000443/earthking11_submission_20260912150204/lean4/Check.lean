/-
  Axiom audit for the formalisation in `Main.lean`.

  Build/run with:
      lake env lean Check.lean

  Every theorem below should report no axioms (or only `propext`); in particular
  none may report `sorryAx`, and none depends on Mathlib.
-/

import Main

open Tlmc443

-- Moebius values
#print axioms mobius_one
#print axioms mobius_two
#print axioms mobius_three
#print axioms mobius_four
#print axioms mobius_six
#print axioms mobius_twelve

-- Exact dimensions (Witt's formula)
#print axioms wittDim_one
#print axioms wittDim_two
#print axioms wittDim_three
#print axioms wittDim_four
#print axioms wittDim_five
#print axioms wittDim_six
#print axioms wittDim_seven
#print axioms wittDim_eight
#print axioms wittDim_nine
#print axioms wittDim_ten
#print axioms wittDim_eleven
#print axioms wittDim_twelve

-- Failure (A)
#print axioms bound_four
#print axioms claimedBound_four
#print axioms inequality_fails_at_four
#print axioms inequality_fails_4_to_12

-- Failure (B)
#print axioms gap_fails_at_three
#print axioms actualGap_three_ne
#print axioms gap_fails_at_seven
#print axioms gap_fails_at_eleven
#print axioms gap_holds_at_five

-- The disproof
#print axioms conjecture_00000000443_false
