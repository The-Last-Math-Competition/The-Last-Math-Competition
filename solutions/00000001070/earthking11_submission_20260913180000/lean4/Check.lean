/-
  Axiom audit for the formalisation in `Main.lean`.

  Build/run with:
      lake env lean Check.lean

  Every theorem below should report only `propext` (introduced through the
  standard library lemmas used by `decide`, `rw` and `simpa`); in particular
  none may report `sorryAx`, and none depends on Mathlib.  The disproof uses
  core Lean only (`import Std`).
-/

import Main

open Tlmc1070

-- Boolean enumeration of the three-fold sum of the witness
#print axioms witness_threefold_bool

-- Soundness bridge from the Boolean test to the propositional sumset
#print axioms isThreefoldSum_sound

-- The witness {0,1,3} has three-fold sum all of F_7
#print axioms witness_threefold

-- The witness has exactly three distinct elements
#print axioms witness_size

-- The explicit 27 three-fold sums already cover all of F_7
#print axioms witness_threefold_set

-- No two-element subset of F_7 has three-fold sum F_7
#print axioms no_two_elements

-- The conjectured formula value at p = 7
#print axioms formula_at_seven

-- The corrected value ceil((p+2)/3) at p = 7, and its tightness
#print axioms corrected_at_seven
#print axioms corrected_matches_witness

-- The formula's value 4 differs from the witness size 3
#print axioms formula_too_large

-- The collected disproof
#print axioms conjecture_00000001070_false
