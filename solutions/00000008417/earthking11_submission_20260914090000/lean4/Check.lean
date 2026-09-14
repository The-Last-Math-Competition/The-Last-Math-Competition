/-
  Axiom audit for the refutation certificate in `Main.lean`.

  Run with:
      lake env lean Check.lean

  Every theorem should report only core axioms; in particular none may report
  `sorryAx`.  The heavy existence theorem is proved by kernel `decide`
  reduction, so it introduces no axiom beyond the code footprint of `decide`
  itself (expected: `propext`).  The preferred default is the fully
  kernel-checked version; `native_decide` is NOT used.
-/

import Main

open Tlmc8417

-- Structural facts about the witness
#print axioms blocks_all_popcount_six
#print axioms blocks_nodup
#print axioms blocks_length
#print axioms fives_all_popcount_five
#print axioms fives_length
#print axioms total_incidences

-- MAIN: every one of the 792 five-subsets lies in exactly one block
#print axioms every_five_in_exactly_one_block
#print axioms every_five_covered

-- The six classical divisibility conditions at (5,6,12)
#print axioms div_i0
#print axioms div_i1
#print axioms div_i2
#print axioms div_i3
#print axioms div_i4
#print axioms div_i5
#print axioms divisibility_conditions_hold

-- Prop-level packaging
#print axioms witt_is_design
#print axioms exists_S5612
#print axioms exists_and_divisible
