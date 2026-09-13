/-
  Axiom audit for the formalisation in `Main.lean`.

  Build/run with:
      lake env lean Check.lean

  Every theorem below should report only axioms from the standard library
  (`propext`, `Classical.choice`, `Quot.sound`) or nothing at all; in particular
  none may report `sorryAx`, and none depends on Mathlib.
-/

import Main

open Tlmc1678

-- Zero forcing on P_4
#print axioms singleton_zero_forces
#print axioms empty_not_zfs
#print axioms zeroForcingNumber_P4

-- Path covers on P_4
#print axioms whole_path_is_path_cover
#print axioms pathCoverNumber_P4

-- Diameter of P_4 is 3 (odd)
#print axioms diameter_P4
#print axioms diameter_P4_odd

-- P_4 has a perfect matching
#print axioms matching_01_23
#print axioms P4_has_perfect_matching

-- The difference is 0, not 1
#print axioms difference_P4
#print axioms difference_P4_ne_one

-- The "exactly" clause and the collected refutation
#print axioms P4_satisfies_rhsPredicate
#print axioms exactly_clause_false
#print axioms conjecture_00000001678_refuted
