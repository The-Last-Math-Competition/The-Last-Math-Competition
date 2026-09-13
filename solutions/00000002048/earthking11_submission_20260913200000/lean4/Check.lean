/-
  Axiom audit for the formalisation in `Main.lean`.

  Build/run with:
      lake env lean Check.lean

  Every theorem below should report only core axioms (`propext` and possibly
  `Classical.choice`); in particular none may report `sorryAx` and none depends
  on Mathlib.
-/

import Main

open Tlmc2048

-- The 3-fold sum of the concrete witness: 3A = {0,1,2,3} and 4 is missing
#print axioms witness_sum3
#print axioms witness_sum3_eq_range
#print axioms witness_four_nonzero
#print axioms witness_misses_four
#print axioms witness_inSum3_four
#print axioms witness_card
#print axioms witness_threshold

-- The disproof of the main claim at p = 5, A = {0,1}
#print axioms conjecture_00000002048_false
#print axioms conjecture_00000002048_not_holds
#print axioms witness_refutes_conjecture

-- The general family p ≡ 2 (mod 3): the missed residue, non-coverage, threshold
#print axioms family_misses_pred
#print axioms family_not_cover
#print axioms family_threshold

-- Cauchy–Davenport at the threshold gives only p - 1
#print axioms cauchy_davenport_at_threshold

-- The packaged general statement
#print axioms general_family_refutes

-- The listed primes 5, 11, …, 89
#print axioms family_primes_prime
#print axioms family_primes_mod
#print axioms general_family_verified
#print axioms listed_family_refutes
