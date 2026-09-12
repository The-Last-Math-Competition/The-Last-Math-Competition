/-
  Axiom audit for the formalisation in `Main.lean`.

  Build/run with:
      lake env lean Check.lean

  Every theorem below should report only `propext` (and, for the `Rat` comparison,
  whatever core instances the elaborator uses via `decide`); in particular none may
  report `sorryAx`, and none depends on Mathlib.
-/

import Main

open Tlmc1186

-- Factorisations
#print axioms factor_60
#print axioms factor_504
#print axioms factor_660

-- Distinct prime counts `ω`
#print axioms distinctPrimeCount_60
#print axioms distinctPrimeCount_504
#print axioms distinctPrimeCount_660

-- Contradiction 1
#print axioms distinctPrimeCount_504_ne_four
#print axioms no_order_504_has_four_distinct_primes

-- Contradiction 2
#print axioms distinctPrimeCount_660_ne_five
#print axioms no_order_660_has_five_distinct_primes

-- Contradiction 3 (Nat encoding of `504 / 60 > 4`)
#print axioms four_times_sixty_lt_504

-- Multiplicity reading
#print axioms Omega_60
#print axioms Omega_504
#print axioms Omega_660

-- The disproof
#print axioms conjecture_00000001186_false
