/-
  Axiom audit for the formalisation in `Main.lean`.

  Build/run with:

      lake build
      lake env lean Check.lean

  Every theorem below must report only core axioms (`propext`, `Quot.sound`,
  and possibly `Classical.choice`); in particular none may report `sorryAx`.
  The expected output is printed next to each `#print axioms` command below.
-/

import Main

open Tlmc153

-- Primality: no prime is divisible by 4
-- expected: 'four_not_dvd_of_isPrime' does not depend on any axioms
#print axioms four_not_dvd_of_isPrime

-- The iteration of T and its closed form
#print axioms iter_zero
#print axioms iter_succ
#print axioms iter_val

-- Minimality: every full orbit is all of X
-- expected: 'minimal' depends on axioms: [propext, Quot.sound]
#print axioms minimal
#print axioms isMinimal

-- The prime-index orbit omits its own starting point
-- expected: 'primeOrbitAt_not_self' depends on axioms: [propext, Quot.sound]
#print axioms primeOrbitAt_not_self
#print axioms primeOrbitAt_not_univ
#print axioms prime_iter_zero_val_ne_zero
#print axioms zero_not_mem_primeOrbit

-- The closure of the prime-index orbit is not all of X
#print axioms primeOrbitClosure_not_univ

-- The packaged refutation of conjecture 00000000153
-- expected: 'conjecture_00000000153_false' depends on axioms: [propext, Quot.sound]
#print axioms conjecture_00000000153_false
#print axioms conjecture_00000000153_false_at_zero
