/-
  Axiom audit for the formalisation in `Main.lean`.

  Run with:
      lake env lean Check.lean

  Every theorem should report only core axioms (`propext`, `Quot.sound`,
  possibly `Classical.choice`); in particular none may report `sorryAx`.
-/

import Main

open Tlmc463

-- Primality test on concrete values
#print axioms primeB_two
#print axioms primeB_three
#print axioms primeB_four
#print axioms primeB_five

-- Every n >= 2 has a prime divisor
#print axioms exists_prime_dvd

-- The key divisibility step p | n -> p*p | n^(n-2)
#print axioms sq_dvd_pow_of_dvd

-- MAIN: for every n >= 4, n^(n-2) is not squarefree
#print axioms not_squarefree_pow

-- The squarefree small cases
#print axioms squarefree_one
#print axioms squarefree_three
#print axioms squarefree_two_pow
#print axioms squarefree_three_pow
#print axioms squarefree_of_le_three
#print axioms sqfree_pow_le_three
#print axioms sqfree_pow_iff_le_three

-- The count is bounded by 3, for every N
#print axioms sqfreeCount_eq_min
#print axioms sqfreeCount_le_three
#print axioms sqfreeCount_10
#print axioms sqfreeCount_100
#print axioms sqfreeCount_1000
#print axioms sqfreeCount_1000000
#print axioms conjecture_00000000463_false
