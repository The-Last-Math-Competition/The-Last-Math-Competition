/-
  Axiom audit for the formalisation in `Main.lean`.

  Run with:
      lake env lean Check.lean

  Every theorem must report only core axioms; in particular none may report
  `sorryAx`.  The concrete computations here should depend on `propext` only
  (or on no axioms at all).
-/

import Main

open Tlmc3844

-- The monoid axioms of H(S_3)
#print axioms assoc
#print axioms identity
#print axioms gen_idem_s1
#print axioms gen_idem_s2
#print axioms braid
#print axioms s1_mul_s2
#print axioms s2_mul_s1

-- The two covering submonoids
#print axioms A_sub
#print axioms B_sub
#print axioms A_proper
#print axioms B_proper
#print axioms cover

-- No single proper submonoid covers H(S_3)
#print axioms no_one_cover

-- The refutation
#print axioms covering_number_le_two
#print axioms covering_number_ne_one
#print axioms covering_number_is_two
#print axioms conjecture_00000003844_false
