/-
  Axiom audit for the formalisation in `Main.lean`.

  Build/run with:
      lake env lean Check.lean

  Every theorem below should report only `propext` (and, where `Rat` comparison or
  division is decided, whatever core instances the elaborator uses via `decide`);
  in particular none may report `sorryAx`, and none depends on Mathlib.
-/

import Main

open Tlmc1097

-- Explicit enumeration over Fin 5
#print axioms rootTripleCount_5_2
#print axioms mean_5_2
#print axioms meanRootCount_5_2

-- The claimed main term
#print axioms gcdB_1_4
#print axioms claimedExponent_5_2
#print axioms claimed_main_term_at_5_2
#print axioms claimedMainTerm_5_2

-- The internal contradiction
#print axioms contradiction

-- The variance clause
#print axioms second_moment_5
#print axioms variance_5

-- The disproof
#print axioms conjecture_00000001097_false
