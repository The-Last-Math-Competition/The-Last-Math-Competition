/-
  Axiom audit for the formalisation in `Main.lean`.

  Build/run with:
      lake env lean Check.lean

  Every theorem below should report only the standard axioms (in particular no
  `sorryAx`, and no Mathlib dependency). -/

import Main

open Tlmc8371

-- Failure 1: the formula at n = 3 and its non-integrality
#print axioms formula_at_3
#print axioms no_count_is_half

-- Conjectured formula at the other checked values
#print axioms formula_at_4
#print axioms formula_at_5
#print axioms formula_at_6

-- Johnson vertex counts
#print axioms johnson_3
#print axioms johnson_4
#print axioms johnson_5
#print axioms johnson_6

-- Failure 2: formula vs. Johnson vertex count
#print axioms formula_ne_johnson_4
#print axioms formula_ne_johnson_5
#print axioms formula_ne_johnson_6

-- The disproof
#print axioms conjecture_00000008371_false
