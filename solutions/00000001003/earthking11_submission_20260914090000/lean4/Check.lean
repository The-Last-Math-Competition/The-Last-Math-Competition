/-
  Axiom audit for the formalisation in `Main.lean`.

  Run with:
      lake env lean Check.lean

  Every theorem should report no axioms at all (the whole file is decided
  computation over `Nat`); in particular none may report `sorryAx`, and none
  may report `Lean.ofReduceBool` (which would indicate `native_decide`).
-/

import Main

-- Non-vacuity checks on the executable cap test
#print axioms isCap_collinear_false
#print axioms isCap_independent_true
#print axioms bad_witness

-- The 20-point cap
#print axioms pts20_nodup
#print axioms pts20_length
#print axioms pts20_isCap

-- Arithmetic of the conjecture's formula at q = 3
#print axioms formula_three
#print axioms twenty_gt_fourteen
#print axioms formula_three_lt_length

-- MAIN: the refutation
#print axioms refutes_conjecture
#print axioms conjecture_00000001003_false
