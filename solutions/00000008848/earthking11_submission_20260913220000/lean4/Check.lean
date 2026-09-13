/-
  Axiom audit for the formalisation in `Main.lean`.

  Run with:
      lake env lean Check.lean

  Every theorem below must report only core axioms; in particular none may
  report `sorryAx` and none may depend on Mathlib.  Core Lean only
  (`import Std`).
-/

import Main

open Tlmc8848

-- Primary, non-vacuous witness: the identity map on ℤ.
#print axioms id_isFixed
#print axioms id_no_least_fixed
#print axioms id_no_greatest_fixed
#print axioms id_mono
#print axioms refutes_least_fixed_point_with_fixpoint
#print axioms refutes_greatest_fixed_point_with_fixpoint
#print axioms id_fixset_unbounded_below
#print axioms id_fixset_unbounded_above

-- Literal reading: the shift map f(x) = x + 1 on ℤ.
#print axioms f_mono
#print axioms f_fixfree
#print axioms no_fixed_at_all
#print axioms f_no_least_fixed
#print axioms f_no_greatest_fixed
#print axioms refutes_least_fixed_point
#print axioms refutes_greatest_fixed_point

-- Packaged refutations.
#print axioms clause_a_false
#print axioms clause_a_false_with_fixpoint
