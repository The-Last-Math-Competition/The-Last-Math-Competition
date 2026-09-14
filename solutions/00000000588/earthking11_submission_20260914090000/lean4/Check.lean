/-
  Axiom audit for the formalisation in `Main.lean`.

  Run with:
      lake env lean Check.lean

  Every theorem should report "does not depend on any axioms" (the concrete
  `Nat`/`omega`/`decide` proofs are axiom-free); in particular no theorem may
  report `sorryAx`.
-/

import Main

open Tlmc588

-- n = 4, the counterexample: S = <4,5,6,7>
#print axioms not_inS_1
#print axioms not_inS_2
#print axioms not_inS_3
#print axioms not_isMax_0
#print axioms isMax_5
#print axioms isMax_6
#print axioms isMax_7
#print axioms maximals_correct
#print axioms t_eq_3
#print axioms t_ne_two

-- MAIN: t = 3 and 3 != 2
#print axioms counterexample_n4

-- n = 3: the conjecture happens to hold (t = 2 = ceil(3/2))
#print axioms maximals3_correct
#print axioms conjecture_holds_n3

-- n = 5: the conjecture fails again (t = 4 != 3 = ceil(5/2))
#print axioms maximals5_correct
#print axioms counterexample_n5

-- Computed values
#eval t
#eval t3
#eval t5
