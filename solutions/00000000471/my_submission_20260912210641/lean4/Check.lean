/-
  Verification of the refutation of 00000000471.

  Builds on Main.lean and (1) prints the enumerations, (2) confirms both
  refutations are available as terms, (3) prints the axioms each theorem
  depends on.

  Run with:  lake build && lake env lean Check.lean
-/
import Main

open Tlmc471

-- 1. the hypergraph
#eval edges 3
#eval edges 4
#eval sublists (edges 3)
#check edges3_length
#check edges4_length
#check edges5_length
#check sublists_length

-- 2. the counting bound (refutation 1)
#check hypertrees_le_subhypergraphs
#check refutation_bound_3
#check refutation_bound_6

-- 3. exact enumeration (refutation 2)
#eval hypertrees 3
#eval (hypertrees 4).length
#eval (hypertrees 5).length
#check hypertrees3_length
#check hypertrees3_eq
#check hypertrees4_length
#check hypertrees5_length

-- 4. the formula
#eval formula 3
#eval formula 4
#eval formula 5
#eval formula 6
#check formula3
#check formula4
#check formula5
#check formula6

-- 5. the disagreement, spelled out
#check refutation_exact_3
#check refutation_exact_4
#check refutation_exact_5
#check summary_3
example : 3 > 2 := by decide
example : 57775431168 > 2 ^ 20 := by decide

-- 6. axioms
#print axioms sublists_length
#print axioms filter_length_le
#print axioms hypertrees_le_subhypergraphs
#print axioms refutation_bound_3
#print axioms refutation_bound_6
#print axioms hypertrees3_length
#print axioms hypertrees4_length
#print axioms hypertrees5_length
#print axioms refutation_exact_3
#print axioms refutation_exact_4
#print axioms refutation_exact_5
