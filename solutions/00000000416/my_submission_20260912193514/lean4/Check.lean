/-
  Verification of the refutation of 00000000416.

  Builds on Main.lean and (1) confirms the enumeration, (2) confirms the
  refutation is available as a term, (3) prints the axioms the file depends on.

  Run with:  lake env lean Check.lean
-/
import Main

open Tlmc416

-- 1. the enumeration: shape (2,2) has exactly two standard Young tableaux
#eval sols
#check sols_length
#check sols_eq

-- 2. the refutation
#check orbit_bound
#check no_such_orbits
#check refutation_at_two
#check refutation_abstract

-- 3. a direct instance: 2 < 3, so a total of 2 cannot cover the claimed orbits
example : 2 < 3 := by decide
example : ¬ (3 ≤ 2) := by decide

-- 4. axioms
#print axioms sols_length
#print axioms orbit_bound
#print axioms refutation_at_two
#print axioms refutation_abstract
