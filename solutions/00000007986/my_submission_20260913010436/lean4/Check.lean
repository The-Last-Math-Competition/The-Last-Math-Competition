import Main

/-! Sanity checks: print the computed covering radii and verify that every
    theorem of Main.lean is axiom-free (`#print axioms` must report
    "does not depend on any axioms"). -/

open Tlmc7986 in
#eval s!"coverRad4 = {coverRad4}   (expected 2)"
open Tlmc7986 in
#eval s!"coverRad2 = {coverRad2}   (expected 1)"

#print axioms Tlmc7986.rho_C4
#print axioms Tlmc7986.refute_bound_4
#print axioms Tlmc7986.rho_C2
#print axioms Tlmc7986.refute_bound_2
