import Main

open Tlmc982

/-! Axiom audit.  Each of these should print no axioms, and in particular must
not contain `sorryAx` or `Lean.ofReduceBool`. -/

#print axioms nonradial_witness
#print axioms z_not_radial
#print axioms one_ne_z
#print axioms one_ne_sq
#print axioms z_ne_sq
#print axioms three_distinct_functions
#print axioms conjecture_00000000982_false
