import Main

open Tlmc1299

/-! Axiom audit.  Each of these should print no axioms, and in particular must
not contain `sorryAx` or `Lean.ofReduceBool`. -/

#print axioms returns_at_15
#print axioms no_return_below_15
#print axioms distinct_first_15
#print axioms fifteen_not_divides_five
#print axioms min_period_five
#print axioms conjecture_00000001299_false
