import Main

open Tlmc458

/-! Axiom audit.  Each of these should print no axioms (or at most `propext`),
and in particular must not contain `sorryAx` or `Lean.ofReduceBool`. -/

#print axioms formula_at_three
#print axioms modulus_nonneg
#print axioms no_abs_eq_neg_one
#print axioms contradiction_sign
#print axioms contradiction_sign_strong
#print axioms card_T3
#print axioms bottom_is_min
#print axioms top_is_max
#print axioms mu_T3
#print axioms abs_mu_T3
#print axioms conjecture_00000000458_false
