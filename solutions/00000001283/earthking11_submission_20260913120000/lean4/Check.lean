import Main

/-!
# Axiom audit for the disproof of conjecture 00000001283

Every result in `Main.lean` must depend only on Lean's three standard axioms
(`propext`, `Classical.choice`, `Quot.sound`), or on none at all. In particular there must
be no `sorryAx` (which is what `sorry` produces) and no custom `axiom`.
-/

open Tlmc1283

#print axioms two_nim_two
#print axioms not_a_solution
#print axioms only_zero_solution
#print axioms no_pos_solutions
#print axioms int_two_pow_pos
#print axioms int_two_pow_ne_nine
#print axioms nine_not_pow
#print axioms nine_not_pow_neg
#print axioms clause2_fails_at_3_3
#print axioms conjecture_00000001283_false
