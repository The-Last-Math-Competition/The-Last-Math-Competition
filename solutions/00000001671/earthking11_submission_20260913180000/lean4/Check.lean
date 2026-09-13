import Main

open Tlmc1671

/-! Axiom audit for the refutation of conjecture 00000001671.

Every theorem below is proved by `by decide` over kernel-reducible data, so the
expected output is that none of them depends on any axioms (in particular there
is no `sorryAx` and no `ofReduceBool`). -/

#print axioms Tlmc1671.basis_three_is_one
#print axioms Tlmc1671.basis_four_is_two
#print axioms Tlmc1671.no_one_fold_four
#print axioms Tlmc1671.k3_basis_is_one_fold
#print axioms Tlmc1671.k4_basis_is_two_fold
#print axioms Tlmc1671.formula_three
#print axioms Tlmc1671.formula_four
#print axioms Tlmc1671.mismatch_three
#print axioms Tlmc1671.mismatch_four
#print axioms Tlmc1671.conjecture_00000001671_false
