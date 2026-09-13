import Main

open Tlmc1676

/-! Axiom audit for the refutation of conjecture 00000001676.

Every theorem below is proved by `by decide` over kernel-reducible data, so the
expected output is that none of them depends on any axioms (in particular there
is no `sorryAx` and no `ofReduceBool`). -/

#print axioms Tlmc1676.minBoundaryOfSize_one
#print axioms Tlmc1676.minBoundaryOfSize_three
#print axioms Tlmc1676.formula_3_1
#print axioms Tlmc1676.formula_3_3
#print axioms Tlmc1676.mismatch_3_1
#print axioms Tlmc1676.mismatch_3_3
#print axioms Tlmc1676.radicand_negative_3_4
#print axioms Tlmc1676.conjecture_00000001676_false
