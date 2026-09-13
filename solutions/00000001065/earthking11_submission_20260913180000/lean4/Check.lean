import Main

/-!
Axiom audit for the refutation of Conjecture 00000001065.

Every theorem below should be free of `sorryAx` and of `ofReduceBool`
(the proofs use the `decide` tactic only, never `native_decide`).
-/

#print axioms TLM1065.nikodym_two
#print axioms TLM1065.kakeya_three
#print axioms TLM1065.nikodym_min
#print axioms TLM1065.kakeya_min
#print axioms TLM1065.no_kakeya_lt_three
#print axioms TLM1065.no_nikodym_lt_two
#print axioms TLM1065.difference_not_q_minus_one
#print axioms TLM1065.conjecture_00000001065_false
