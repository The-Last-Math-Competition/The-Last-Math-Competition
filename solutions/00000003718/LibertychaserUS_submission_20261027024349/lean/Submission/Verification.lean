import Submission.Main

/-!
# Axiom audit

Every declaration below depends only on the standard axioms `propext`, `Classical.choice` and
`Quot.sound`.  No `sorry`, no `native_decide`, no additional axioms.
-/

#print axioms TLMC3718.det_leaf
#print axioms SimpleGraph.matchingPolyIn_leaf
#print axioms SimpleGraph.IsAcyclic.exists_leaf_in
#print axioms SimpleGraph.charpoly_adjMatrixIn_leaf
#print axioms SimpleGraph.matchingPolyIn_eq_charpoly
#print axioms SimpleGraph.matchingPolynomial_eq_charpoly
#print axioms SimpleGraph.matchingPolynomial_eq_sum_numMatchings
#print axioms TLMC3718.matchingPolynomial_splits
#print axioms TLMC3718.card_roots_matchingPolynomial
#print axioms TLMC3718.exists_real_of_isRoot
#print axioms TLMC3718.im_eq_zero_of_isRoot
#print axioms TLMC3718.sum_roots_pow_eq_card_closedWalks
#print axioms TLMC3718.conjecture_00000003718
