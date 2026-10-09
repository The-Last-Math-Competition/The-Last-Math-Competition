import Solution

/- Independent endpoint expansion. This file belongs only to the reviewer build. -/
example : Conjecture1735.solutionSet 0 = {(0, 0)} :=
  Conjecture1735.solutionSet_zero

example : ¬ (
    ((∀ k : ℤ, Cardinal.mk {p : ℤ × ℤ // p.1 ^ 3 - 2 * p.2 ^ 3 = k} ≤ 12) ∧
      ∃ k : ℤ, Cardinal.mk {p : ℤ × ℤ // p.1 ^ 3 - 2 * p.2 ^ 3 = k} = 12) ∧
    Set.Finite {k : ℤ | Cardinal.mk {p : ℤ × ℤ // p.1 ^ 3 - 2 * p.2 ^ 3 = k} = 12}) :=
  Conjecture1735.conjecture_false

example : ¬ (
    (∀ k : ℤ, k ≠ 0 → Cardinal.mk {p : ℤ × ℤ // p.1 ^ 3 - 2 * p.2 ^ 3 = k} ≤ 12) ∧
    (∃ k : ℤ, k ≠ 0 ∧ Cardinal.mk {p : ℤ × ℤ // p.1 ^ 3 - 2 * p.2 ^ 3 = k} = 12) ∧
    Set.Finite {k : ℤ | k ≠ 0 ∧ Cardinal.mk {p : ℤ × ℤ // p.1 ^ 3 - 2 * p.2 ^ 3 = k} = 12}) :=
  Conjecture1735.nonzero_conjecture_false

#print axioms Conjecture1735.solutionSet
#print axioms Conjecture1735.solutionCount
#print axioms Conjecture1735.zero_fiber
#print axioms Conjecture1735.solutionSet_zero
#print axioms Conjecture1735.solutionCount_zero
#print axioms Conjecture1735.scaleSolution
#print axioms Conjecture1735.scaleSolution_injective
#print axioms Conjecture1735.solutionCount_le_scaled
#print axioms Conjecture1735.scaled_is_maximizer
#print axioms Conjecture1735.scaled_rhs_injective
#print axioms Conjecture1735.infinite_maximizers_of_nonzero_maximizer
#print axioms Conjecture1735.MaximumIsTwelve
#print axioms Conjecture1735.Conjecture
#print axioms Conjecture1735.twelve_solution_rhs_ne_zero
#print axioms Conjecture1735.maximum_twelve_implies_infinite_maximizers
#print axioms Conjecture1735.conjecture_false
#print axioms Conjecture1735.NonzeroConjecture
#print axioms Conjecture1735.nonzero_conjecture_false
