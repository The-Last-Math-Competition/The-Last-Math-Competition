import Std

/-!
Arithmetic core of the disproof of conjecture 00000000806.
The report proves that the first eigenvalue of two congruent disjoint components
occurs twice in the Dirichlet spectrum when eigenvalues are counted with
multiplicity. This file verifies the consequence for the displayed gap ratio.
-/

def spectralGap (lambda1 lambda2 : Nat) : Nat := lambda2 - lambda1

/-- A nonnegative rational represented by numerator and positive denominator. --/
def spectralRatio (lambda1 lambda2 : Nat) : Nat × Nat :=
  (spectralGap lambda1 lambda2, lambda1)

def fractionEq (a b : Nat × Nat) : Prop := a.1 * b.2 = b.1 * a.2

theorem repeated_first_eigenvalue_has_zero_gap (lambda : Nat) :
    spectralGap lambda lambda = 0 := by
  simp [spectralGap]

theorem repeated_first_eigenvalue_has_zero_ratio (lambda : Nat) (_h : 0 < lambda) :
    spectralRatio lambda lambda = (0, lambda) := by
  simp [spectralRatio, spectralGap]

theorem zero_is_not_three_quarters : ¬ fractionEq (0, 1) (3, 4) := by
  unfold fractionEq
  decide

theorem equal_component_union_refutes_claimed_value :
    ¬ fractionEq (spectralRatio 1 1) (3, 4) := by
  unfold fractionEq spectralRatio spectralGap
  decide

#print axioms repeated_first_eigenvalue_has_zero_gap
#print axioms repeated_first_eigenvalue_has_zero_ratio
#print axioms zero_is_not_three_quarters
#print axioms equal_component_union_refutes_claimed_value
