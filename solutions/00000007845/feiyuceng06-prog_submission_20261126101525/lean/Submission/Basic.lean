import Mathlib

namespace Submission00000007845

open Matrix
open scoped Matrix.Norms.L2Operator

abbrev Mat₂ := Matrix (Fin 2) (Fin 2) ℝ
abbrev Vec₂ := Fin 2 → ℝ

/-- The squared Euclidean norm of a vector, also the squared spectral norm of a row. -/
noncomputable def sqNorm (x : Vec₂) : ℝ := x ⬝ᵥ x

/-- One Kaczmarz step on the error for a consistent system, choosing row i. -/
noncomputable def projectError (A : Mat₂) (i : Fin 2) (e : Vec₂) : Vec₂ :=
  e - ((A i ⬝ᵥ e) / sqNorm (A i)) • A i

/-- The sampling weight is a function of the squared row norm.
Use `Real.sqrt` for row-norm sampling or `id` for squared-row-norm sampling. -/
noncomputable def expectedRatio (weight : ℝ → ℝ) (A : Mat₂) (e : Vec₂) : ℝ :=
  ∑ i : Fin 2,
    (weight (sqNorm (A i)) / (∑ j : Fin 2, weight (sqNorm (A j)))) *
      (sqNorm (projectError A i e) / sqNorm e)

/-- The Euclidean condition number of an invertible square matrix. -/
noncomputable def conditionNumber (A : Mat₂) : ℝ := ‖A‖ * ‖A⁻¹‖

/-- The proposed worst-case rate implies this upper bound even in dimension two. -/
def ClaimedBound (weight : ℝ → ℝ) : Prop :=
  ∀ (A : Mat₂) (e : Vec₂), A.rank = 2 → e ≠ 0 →
    expectedRatio weight A e ≤ 1 - (conditionNumber A)⁻¹ ^ 2

private def e₀ : Vec₂ := ![1, 0]

private theorem one_row_zero : (1 : Mat₂) 0 = ![1, 0] := by
  ext i
  fin_cases i <;> simp [Matrix.one_apply]

private theorem one_row_one : (1 : Mat₂) 1 = ![0, 1] := by
  ext i
  fin_cases i <;> simp [Matrix.one_apply]

private theorem zero_sqNorm : sqNorm (0 : Vec₂) = 0 := by
  simp [sqNorm]

private theorem first_sqNorm : sqNorm ![1, 0] = 1 := by
  norm_num [sqNorm, dotProduct, Fin.sum_univ_two]

private theorem second_sqNorm : sqNorm ![0, 1] = 1 := by
  norm_num [sqNorm, dotProduct, Fin.sum_univ_two]

private theorem first_project : projectError 1 0 e₀ = 0 := by
  simp [projectError, one_row_zero, first_sqNorm, e₀]

private theorem second_project : projectError 1 1 e₀ = e₀ := by
  have dot : (![0, 1] : Vec₂) ⬝ᵥ e₀ = 0 := by
    norm_num [dotProduct, Fin.sum_univ_two, e₀]
  simp [projectError, one_row_one, dot]

theorem identity_expectedRatio (weight : ℝ → ℝ) (hWeight : weight 1 = 1) :
    expectedRatio weight 1 e₀ = 1 / 2 := by
  rw [expectedRatio, Fin.sum_univ_two]
  simp only [Fin.sum_univ_two, one_row_zero, one_row_one, first_project, second_project,
    zero_sqNorm, show sqNorm e₀ = 1 from first_sqNorm, first_sqNorm, second_sqNorm, hWeight]
  norm_num

theorem identity_conditionNumber : conditionNumber (1 : Mat₂) = 1 := by
  simp [conditionNumber]

theorem kaczmarz_counterexample (weight : ℝ → ℝ) (hWeight : weight 1 = 1) :
    ∃ (A : Mat₂) (e : Vec₂), A.rank = 2 ∧ e ≠ 0 ∧
      expectedRatio weight A e > 1 - (conditionNumber A)⁻¹ ^ 2 := by
  refine ⟨1, e₀, by simp, ?_, ?_⟩
  · intro h
    have hnorm := congrArg sqNorm h
    rw [show sqNorm e₀ = 1 from first_sqNorm, zero_sqNorm] at hnorm
    exact one_ne_zero hnorm
  · rw [identity_expectedRatio weight hWeight, identity_conditionNumber]
    norm_num

private theorem bound_false (weight : ℝ → ℝ) (hWeight : weight 1 = 1) :
    ¬ ClaimedBound weight := by
  intro h
  obtain ⟨A, e, hRank, hError, hCounterexample⟩ := kaczmarz_counterexample weight hWeight
  exact (not_le_of_gt hCounterexample) (h A e hRank hError)

theorem conjecture_00000007845_false (RemainingClaims : Prop) :
    ¬ (ClaimedBound Real.sqrt ∧ RemainingClaims) ∧
      ¬ (ClaimedBound id ∧ RemainingClaims) :=
  ⟨fun h => bound_false Real.sqrt Real.sqrt_one h.1, fun h => bound_false id rfl h.1⟩

#print axioms conjecture_00000007845_false

end Submission00000007845
