import Mathlib

namespace Submission00000008785

open Matrix
open scoped Matrix.Norms.L2Operator Ring

abbrev V := Fin 3 → ℝ
abbrev M := Matrix (Fin 3) (Fin 3) ℝ

noncomputable def rayleigh (A : M) (x : V) : ℝ :=
  (x ⬝ᵥ (A *ᵥ x)) / (x ⬝ᵥ x)

def krylov₂ (A : M) (x : V) : Submodule ℝ V :=
  Submodule.span ℝ ({x, A *ᵥ x} : Set V)

noncomputable def largestRitz (A : M) (K : Submodule ℝ V) : ℝ :=
  sSup {r | ∃ y ∈ K, y ≠ 0 ∧ rayleigh A y = r}

noncomputable def relativeError (target approx : ℝ) : ℝ :=
  |target - approx| / |target|

noncomputable def conditionNumber (A : M) : ℝ := ‖A‖ * ‖A⁻¹‖

/-- Even the claimed factor as an upper bound on the next nonnegative
relative error would entail this statement at the first Lanczos update. -/
def FactorBoundAtStart (A : M) (target : ℝ) (x : V) : Prop :=
  relativeError target (largestRitz A (krylov₂ A x)) ≤
    (1 - 2 / Real.sqrt (conditionNumber A)) * relativeError target (rayleigh A x)

noncomputable def exampleMatrix : M := diagonal ![1, 3 / 2, 2]

theorem example_posDef : exampleMatrix.PosDef := by
  apply Matrix.posDef_diagonal_iff.mpr
  intro i
  fin_cases i <;> norm_num

theorem example_topEigenvalue : IsGreatest (spectrum ℝ exampleMatrix) 2 := by
  rw [exampleMatrix, spectrum_diagonal]
  refine ⟨⟨2, rfl⟩, ?_⟩
  rintro _ ⟨i, rfl⟩
  fin_cases i <;> norm_num

theorem example_conditionNumber : conditionNumber exampleMatrix = 2 := by
  rw [conditionNumber, exampleMatrix, Matrix.inv_diagonal, Matrix.l2_opNorm_diagonal,
    Matrix.l2_opNorm_diagonal]
  have hDiag : ‖(![1, 3 / 2, 2] : V)‖ = 2 := by
    refine le_antisymm ((pi_norm_le_iff_of_nonneg (by norm_num)).mpr ?_) ?_
    · intro i
      fin_cases i <;> norm_num [Real.norm_eq_abs]
    · simpa using norm_le_pi_norm (![1, 3 / 2, 2] : V) (2 : Fin 3)
  have hUnit : IsUnit (![1, 3 / 2, 2] : V) := by
    rw [Pi.isUnit_iff]
    intro i
    fin_cases i <;> norm_num [isUnit_iff_ne_zero]
  have hInvVec : ((![1, 3 / 2, 2] : V)⁻¹ʳ) = ![1, 2 / 3, 1 / 2] := by
    symm
    rw [← one_mul ((![1, 3 / 2, 2] : V)⁻¹ʳ)]
    apply (Ring.eq_mul_inverse_iff_mul_eq _ _ _ hUnit).mpr
    funext i
    fin_cases i <;> norm_num [Pi.mul_apply]
  have hInv : ‖((![1, 3 / 2, 2] : V)⁻¹ʳ)‖ = 1 := by
    rw [hInvVec]
    refine le_antisymm ((pi_norm_le_iff_of_nonneg (by norm_num)).mpr ?_) ?_
    · intro i
      fin_cases i <;> norm_num [Real.norm_eq_abs]
    · simpa using norm_le_pi_norm (![1, 2 / 3, 1 / 2] : V) (0 : Fin 3)
  rw [hDiag, hInv, mul_one]

private theorem rayleigh_formula (x : V) :
    rayleigh exampleMatrix x =
      (x 0 ^ 2 + (3 / 2) * x 1 ^ 2 + 2 * x 2 ^ 2) /
        (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2) := by
  simp only [rayleigh, exampleMatrix, Matrix.mulVec_diagonal, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  congr 1 <;> ring

theorem first_error_pos (x : V) (hx : x 0 ≠ 0) :
    0 < relativeError 2 (rayleigh exampleMatrix x) := by
  rw [rayleigh_formula]
  have hpos : 0 < x 0 ^ 2 := sq_pos_of_ne_zero hx
  have hden : 0 < x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := by
    linarith [sq_nonneg (x 1), sq_nonneg (x 2)]
  have hquot : (x 0 ^ 2 + (3 / 2) * x 1 ^ 2 + 2 * x 2 ^ 2) /
      (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2) < 2 :=
    (div_lt_iff₀ hden).mpr (by nlinarith [sq_nonneg (x 1)])
  unfold relativeError
  apply div_pos
  · exact abs_pos.mpr (sub_ne_zero.mpr (ne_of_gt hquot))
  · norm_num

private theorem factor_neg : 1 - 2 / Real.sqrt (conditionNumber exampleMatrix) < 0 := by
  rw [example_conditionNumber, sub_neg, lt_div_iff₀ (Real.sqrt_pos.2 (by norm_num))]
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  nlinarith [Real.sqrt_nonneg 2]

/-- The second Krylov vector does not lie in the first Krylov subspace. -/
theorem second_step_exists (x : V) (h₀ : x 0 ≠ 0) (h₁ : x 1 ≠ 0) :
    exampleMatrix *ᵥ x ∉ Submodule.span ℝ ({x} : Set V) := by
  intro h
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp h
  have ha₀ : a * x 0 = 1 * x 0 := by
    simpa [exampleMatrix, Matrix.mulVec_diagonal] using congrFun ha (0 : Fin 3)
  have ha₁ : a * x 1 = (3 / 2) * x 1 := by
    simpa [exampleMatrix, Matrix.mulVec_diagonal] using congrFun ha (1 : Fin 3)
  have hEq₀ := mul_right_cancel₀ h₀ ha₀
  have hEq₁ := mul_right_cancel₀ h₁ ha₁
  linarith

/-- The lower bound zero for the next error is already enough to refute the
proposed upper bound, whose right side is strictly negative. -/
theorem conjecture_00000008785_false (x : V) (h₀ : x 0 ≠ 0) (h₁ : x 1 ≠ 0)
    (RemainingClaims : Prop) :
    exampleMatrix *ᵥ x ∉ Submodule.span ℝ ({x} : Set V) ∧
      ¬ (FactorBoundAtStart exampleMatrix 2 x ∧ RemainingClaims) := by
  refine ⟨second_step_exists x h₀ h₁, ?_⟩
  rintro ⟨h, _⟩
  have hnext : 0 ≤ relativeError 2 (largestRitz exampleMatrix (krylov₂ exampleMatrix x)) :=
    div_nonneg (abs_nonneg _) (abs_nonneg _)
  exact (not_le_of_gt (mul_neg_of_neg_of_pos factor_neg (first_error_pos x h₀))) (hnext.trans h)

#print axioms conjecture_00000008785_false

end Submission00000008785
