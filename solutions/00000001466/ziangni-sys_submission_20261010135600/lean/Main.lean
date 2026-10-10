import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic

open MeasureTheory
namespace GaussianTriangle

noncomputable def A (t : ℝ) : ℝ := t ^ 2 / 2
noncomputable def density (t x : ℝ) : ℝ :=
  (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x-t)^2 / 2)

/-- These are actual nonnegative Gaussian densities. -/
theorem density_positive (t x : ℝ) : 0 < density t x := by
  unfold density
  positivity

/-- Every member of the family is normalized with respect to Lebesgue measure. -/
theorem normalized (t : ℝ) : (∫ x : ℝ, density t x) = 1 := by
  unfold density
  rw [integral_const_mul]
  rw [integral_sub_right_eq_self (fun x : ℝ => Real.exp (-x^2 / 2)) t]
  have h : (fun x : ℝ => Real.exp (-x^2 / 2)) =
      (fun x : ℝ => Real.exp (-(1/2 : ℝ) * x^2)) := by
    funext x
    congr 1
    ring
  rw [h, integral_gaussian]
  have hs : Real.sqrt (Real.pi / (1/2 : ℝ)) = Real.sqrt (2 * Real.pi) := by
    congr 1
    ring
  rw [hs]
  exact inv_mul_cancel₀ (ne_of_gt (Real.sqrt_pos.2 (by positivity)))

/-- Canonical exponential-family factorization, with statistic x and log partition A. -/
theorem exponential_family (t x : ℝ) :
    density t x = density 0 x * Real.exp (t*x - A t) := by
  unfold density A
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- The partition integral is exp(A(t)); A really is the log partition. -/
theorem partition (t : ℝ) :
    (∫ x : ℝ, density 0 x * Real.exp (t*x)) = Real.exp (A t) := by
  have hf : (fun x : ℝ => density 0 x * Real.exp (t*x)) =
      (fun x : ℝ => Real.exp (A t) * density t x) := by
    funext x
    rw [exponential_family t x, ← mul_assoc, mul_comm (Real.exp (A t)), mul_assoc,
      ← Real.exp_add]
    congr 2
    ring
  rw [hf, integral_const_mul, normalized, mul_one]

theorem log_partition (t : ℝ) :
    Real.log (∫ x : ℝ, density 0 x * Real.exp (t*x)) = A t := by
  rw [partition, Real.log_exp]

theorem derivative (t : ℝ) : HasDerivAt A t t := by
  convert ((hasDerivAt_id t).pow 2).div_const 2 using 1 <;> simp [A] <;> ring

/-- Bregman divergence of the genuine Gaussian log-partition, using its derivative. -/
noncomputable def D (s t : ℝ) : ℝ := A s - A t - deriv A t * (s-t)

theorem divergence_formula (s t : ℝ) : D s t = (s-t)^2 / 2 := by
  unfold D
  rw [(derivative t).deriv]
  unfold A
  ring

theorem divergence_nonnegative (s t : ℝ) : 0 ≤ D s t := by
  rw [divergence_formula]
  positivity

theorem divergence_zero_iff (s t : ℝ) : D s t = 0 ↔ s = t := by
  rw [divergence_formula]
  constructor
  · intro h
    nlinarith [sq_nonneg (s-t)]
  · intro h
    simp [h]

/-- A valid additive triangle correction at the witness must be at least one. -/
theorem correction_lower_bound (c : ℝ)
    (h : D 0 2 ≤ D 0 1 + D 1 2 + c) : 1 ≤ c := by
  simp only [divergence_formula] at h
  norm_num at h ⊢
  linarith

/-- The zero-correction triangle law fails for this normalized exponential family. -/
theorem no_zero_correction : ¬ (∀ s t u : ℝ, D s u ≤ D s t + D t u) := by
  intro h
  have hc := correction_lower_bound 0 (by simpa using h 0 1 2)
  norm_num at hc

#print axioms normalized
#print axioms exponential_family
#print axioms log_partition
#print axioms divergence_formula
#print axioms correction_lower_bound
#print axioms no_zero_correction
end GaussianTriangle
