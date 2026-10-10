import TLMC69.Primitive
import TLMC69.KernelIntegrals

noncomputable section
open Polynomial MeasureTheory Set Filter
open scoped BigOperators Topology
namespace TLMC69

/-- The ordinary unweighted Lebesgue L¹ error on [-1,1]. -/
def l1Error (p : ℝ[X]) : ℝ := ∫ x in (-1 : ℝ)..1, |abs x - p.eval x|

/-- The degree-constrained infimum over all real polynomials. -/
def bestError (n : ℕ) : ℝ := sInf {e : ℝ | ∃ p : ℝ[X], p.natDegree ≤ n ∧ e = l1Error p}

/-- Normalized polynomial integral of a nonnegative even kernel, times X. -/
def approximant (n : ℕ) : ℝ[X] := C (mass n)⁻¹ * (X * primitive (kernel n))

lemma approximant_eval (n : ℕ) (x : ℝ) :
    (approximant n).eval x = x * (primitive (kernel n)).eval x / mass n := by
  simp only [approximant, eval_mul, eval_C, eval_X]
  ring

lemma approximant_degree (n : ℕ) : (approximant n).natDegree ≤ 8*n+2 := by
  apply (natDegree_C_mul_le _ _).trans
  apply natDegree_mul_le.trans
  have h1 := primitive_degree (kernel n)
  have h2 := kernel_degree n
  simp only [natDegree_X]
  omega

lemma approximant_even (n : ℕ) (x : ℝ) :
    (approximant n).eval (-x) = (approximant n).eval x := by
  rw [approximant_eval, approximant_eval, primitive_odd _ (kernel_even n)]
  ring

lemma primitive_kernel_bounds (n : ℕ) {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) :
    0 ≤ (primitive (kernel n)).eval x ∧ (primitive (kernel n)).eval x ≤ mass n := by
  rw [primitive_integral]
  constructor
  · exact intervalIntegral.integral_nonneg_of_forall hx.1 (kernel_nonneg n)
  · exact intervalIntegral.integral_mono_interval (μ := volume) le_rfl hx.1 hx.2
      (Filter.Eventually.of_forall fun t => kernel_nonneg n t)
      ((kernel n).continuous.intervalIntegrable _ _)

lemma approximant_le (n : ℕ) {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) :
    (approximant n).eval x ≤ x := by
  rw [approximant_eval, div_le_iff₀ (mass_pos n)]
  exact mul_le_mul_of_nonneg_left (primitive_kernel_bounds n hx).2 hx.1

lemma even_integral (f : ℝ → ℝ) (hc : Continuous f) (he : ∀ x, f (-x) = f x) :
    (∫ x in (-1:ℝ)..1, f x) = 2 * ∫ x in (0:ℝ)..1, f x := by
  have h := intervalIntegral.integral_comp_neg (a := (0:ℝ)) (b := 1) f
  simp only [neg_zero, he] at h
  have h' := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ := volume) (-1) 0) (hc.intervalIntegrable 0 1)
  linarith

lemma approximant_error_exact (n : ℕ) : l1Error (approximant n) = moment n / mass n := by
  let A := primitive (kernel n)
  have hA : Continuous (fun x => A.eval x) := A.continuous
  have hK : Continuous (fun x => (kernel n).eval x) := (kernel n).continuous
  have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (a := (0:ℝ)) (b := 1)
    (u := fun x : ℝ => x^2) (u' := fun x => 2*x)
    (v := fun x : ℝ => A.eval x) (v' := fun x => (kernel n).eval x)
    (continuous_id.pow 2).continuousOn hA.continuousOn
    (by intro x _; convert (hasDerivAt_id x).pow 2 using 1; simp)
    (by intro x _; exact primitive_deriv _ _)
    ((continuous_const.mul continuous_id).intervalIntegrable _ _) (hK.intervalIntegrable _ _)
  have hAe : A.eval 1 = mass n := primitive_integral _ _
  simp only [one_pow, zero_pow (by norm_num : (2:ℕ) ≠ 0), one_mul, zero_mul, sub_zero, hAe] at hIBP
  have htwo : (∫ x in (0:ℝ)..1, (2*x)*A.eval x) = 2 * ∫ x in (0:ℝ)..1, x*A.eval x := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1; funext x; ring
  rw [htwo] at hIBP
  have herr : l1Error (approximant n) = 2 * ∫ x in (0:ℝ)..1, x - (approximant n).eval x := by
    rw [l1Error, even_integral _ ((continuous_abs.sub (approximant n).continuous).abs)
      (by intro x; rw [abs_neg, approximant_even])]
    congr 1
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hx
    dsimp only
    rw [abs_of_nonneg hx.1, abs_of_nonneg (sub_nonneg.mpr (approximant_le n hx))]
  rw [herr]
  rw [intervalIntegral.integral_sub (f := fun x : ℝ => x)
    (g := fun x : ℝ => (approximant n).eval x)
    (continuous_id.intervalIntegrable _ _) ((approximant n).continuous.intervalIntegrable _ _)]
  have hpint : (∫ x in (0:ℝ)..1, (approximant n).eval x) =
      (∫ x in (0:ℝ)..1, x*A.eval x) / mass n := by
    simp only [approximant_eval, A, intervalIntegral.integral_div]
  rw [hpint]
  have hid : (∫ x in (0:ℝ)..1, x) = 1/2 := by
    convert (integral_pow (a := (0:ℝ)) (b := 1) 1) using 1 <;> norm_num
  rw [hid]
  change (∫ x in (0:ℝ)..1, x^2*(kernel n).eval x) = _ at hIBP
  dsimp [moment]
  rw [hIBP]
  field_simp [(mass_pos n).ne']
  ring

end TLMC69
