import TLMC69.Kernel

noncomputable section
open Polynomial MeasureTheory Set Filter
open scoped BigOperators Topology
namespace TLMC69

/-- Polynomial antiderivative with constant coefficient zero. -/
def primitive (p : ℝ[X]) : ℝ[X] :=
  ∑ i ∈ p.support, monomial (i+1) (p.coeff i / (i+1))

lemma derivative_primitive (p : ℝ[X]) : (primitive p).derivative = p := by
  rw [primitive, derivative_sum]
  simp_rw [derivative_monomial_succ]
  have hh : ∀ i : ℕ, (p.coeff i / ((i:ℝ)+1)) * ((i:ℝ)+1) = p.coeff i := by
    intro i; field_simp
  simp_rw [hh]
  exact p.sum_monomial_eq

lemma primitive_zero (p : ℝ[X]) : (primitive p).eval 0 = 0 := by
  simp [primitive, eval_finset_sum, eval_monomial]

lemma primitive_deriv (p : ℝ[X]) (x : ℝ) :
    HasDerivAt (fun y => (primitive p).eval y) (p.eval x) x := by
  simpa [derivative_primitive] using (primitive p).hasDerivAt x

lemma primitive_integral (p : ℝ[X]) (x : ℝ) :
    (primitive p).eval x = ∫ t in (0:ℝ)..x, p.eval t := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => primitive_deriv p t) (p.continuous.intervalIntegrable _ _), primitive_zero, sub_zero]

lemma primitive_degree (p : ℝ[X]) : (primitive p).natDegree ≤ p.natDegree + 1 := by
  apply natDegree_sum_le_of_forall_le
  intro i hi
  exact (natDegree_monomial_le _).trans (Nat.add_le_add_right (le_natDegree_of_ne_zero (mem_support_iff.mp hi)) 1)

lemma primitive_odd (p : ℝ[X]) (hp : ∀ x : ℝ, p.eval (-x) = p.eval x) (x : ℝ) :
    (primitive p).eval (-x) = -(primitive p).eval x := by
  rw [primitive_integral, primitive_integral]
  have h := intervalIntegral.integral_comp_neg (a := (0:ℝ)) (b := x) (fun t => p.eval t)
  simp only [neg_zero, hp] at h
  rw [intervalIntegral.integral_symm 0 (-x)] at h
  linarith

end TLMC69
