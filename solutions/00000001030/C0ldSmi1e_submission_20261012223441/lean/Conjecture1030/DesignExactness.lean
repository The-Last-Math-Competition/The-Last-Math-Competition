import Conjecture1030.SurfaceMeasure
import Conjecture1030.SphereMoments
import Conjecture1030.LinearProgramming

noncomputable section
open scoped BigOperators ENNReal RealInnerProductSpace
open MeasureTheory Metric Set
namespace Conjecture1030
set_option maxHeartbeats 1200000

/-- The ambient polynomial giving the Euclidean inner product with a fixed pole. -/
def linearForm (x : E) : MvPolynomial (Fin 3) ℝ :=
  ∑ i : Fin 3, MvPolynomial.C (x i) * MvPolynomial.X i

 theorem linearForm_degree (x : E) : (linearForm x).totalDegree ≤ 1 := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i hi
  exact (MvPolynomial.totalDegree_mul _ _).trans (by simp)

 theorem eval_linearForm (x : E) (y : S2) :
    evalOnSphere (linearForm x) y = ⟪x, (y : E)⟫ := by
  simp [evalOnSphere, linearForm, inner3, Fin.sum_univ_succ, add_assoc, mul_comm]

/-- Dot-product moments are genuine sphere integrals, transported by a proved reflection. -/
 theorem dot_pow_integral_eq_coord (x : S2) (n : ℕ) :
    (∫ y : S2, ⟪(x : E), (y : E)⟫ ^ n ∂sigma) =
      ∫ y : S2, ((y : E) 0) ^ n ∂sigma := by
  let e : E := !₂[1, 0, 0]
  have he : ‖e‖ = 1 := by
    have h : ‖e‖ ^ 2 = 1 := by rw [norm_sq3]; norm_num [e, Matrix.cons_val_two]
    nlinarith [norm_nonneg e]
  let U : E ≃ₗᵢ[ℝ] E := (ℝ ∙ ((x : E) - e))ᗮ.reflection
  have hU : U (x : E) = e := Submodule.reflection_sub (by rw [sphere_norm, he])
  have hpoint (y : S2) : ⟪e, U (y : E)⟫ = ⟪(x : E), (y : E)⟫ := by
    rw [← hU, U.inner_map_map]
  have h := invariant_integral sigma sigma_orthogonallyInvariant U
    (fun y : S2 => ⟪e, (y : E)⟫ ^ n)
  simp only [sphereIso_coe, hpoint] at h
  have haxis (y : S2) : ⟪e, (y : E)⟫ = (y : E) 0 := by
    rw [inner3]
    norm_num [e, Matrix.cons_val_two]
  simpa only [haxis] using h

 theorem dot_pow_integral_le_five (x : S2) (n : ℕ) (hn : n ≤ 5) :
    (∫ y : S2, ⟪(x : E), (y : E)⟫ ^ n ∂sigma) =
      if n = 0 then 1 else if n = 2 then 1 / 3 else if n = 4 then 1 / 5 else 0 := by
  rw [dot_pow_integral_eq_coord]
  exact coord_pow_integral_le_five sigma sigma_orthogonallyInvariant 0 n hn

 theorem dot_pow_integrable (x : S2) (n : ℕ) :
    Integrable (fun y : S2 => ⟪(x : E), (y : E)⟫ ^ n) sigma := by
  apply integrable_sphere_continuous sigma
  fun_prop

 theorem design_sum_dot_pow (X : Finset S2) (hX : SphericalDesign 5 X)
    (x : S2) (n : ℕ) (hn : n ≤ 5) :
    ∑ y ∈ X, ⟪(x : E), (y : E)⟫ ^ n = (X.card : ℝ) *
      (if n = 0 then 1 else if n = 2 then 1 / 3 else if n = 4 then 1 / 5 else 0) := by
  have hp : ((linearForm (x : E)) ^ n).totalDegree ≤ 5 :=
    (MvPolynomial.totalDegree_pow _ _).trans ((Nat.mul_le_mul_left n (linearForm_degree (x : E))).trans (by simpa using hn))
  have heval (y : S2) : evalOnSphere ((linearForm (x : E)) ^ n) y =
      ⟪(x : E), (y : E)⟫ ^ n := by
    simp only [evalOnSphere, MvPolynomial.eval_pow]
    rw [← evalOnSphere, eval_linearForm]
  have hh := hX.2 _ hp
  simp_rw [heval] at hh
  rw [dot_pow_integral_le_five x n hn] at hh
  have hn0 : (X.card : ℝ) ≠ 0 := by exact_mod_cast (Finset.card_ne_zero.mpr hX.1)
  have hmul := congrArg (fun q : ℝ => (X.card : ℝ) * q) hh
  simpa only [← mul_assoc, mul_inv_cancel₀ hn0, one_mul] using hmul

/-- The exact LP sum is derived from full polynomial design exactness and surface integration. -/
 theorem design_sum_lpValue (X : Finset S2) (hX : SphericalDesign 5 X) (x : S2) :
    ∑ y ∈ X, lpValue ⟪(x : E), (y : E)⟫ = (8 / 3 : ℝ) * X.card := by
  have h1 := design_sum_dot_pow X hX x 1 (by norm_num)
  have h2 := design_sum_dot_pow X hX x 2 (by norm_num)
  have h3 := design_sum_dot_pow X hX x 3 (by norm_num)
  have h4 := design_sum_dot_pow X hX x 4 (by norm_num)
  have h5 := design_sum_dot_pow X hX x 5 (by norm_num)
  norm_num only [pow_one, mul_zero, ite_false, ite_true] at h1 h2 h3 h4 h5
  have hp (t : ℝ) : lpValue t = 25 * t ^ 5 + 25 * t ^ 4 - 10 * t ^ 3 -
      10 * t ^ 2 + t + 1 := by unfold lpValue; ring
  simp_rw [hp]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [h1, h2, h3, h4, h5]
  ring

 theorem spherical_five_design_card_ge_twelve (X : Finset S2)
    (hX : SphericalDesign 5 X) : 12 ≤ X.card := by
  obtain ⟨x, hx⟩ := hX.1
  exact card_ge_twelve_of_lp_sum X x hx (design_sum_lpValue X hX x)

end Conjecture1030
