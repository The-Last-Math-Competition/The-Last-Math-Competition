import Mathlib

namespace Submission00000008785

open Matrix MeasureTheory
open scoped Matrix.Norms.L2Operator Pointwise Ring

abbrev V := Fin 3 → ℝ
abbrev M := Matrix (Fin 3) (Fin 3) ℝ

noncomputable def rayleigh (A : M) (x : V) : ℝ :=
  (x ⬝ᵥ (A *ᵥ x)) / (x ⬝ᵥ x)

def krylov₁ (x : V) : Submodule ℝ V :=
  Submodule.span ℝ ({x} : Set V)

def krylov₂ (A : M) (x : V) : Submodule ℝ V :=
  Submodule.span ℝ ({x, A *ᵥ x} : Set V)

def ritzValues (A : M) (K : Submodule ℝ V) : Set ℝ :=
  {r | ∃ y ∈ K, y ≠ 0 ∧ rayleigh A y = r}

noncomputable def largestRitz (A : M) (K : Submodule ℝ V) : ℝ :=
  sSup (ritzValues A K)

private theorem rayleigh_smul (A : M) (x : V) {a : ℝ} (ha : a ≠ 0) :
    rayleigh A (a • x) = rayleigh A x := by
  simp only [rayleigh, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  simp_rw [← mul_assoc]
  exact mul_div_mul_left _ _ (mul_ne_zero ha ha)

/-- The supremum is attained whenever the subspace contains a nonzero vector. -/
theorem largestRitz_isGreatest (A : M) (K : Submodule ℝ V)
    {x : V} (hxK : x ∈ K) (hx : x ≠ 0) :
    IsGreatest (ritzValues A K) (largestRitz A K) := by
  -- Any norm sphere can be used because the quotient is scale invariant.
  let S : Set V := Metric.sphere 0 1 ∩ (K : Set V)
  have normalize_mem {y : V} (hyK : y ∈ K) (hy : y ≠ 0) : ‖y‖⁻¹ • y ∈ S := by
    refine ⟨?_, K.smul_mem _ hyK⟩
    rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_of_nonneg
      (inv_nonneg.mpr (norm_nonneg y)), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hy)]
  have hcompact : IsCompact S := (isCompact_sphere _ _).inter_right K.closed_of_finiteDimensional
  have hcontinuous : ContinuousOn (rayleigh A) S := by
    apply (continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_id)).continuousOn.div
      (continuous_id.dotProduct continuous_id).continuousOn
    intro y hy
    have hyne : y ≠ 0 := Metric.ne_of_mem_sphere hy.1 (by norm_num)
    exact fun h => hyne (dotProduct_self_eq_zero.mp h)
  obtain ⟨v, hv, hvmax⟩ := hcompact.exists_isMaxOn ⟨_, normalize_mem hxK hx⟩ hcontinuous
  have hmax : IsGreatest (ritzValues A K) (rayleigh A v) := by
    refine ⟨⟨v, hv.2, Metric.ne_of_mem_sphere hv.1 (by norm_num), rfl⟩, ?_⟩
    rintro _ ⟨y, hyK, hy, rfl⟩
    have hle : rayleigh A (‖y‖⁻¹ • y) ≤ rayleigh A v := hvmax (normalize_mem hyK hy)
    rwa [rayleigh_smul A y (inv_ne_zero (norm_ne_zero_iff.mpr hy))] at hle
  rw [largestRitz, hmax.csSup_eq]
  exact hmax

theorem firstRitz_eq_rayleigh (A : M) {x : V} (hx : x ≠ 0) :
    largestRitz A (krylov₁ x) = rayleigh A x := by
  have hxK : x ∈ krylov₁ x := Submodule.subset_span (Set.mem_singleton x)
  have h := (largestRitz_isGreatest A (krylov₁ x) hxK hx).1
  obtain ⟨y, hyK, hy, hRitz⟩ := h
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hyK
  have ha : a ≠ 0 := by
    rintro rfl
    exact hy (zero_smul ℝ x)
  exact hRitz.symm.trans (rayleigh_smul A x ha)

theorem secondRitz_isGreatest (A : M) {x : V} (hx : x ≠ 0) :
    IsGreatest (ritzValues A (krylov₂ A x)) (largestRitz A (krylov₂ A x)) :=
  largestRitz_isGreatest A _ (Submodule.subset_span (by simp)) hx

noncomputable def relativeError (target approx : ℝ) : ℝ :=
  |target - approx| / |target|

noncomputable def conditionNumber (A : M) : ℝ := ‖A‖ * ‖A⁻¹‖

/-- Even the claimed factor as an upper bound on the next nonnegative
relative error would entail this statement at the first Lanczos update. -/
def FactorBoundAtStart (A : M) (target : ℝ) (x : V) : Prop :=
  relativeError target (largestRitz A (krylov₂ A x)) ≤
    (1 - 2 / Real.sqrt (conditionNumber A)) *
      relativeError target (largestRitz A (krylov₁ x))

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
    0 < relativeError 2 (largestRitz exampleMatrix (krylov₁ x)) := by
  have hne : x ≠ 0 := fun h => hx (congrFun h 0)
  rw [firstRitz_eq_rayleigh _ hne, rayleigh_formula]
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

/-- An asymptotic ratio of nonnegative errors also cannot equal the claimed factor. -/
theorem asymptoticFactor_ne (error : ℕ → ℝ) (hnonneg : ∀ k, 0 ≤ error k) :
    ¬ Filter.Tendsto (fun k => error (k + 1) / error k) Filter.atTop
      (nhds (1 - 2 / Real.sqrt (conditionNumber exampleMatrix))) := by
  intro h
  have hlimit : 0 ≤ 1 - 2 / Real.sqrt (conditionNumber exampleMatrix) :=
    ge_of_tendsto h (Filter.Eventually.of_forall fun k => div_nonneg (hnonneg _) (hnonneg _))
  exact (not_le_of_gt factor_neg) hlimit

/-- The second Krylov vector does not lie in the first Krylov subspace. -/
theorem second_step_exists (x : V) (h₀ : x 0 ≠ 0) (h₁ : x 1 ≠ 0) :
    exampleMatrix *ᵥ x ∉ krylov₁ x := by
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
theorem factorBoundAtStart_fails (x : V) (h₀ : x 0 ≠ 0) :
    ¬ FactorBoundAtStart exampleMatrix 2 x := by
  intro h
  have hnext : 0 ≤ relativeError 2 (largestRitz exampleMatrix (krylov₂ exampleMatrix x)) :=
    div_nonneg (abs_nonneg _) (abs_nonneg _)
  exact (not_le_of_gt (mul_neg_of_neg_of_pos factor_neg (first_error_pos x h₀))) (hnext.trans h)

abbrev E := EuclideanSpace ℝ (Fin 3)
abbrev UnitSphere := Metric.sphere (0 : E) 1

local instance : Nonempty UnitSphere :=
  ⟨⟨PiLp.single 2 0 (1 : ℝ), by
    rw [Metric.mem_sphere, dist_zero_right, PiLp.norm_single]
    exact norm_one⟩⟩

private noncomputable def sphereArea : FiniteMeasure UnitSphere :=
  ⟨(volume : Measure E).toSphere, inferInstance⟩

/-- Uniform sampling from the Euclidean unit sphere, using normalized surface area. -/
noncomputable def uniformStart : ProbabilityMeasure UnitSphere :=
  sphereArea.normalize

private theorem sphereArea_ne_zero : sphereArea ≠ 0 := by
  intro h
  exact (volume : Measure E).toSphere_ne_zero
    (congrArg (fun μ : FiniteMeasure UnitSphere => (μ : Measure UnitSphere)) h)

private theorem coordinate_ne_zero_ae (i : Fin 3) :
    ∀ᵐ u ∂(uniformStart : Measure UnitSphere), u.val i ≠ 0 := by
  let P := (PiLp.projₗ (𝕜 := ℝ) (p := 2) (β := fun _ : Fin 3 => ℝ) i).ker
  have hP : P ≠ ⊤ := by
    intro h
    have hmem : PiLp.single 2 i (1 : ℝ) ∈ P := by simp [h]
    simp [P, LinearMap.mem_ker] at hmem
  let Z : Set UnitSphere := Subtype.val ⁻¹' (P : Set E)
  have hZ : MeasurableSet Z :=
    P.closed_of_finiteDimensional.measurableSet.preimage measurable_subtype_coe
  have hcone : Set.Ioo (0 : ℝ) 1 • (Subtype.val '' Z) ⊆ (P : Set E) := by
    rintro _ ⟨r, _, _, ⟨u, hu, rfl⟩, rfl⟩
    exact P.smul_mem r hu
  have hnull : (volume : Measure E).toSphere Z = 0 := by
    rw [Measure.toSphere_apply' _ hZ,
      measure_mono_null hcone (Measure.addHaar_submodule volume P hP), mul_zero]
  rw [ae_iff]
  change (uniformStart : Measure UnitSphere) {u | ¬u.val i ≠ 0} = 0
  have heq : {u : UnitSphere | ¬u.val i ≠ 0} = Z := by
    ext u
    simp [Z, P, LinearMap.mem_ker]
  rw [heq, uniformStart, sphereArea.toMeasure_normalize_eq_of_nonzero sphereArea_ne_zero,
    Measure.smul_apply]
  simp [sphereArea, hnull]

/-- With probability one the second step exists, the initial error is positive,
and the claimed single-step factor fails even as an upper bound. -/
theorem conjecture_00000008785_false :
    ∀ᵐ u ∂(uniformStart : Measure UnitSphere),
      exampleMatrix *ᵥ u.val.ofLp ∉ krylov₁ u.val.ofLp ∧
      IsGreatest (ritzValues exampleMatrix (krylov₂ exampleMatrix u.val.ofLp))
        (largestRitz exampleMatrix (krylov₂ exampleMatrix u.val.ofLp)) ∧
      0 < relativeError 2 (largestRitz exampleMatrix (krylov₁ u.val.ofLp)) ∧
      ¬ FactorBoundAtStart exampleMatrix 2 u.val.ofLp := by
  filter_upwards [coordinate_ne_zero_ae 0, coordinate_ne_zero_ae 1] with u h₀ h₁
  have hne : u.val.ofLp ≠ 0 := fun h => h₀ (congrFun h 0)
  exact ⟨second_step_exists _ h₀ h₁, secondRitz_isGreatest _ hne,
    first_error_pos _ h₀, factorBoundAtStart_fails _ h₀⟩

#print axioms largestRitz_isGreatest
#print axioms firstRitz_eq_rayleigh
#print axioms example_posDef
#print axioms example_topEigenvalue
#print axioms example_conditionNumber
#print axioms asymptoticFactor_ne
#print axioms conjecture_00000008785_false

end Submission00000008785
