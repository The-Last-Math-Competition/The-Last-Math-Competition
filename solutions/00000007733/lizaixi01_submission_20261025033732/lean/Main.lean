import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Lean.Elab.Tactic.Omega

/-!
The fixed-target, one-variable free Stein discrepancy is the infimum over
ALL complex L2 kernels satisfying ALL polynomial integration-by-parts tests.
The reference potential stays x^2/2.  No variance-one constraint is added to
the source's class of atomless laws supported in [-2,2].
-/

set_option linter.unusedSectionVars false

noncomputable section
open MeasureTheory Set Filter Polynomial
open scoped ENNReal BigOperators ComplexConjugate InnerProductSpace

namespace TLMC7733

/-- An actual semicircle density on [-1,1], before the variance-one scaling. -/
def density (x : ℝ) : ℝ := (2 / Real.pi) * Real.sqrt (1 - x ^ 2)

theorem density_nonneg (x : ℝ) : 0 ≤ density x := by
  unfold density
  positivity

theorem density_continuous : Continuous density := by
  unfold density
  fun_prop

def baseLaw : Measure ℝ :=
  (volume.restrict (Icc (-1) 1)).withDensity (fun x => ENNReal.ofReal (density x))

theorem density_integral :
    ∫ x, density x ∂volume.restrict (Icc (-1) 1) = 1 := by
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  unfold density
  rw [intervalIntegral.integral_const_mul, integral_sqrt_one_sub_sq]
  field_simp

instance baseLaw_probability : IsProbabilityMeasure baseLaw where
  measure_univ := by
    rw [baseLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    rw [← ofReal_integral_eq_lintegral_ofReal density_continuous.integrableOn_Icc
      (Eventually.of_forall density_nonneg), density_integral]
    norm_num

instance baseLaw_noAtoms : NullSingletonClass baseLaw := by
  unfold baseLaw
  infer_instance

theorem baseLaw_supported : ∀ᵐ x ∂baseLaw, x ∈ Icc (-1 : ℝ) 1 :=
  (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Icc)

theorem base_integrable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (hf : Continuous f) : Integrable f baseLaw := by
  rw [baseLaw, integrable_withDensity_iff_integrable_smul'
    (density_continuous.measurable.ennreal_ofReal)
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp_rw [ENNReal.toReal_ofReal (density_nonneg _)]
  exact (density_continuous.smul hf).integrableOn_Icc

theorem base_integral_real (f : ℝ → ℝ) :
    (∫ x, f x ∂baseLaw) =
      (2 / Real.pi) * ∫ x in (-1 : ℝ)..1, f x * Real.sqrt (1 - x ^ 2) := by
  rw [baseLaw, integral_withDensity_eq_integral_toReal_smul
    (density_continuous.measurable.ennreal_ofReal)
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp_rw [ENNReal.toReal_ofReal (density_nonneg _), smul_eq_mul]
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
    ← intervalIntegral.integral_const_mul]
  congr 1
  ext x
  simp only [density]
  ring

theorem sqrt_factor (x : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) :
    (1 - x ^ 2) * (Real.sqrt (1 - x ^ 2))⁻¹ = Real.sqrt (1 - x ^ 2) := by
  have hn : 0 ≤ 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
  calc
    (1 - x ^ 2) * (Real.sqrt (1 - x ^ 2))⁻¹ =
        Real.sqrt (1 - x ^ 2) ^ 2 * (Real.sqrt (1 - x ^ 2))⁻¹ := by
      rw [Real.sq_sqrt hn]
    _ = Real.sqrt (1 - x ^ 2) := by
      by_cases h : Real.sqrt (1 - x ^ 2) = 0
      · simp [h]
      · field_simp

theorem base_integral_chebyshev_weight (f : ℝ → ℝ) :
    (∫ x, f x ∂baseLaw) = (2 / Real.pi) *
      ∫ x, f x * (1 - x ^ 2) ∂Polynomial.Chebyshev.measureT := by
  rw [base_integral_real, Polynomial.Chebyshev.integral_measureT]
  congr 1
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hx
  dsimp only
  simp only [Real.sqrt_inv]
  rw [mul_assoc, sqrt_factor x hx]

theorem U_weight_identity (n : ℤ) :
    2 * (1 - (X : ℝ[X]) ^ 2) * Polynomial.Chebyshev.U ℝ n =
      Polynomial.Chebyshev.T ℝ n - Polynomial.Chebyshev.T ℝ (n + 2) := by
  have h1 := Polynomial.Chebyshev.one_sub_X_sq_mul_U_eq_pol_in_T ℝ n
  have h2 := Polynomial.Chebyshev.T_add_two ℝ n
  linear_combination 2 * h1 - h2

theorem base_U_integral (n : ℕ) :
    (∫ x, (Polynomial.Chebyshev.U ℝ n).eval x ∂baseLaw) = if n = 0 then 1 else 0 := by
  rw [base_integral_chebyshev_weight]
  have hp : (fun x : ℝ => (Polynomial.Chebyshev.U ℝ n).eval x * (1 - x ^ 2)) =
      fun x => ((Polynomial.Chebyshev.T ℝ n).eval x -
        (Polynomial.Chebyshev.T ℝ ((n : ℤ) + 2)).eval x) / 2 := by
    funext x
    have h := congrArg (Polynomial.eval x) (U_weight_identity n)
    simp only [eval_mul, eval_ofNat, eval_sub, eval_one, eval_pow, eval_X] at h
    linarith
  rw [hp, integral_div, integral_sub]
  · rw [Polynomial.Chebyshev.integral_eval_T_real_measureT_of_ne_zero
      (by omega : (n : ℤ) + 2 ≠ 0)]
    by_cases hn : n = 0
    · subst n
      norm_num only [Nat.cast_zero, if_pos rfl]
      rw [Polynomial.Chebyshev.integral_eval_T_real_measureT_zero]
      field_simp
      simp
    · rw [Polynomial.Chebyshev.integral_eval_T_real_measureT_of_ne_zero (by exact_mod_cast hn)]
      simp [hn]
  all_goals exact Polynomial.Chebyshev.integrable_measureT (by fun_prop)

/-- The native complex Chebyshev polynomials, evaluated at a real argument. -/
def u (n : ℕ) (x : ℝ) : ℂ := (Polynomial.Chebyshev.U ℂ n).eval (x : ℂ)

theorem u_zero (x : ℝ) : u 0 x = 1 := by simp [u]

theorem u_one (x : ℝ) : u 1 x = 2 * x := by simp [u]

theorem u_rec (n : ℕ) (x : ℝ) :
    u (n + 2) x = 2 * x * u (n + 1) x - u n x := by
  simp only [u, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one, Polynomial.Chebyshev.U_add_two,
    eval_sub, eval_mul, eval_ofNat, eval_X]

theorem u_ofReal (n : ℕ) (x : ℝ) :
    u n x = Complex.ofReal ((Polynomial.Chebyshev.U ℝ n).eval x) := by
  calc
    u n x = ((Polynomial.Chebyshev.U ℝ n).map Complex.ofRealHom).eval (x : ℂ) := by
      rw [Polynomial.Chebyshev.map_U]
      rfl
    _ = Complex.ofReal ((Polynomial.Chebyshev.U ℝ n).eval x) :=
      Polynomial.eval_map_apply (p := Polynomial.Chebyshev.U ℝ n) Complex.ofRealHom x

theorem u_continuous (n : ℕ) : Continuous (u n) := by
  unfold u
  fun_prop

theorem base_u_integral (n : ℕ) :
    (∫ x, u n x ∂baseLaw) = if n = 0 then 1 else 0 := by
  simp_rw [u_ofReal]
  rw [integral_complex_ofReal, base_U_integral]
  split_ifs <;> simp

/-- The actual polynomial divided difference, with the derivative on the diagonal. -/
def dividedDifference (p : ℂ[X]) (x y : ℝ) : ℂ :=
  if x = y then p.derivative.eval (x : ℂ)
  else (p.eval (x : ℂ) - p.eval (y : ℂ)) / ((x : ℂ) - y)

theorem dividedDifference_diagonal (p : ℂ[X]) (x : ℝ) :
    dividedDifference p x x = p.derivative.eval (x : ℂ) := by
  simp [dividedDifference]

theorem dividedDifference_add (p q : ℂ[X]) (x y : ℝ) :
    dividedDifference (p + q) x y = dividedDifference p x y + dividedDifference q x y := by
  by_cases h : x = y
  · simp [dividedDifference, h]
  · simp only [dividedDifference, if_neg h, eval_add]
    ring

theorem dividedDifference_smul (c : ℂ) (p : ℂ[X]) (x y : ℝ) :
    dividedDifference (c • p) x y = c * dividedDifference p x y := by
  by_cases h : x = y
  · simp [dividedDifference, h]
  · simp only [dividedDifference, if_neg h, eval_smul, smul_eq_mul]
    ring

theorem dividedDifference_zero (x y : ℝ) : dividedDifference 0 x y = 0 := by
  simp [dividedDifference]

theorem dividedDifference_X (x y : ℝ) : dividedDifference X x y = 1 := by
  by_cases h : x = y
  · simp [dividedDifference, h]
  · simp [dividedDifference, h, sub_ne_zero.mpr (Complex.ofReal_injective.ne h)]

/-- A finite bivariate polynomial, later identified with the genuine divided difference. -/
def convolution (n : ℕ) (x y : ℝ) : ℂ :=
  ∑ i ∈ Finset.range (n + 1), u i x * u (n - i) y

theorem convolution_zero (x y : ℝ) : convolution 0 x y = 1 := by
  simp [convolution, u_zero]

theorem convolution_one (x y : ℝ) : convolution 1 x y = 2 * x + 2 * y := by
  simp [convolution, Finset.sum_range_succ, u_zero, u_one, add_comm]

theorem convolution_rec (n : ℕ) (x y : ℝ) :
    convolution (n + 2) x y =
      2 * y * convolution (n + 1) x y - convolution n x y + u (n + 2) x := by
  have hterm : ∀ i ∈ Finset.range (n + 1),
      u i x * u (n + 2 - i) y =
        2 * y * (u i x * u (n + 1 - i) y) - u i x * u (n - i) y := by
    intro i hi
    have hi' : i ≤ n := by simpa using hi
    rw [show n + 2 - i = (n - i) + 2 by omega,
      show n + 1 - i = (n - i) + 1 by omega, u_rec]
    ring
  have hs : (∑ i ∈ Finset.range (n + 1), u i x * u (n + 2 - i) y) =
      2 * y * (∑ i ∈ Finset.range (n + 1), u i x * u (n + 1 - i) y) -
        convolution n x y := by
    simp_rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rfl
  have h1 : convolution (n + 1) x y =
      (∑ i ∈ Finset.range (n + 1), u i x * u (n + 1 - i) y) + u (n + 1) x := by
    simp only [convolution, Finset.sum_range_succ, Nat.sub_self, u_zero, mul_one]
  have h2 : convolution (n + 2) x y =
      (∑ i ∈ Finset.range (n + 1), u i x * u (n + 2 - i) y) +
        u (n + 1) x * (2 * y) + u (n + 2) x := by
    simp only [convolution, show n + 2 + 1 = (n + 1) + 1 + 1 by omega,
      Finset.sum_range_succ, Nat.sub_self, u_zero, mul_one,
      show n + 2 - (n + 1) = 1 by omega, u_one]
  rw [h2, hs, h1]
  ring

theorem convolution_difference (n : ℕ) (x y : ℝ) :
    2 * ((x : ℂ) - y) * convolution n x y = u (n + 1) x - u (n + 1) y := by
  induction n using Nat.twoStepInduction with
  | zero => simp [convolution_zero, u_one]; ring
  | one => simp [convolution_one, u_rec, u_zero, u_one]; ring
  | more n ih1 ih2 =>
    rw [convolution_rec]
    have hx := u_rec (n + 1) x
    have hy := u_rec (n + 1) y
    linear_combination 2 * (y : ℂ) * ih2 - ih1 - hx + hy

theorem dividedDifference_U_of_ne (n : ℕ) {x y : ℝ} (h : x ≠ y) :
    dividedDifference (Polynomial.Chebyshev.U ℂ (n + 1)) x y =
      2 * convolution n x y := by
  rw [dividedDifference, if_neg h]
  change (u (n + 1) x - u (n + 1) y) / ((x : ℂ) - y) = _
  rw [← convolution_difference]
  field_simp [sub_ne_zero.mpr (Complex.ofReal_injective.ne h)]

theorem base_memLp {E : Type*} [NormedAddCommGroup E] {f : ℝ → E}
    (hf : Continuous f) (p : ℝ≥0∞) : MemLp f p baseLaw := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.image hf.norm).bddAbove
  exact MemLp.of_bound hf.aestronglyMeasurable C (baseLaw_supported.mono fun x hx =>
    hC ⟨x, hx, rfl⟩)

theorem base_product_supported :
    ∀ᵐ z ∂baseLaw.prod baseLaw, z ∈ (Icc (-1 : ℝ) 1) ×ˢ Icc (-1 : ℝ) 1 := by
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_Icc.prod measurableSet_Icc)).mpr
  filter_upwards [baseLaw_supported] with x hx
  exact baseLaw_supported.mono fun _ hy => ⟨hx, hy⟩

theorem base_product_memLp {f : ℝ × ℝ → ℂ} (hf : Continuous f) (p : ℝ≥0∞) :
    MemLp f p (baseLaw.prod baseLaw) := by
  obtain ⟨C, hC⟩ := ((isCompact_Icc.prod isCompact_Icc).image hf.norm).bddAbove
  exact MemLp.of_bound hf.aestronglyMeasurable C (base_product_supported.mono fun z hz =>
    hC ⟨z, hz, rfl⟩)

theorem base_product_off_diagonal : ∀ᵐ z ∂baseLaw.prod baseLaw, z.1 ≠ z.2 := by
  apply (Measure.ae_prod_iff_ae_ae (isClosed_eq continuous_fst continuous_snd).measurableSet.compl).mpr
  exact Eventually.of_forall fun x => (baseLaw.ae_ne x).mono fun _ hy => hy.symm

theorem convolution_continuous (n : ℕ) :
    Continuous (fun z : ℝ × ℝ => convolution n z.1 z.2) := by
  unfold convolution
  exact continuous_finsetSum _ fun i _ => (u_continuous i).comp continuous_fst |>.mul
    ((u_continuous (n - i)).comp continuous_snd)

theorem convolution_integral (n : ℕ) :
    (∫ z, convolution n z.1 z.2 ∂baseLaw.prod baseLaw) = if n = 0 then 1 else 0 := by
  change (∫ z, ∑ i ∈ Finset.range (n + 1), u i z.1 * u (n - i) z.2
    ∂baseLaw.prod baseLaw) = _
  rw [integral_finsetSum]
  · simp_rw [integral_prod_mul, base_u_integral, ite_mul, one_mul, zero_mul]
    simp
  · intro i hi
    exact (base_integrable (u_continuous i)).mul_prod
      (base_integrable (u_continuous (n - i)))

theorem base_centered : (∫ x : ℝ, (x : ℂ) ∂baseLaw) = 0 := by
  have h := base_u_integral 1
  simp only [u_one, integral_const_mul, if_neg (by omega : (1 : ℕ) ≠ 0)] at h
  linear_combination h / 2

theorem base_coordinate_U_integral (n : ℕ) :
    (∫ x : ℝ, (x : ℂ) * u (n + 1) x ∂baseLaw) = if n = 0 then 1 / 2 else 0 := by
  have hp : (fun x : ℝ => (x : ℂ) * u (n + 1) x) =
      fun x => (u (n + 2) x + u n x) / 2 := by
    funext x
    have h := u_rec n x
    linear_combination -h / 2
  rw [hp, integral_div, integral_add (base_integrable (u_continuous _))
    (base_integrable (u_continuous _)), base_u_integral, base_u_integral]
  by_cases hn : n = 0 <;> simp [hn]

/-- A submodule of ALL complex polynomials: bounded genuine tests and the true identity. -/
def baseTestSpace : Submodule ℂ ℂ[X] where
  carrier := {p | MemLp (fun z : ℝ × ℝ => dividedDifference p z.1 z.2) ∞
      (baseLaw.prod baseLaw) ∧
    (∫ x : ℝ, (x : ℂ) * p.eval (x : ℂ) ∂baseLaw) =
      (1 / 4 : ℂ) * ∫ z, dividedDifference p z.1 z.2 ∂baseLaw.prod baseLaw}
  zero_mem' := by simp [dividedDifference]
  add_mem' := by
    intro p q hp hq
    constructor
    · convert hp.1.add hq.1 using 1
      funext z
      exact dividedDifference_add p q z.1 z.2
    · simp only [eval_add, mul_add, dividedDifference_add]
      rw [integral_add (base_integrable (by fun_prop)) (base_integrable (by fun_prop)),
        integral_add (hp.1.integrable (by simp)) (hq.1.integrable (by simp)), hp.2, hq.2]
      ring
  smul_mem' := by
    intro c p hp
    constructor
    · simpa only [dividedDifference_smul] using hp.1.const_mul c
    · simp only [eval_smul, smul_eq_mul, dividedDifference_smul]
      have hc (x : ℝ) : (x : ℂ) * (c * p.eval (x : ℂ)) =
          c * ((x : ℂ) * p.eval (x : ℂ)) := by ring
      simp_rw [hc]
      rw [integral_const_mul, integral_const_mul, hp.2]
      ring

theorem U_mem_baseTestSpace (n : ℕ) : Polynomial.Chebyshev.U ℂ n ∈ baseTestSpace := by
  cases n with
  | zero =>
    change MemLp _ ∞ _ ∧ _
    simp only [Nat.cast_zero, Polynomial.Chebyshev.U_zero, derivative_one, eval_zero,
      eval_one, sub_self, zero_div, ite_self, mul_one, integral_zero, mul_zero,
      dividedDifference]
    exact ⟨memLp_const 0, base_centered⟩
  | succ n =>
    have hae : (fun z : ℝ × ℝ => dividedDifference (Polynomial.Chebyshev.U ℂ (n + 1 : ℕ)) z.1 z.2) =ᵐ[baseLaw.prod baseLaw]
        fun z => 2 * convolution n z.1 z.2 :=
      base_product_off_diagonal.mono fun _ hz => by
        simpa only [Nat.cast_add, Nat.cast_one] using dividedDifference_U_of_ne n hz
    constructor
    · exact (base_product_memLp (continuous_const.mul (convolution_continuous n)) ∞).ae_eq hae.symm
    · change (∫ x, (x : ℂ) * u (n + 1) x ∂baseLaw) = _
      rw [base_coordinate_U_integral, integral_congr_ae hae, integral_const_mul,
        convolution_integral]
      split_ifs <;> norm_num

def USequence : Polynomial.Sequence ℂ where
  elems' n := Polynomial.Chebyshev.U ℂ n
  degree_eq' n := Polynomial.Chebyshev.degree_U_natCast ℂ n

theorem all_base_tests (p : ℂ[X]) : p ∈ baseTestSpace := by
  have hc : ∀ i : ℕ, IsUnit (USequence i).leadingCoeff := by
    intro i
    apply isUnit_iff_ne_zero.mpr
    exact leadingCoeff_ne_zero.mpr (Polynomial.Chebyshev.U_ne_zero ℂ i (by omega))
  have hs : (⊤ : Submodule ℂ ℂ[X]) ≤ baseTestSpace := by
    rw [← USequence.span hc]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact U_mem_baseTestSpace i
  exact hs (Submodule.mem_top)

theorem base_free_integration_by_parts (p : ℂ[X]) :
    (∫ x : ℝ, (x : ℂ) * p.eval (x : ℂ) ∂baseLaw) =
      (1 / 4 : ℂ) * ∫ z, dividedDifference p z.1 z.2 ∂baseLaw.prod baseLaw :=
  (all_base_tests p).2

/-- The genuine dilation pushforward; its variance will be proved to be s^2. -/
def law (s : ℝ) : Measure ℝ := Measure.map (fun x : ℝ => 2 * s * x) baseLaw

instance law_probability (s : ℝ) : IsProbabilityMeasure (law s) where
  measure_univ := by
    rw [law, Measure.map_apply (by fun_prop) MeasurableSet.univ]
    simp

theorem law_noAtoms {s : ℝ} (hs : s ≠ 0) : NullSingletonClass (law s) where
  measure_singleton a := by
    rw [law, Measure.map_apply (by fun_prop) (measurableSet_singleton a)]
    apply Set.Subsingleton.measure_zero
    intro x hx y hy
    have hx' : 2 * s * x = a := by simpa using hx
    have hy' : 2 * s * y = a := by simpa using hy
    exact mul_left_cancel₀ (mul_ne_zero (by norm_num) hs) (hx'.trans hy'.symm)

theorem law_supported {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    ∀ᵐ x ∂law s, x ∈ Icc (-2 : ℝ) 2 := by
  unfold law
  apply (ae_map_iff (by fun_prop) (show MeasurableSet {x : ℝ | x ∈ Icc (-2 : ℝ) 2} from
    measurableSet_Icc)).mpr
  filter_upwards [baseLaw_supported] with x hx
  have h1 := mul_le_mul_of_nonneg_left hx.1 (show 0 ≤ 2 * s by positivity)
  have h2 := mul_le_mul_of_nonneg_left hx.2 (show 0 ≤ 2 * s by positivity)
  constructor <;> nlinarith

theorem law_memLp (s : ℝ) {E : Type*} [NormedAddCommGroup E] {f : ℝ → E}
    (hf : Continuous f) (p : ℝ≥0∞) : MemLp f p (law s) := by
  apply (memLp_map_measure_iff hf.aestronglyMeasurable (by fun_prop)).mpr
  exact base_memLp (by fun_prop) p

theorem law_integrable (s : ℝ) {E : Type*} [NormedAddCommGroup E] {f : ℝ → E}
    (hf : Continuous f) : Integrable f (law s) :=
  (law_memLp s hf 1).integrable le_rfl

theorem law_integral (s : ℝ) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {f : ℝ → E} (hf : Continuous f) :
    (∫ x, f x ∂law s) = ∫ x, f (2 * s * x) ∂baseLaw := by
  rw [law, integral_map (by fun_prop) hf.aestronglyMeasurable]

theorem dividedDifference_measurable (p : ℂ[X]) :
    Measurable (fun z : ℝ × ℝ => dividedDifference p z.1 z.2) := by
  unfold dividedDifference
  exact Measurable.ite (isClosed_eq continuous_fst continuous_snd).measurableSet
    (by fun_prop) (by fun_prop)

def scaledPolynomial (s : ℝ) (p : ℂ[X]) : ℂ[X] := p.comp (C (2 * s : ℂ) * X)

theorem scaledPolynomial_eval (s : ℝ) (p : ℂ[X]) (x : ℝ) :
    (scaledPolynomial s p).eval (x : ℂ) = p.eval (Complex.ofReal (2 * s * x)) := by
  simp [scaledPolynomial, eval_comp, Complex.ofReal_mul]

theorem scaledPolynomial_derivative_eval (s : ℝ) (p : ℂ[X]) (x : ℝ) :
    (scaledPolynomial s p).derivative.eval (x : ℂ) =
      (2 * s : ℂ) * p.derivative.eval (Complex.ofReal (2 * s * x)) := by
  simp [scaledPolynomial, derivative_comp, derivative_mul, eval_comp,
    Complex.ofReal_mul, mul_comm]

theorem scaledPolynomial_dividedDifference {s : ℝ} (hs : s ≠ 0) (p : ℂ[X]) (x y : ℝ) :
    dividedDifference (scaledPolynomial s p) x y =
      (2 * s : ℂ) * dividedDifference p (2 * s * x) (2 * s * y) := by
  by_cases h : x = y
  · subst y
    simp [dividedDifference, scaledPolynomial_derivative_eval]
  · have hh : 2 * s * x ≠ 2 * s * y := by
      intro hh
      exact h (mul_left_cancel₀ (mul_ne_zero (by norm_num) hs) hh)
    simp only [dividedDifference, if_neg h, if_neg hh, scaledPolynomial_eval]
    push_cast
    have hc : (2 * s : ℂ) ≠ 0 := by exact_mod_cast mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hs
    have hsC : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs
    field_simp [hc, hsC, sub_ne_zero.mpr (Complex.ofReal_injective.ne h)]

theorem law_product_integral (s : ℝ) {f : ℝ × ℝ → ℂ} (hf : Measurable f) :
    (∫ z, f z ∂(law s).prod (law s)) =
      ∫ z : ℝ × ℝ, f (2 * s * z.1, 2 * s * z.2) ∂baseLaw.prod baseLaw := by
  rw [law, Measure.map_prod_map baseLaw baseLaw (by fun_prop) (by fun_prop),
    integral_map (by fun_prop) hf.aestronglyMeasurable]
  rfl

theorem law_dividedDifference_memLp {s : ℝ} (hs : s ≠ 0) (p : ℂ[X]) (q : ℝ≥0∞) :
    MemLp (fun z : ℝ × ℝ => dividedDifference p z.1 z.2) q ((law s).prod (law s)) := by
  rw [law, Measure.map_prod_map baseLaw baseLaw (by fun_prop) (by fun_prop)]
  apply (memLp_map_measure_iff (dividedDifference_measurable p).aestronglyMeasurable
    (by fun_prop)).mpr
  have hc : (2 * s : ℂ) ≠ 0 := by exact_mod_cast mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hs
  have h := ((all_base_tests (scaledPolynomial s p)).1.mono_exponent (le_top : q ≤ ∞)).const_mul (2 * s : ℂ)⁻¹
  convert h using 1
  funext z
  dsimp only [Function.comp_apply, Prod.map_fst, Prod.map_snd]
  rw [scaledPolynomial_dividedDifference hs, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]

theorem law_free_integration_by_parts {s : ℝ} (hs : s ≠ 0) (p : ℂ[X]) :
    (∫ x : ℝ, (x : ℂ) * p.eval (x : ℂ) ∂law s) =
      (s ^ 2 : ℝ) * ∫ z, dividedDifference p z.1 z.2 ∂(law s).prod (law s) := by
  rw [law_integral s (by fun_prop), law_product_integral s (dividedDifference_measurable p)]
  have h := base_free_integration_by_parts (scaledPolynomial s p)
  simp_rw [scaledPolynomial_eval, scaledPolynomial_dividedDifference hs] at h
  rw [integral_const_mul] at h
  have hf : (fun x : ℝ => Complex.ofReal (2 * s * x) * p.eval (Complex.ofReal (2 * s * x))) =
      fun x : ℝ => (2 * s : ℂ) * ((x : ℂ) * p.eval (Complex.ofReal (2 * s * x))) := by
    funext x
    push_cast
    ring
  rw [hf, integral_const_mul, h]
  push_cast
  ring

theorem law_centered (s : ℝ) : (∫ x : ℝ, (x : ℂ) ∂law s) = 0 := by
  rw [law_integral s (by fun_prop)]
  simp_rw [Complex.ofReal_mul, Complex.ofReal_ofNat]
  rw [integral_const_mul, base_centered, mul_zero]

theorem law_second_moment {s : ℝ} (hs : s ≠ 0) :
    (∫ x : ℝ, (x : ℂ) ^ 2 ∂law s) = (s ^ 2 : ℝ) := by
  simpa only [eval_X, dividedDifference_X, integral_const, probReal_univ,
    smul_eq_mul, one_smul, one_mul, mul_one, pow_two] using law_free_integration_by_parts hs X

abbrev OneSpace (s : ℝ) := Lp ℂ 2 (law s)
abbrev KernelSpace (s : ℝ) := Lp ℂ 2 ((law s).prod (law s))

def constantVector {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (c : ℂ) : Lp ℂ 2 μ := (memLp_const c).toLp (fun _ => c)

theorem constantVector_ae {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (c : ℂ) : constantVector μ c =ᵐ[μ] fun _ => c := MemLp.coeFn_toLp _

theorem constantVector_norm {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (c : ℂ) : ‖constantVector μ c‖ = ‖c‖ := by
  rw [constantVector, Lp.norm_toLp, eLpNorm_const c (by norm_num) (NeZero.ne μ)]
  simp

theorem constantVector_sub {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (c d : ℂ) : constantVector μ c - constantVector μ d = constantVector μ (c - d) := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub (constantVector μ c) (constantVector μ d),
    constantVector_ae μ c, constantVector_ae μ d, constantVector_ae μ (c - d)] with x h hc hd hcd
  rw [h]
  dsimp only [Pi.sub_apply]
  rw [hc, hd, hcd]

def polynomialVector (s : ℝ) (p : ℂ[X]) : OneSpace s :=
  (law_memLp s (show Continuous (fun x : ℝ => p.eval (x : ℂ)) by fun_prop) 2).toLp _

def coordinateVector (s : ℝ) : OneSpace s := polynomialVector s X

def testVector {s : ℝ} (hs : s ≠ 0) (p : ℂ[X]) : KernelSpace s :=
  (law_dividedDifference_memLp hs p 2).toLp _

theorem polynomialVector_ae (s : ℝ) (p : ℂ[X]) :
    polynomialVector s p =ᵐ[law s] fun x => p.eval (x : ℂ) := MemLp.coeFn_toLp _

theorem coordinateVector_ae (s : ℝ) : coordinateVector s =ᵐ[law s] fun x : ℝ => (x : ℂ) := by
  simpa only [coordinateVector, eval_X] using polynomialVector_ae s X

theorem testVector_ae {s : ℝ} (hs : s ≠ 0) (p : ℂ[X]) :
    testVector hs p =ᵐ[(law s).prod (law s)] fun z => dividedDifference p z.1 z.2 :=
  MemLp.coeFn_toLp _

/-- Native L2 inner products, with the conjugate-linear-first convention of Lean. -/
theorem polynomial_coordinate_inner (s : ℝ) (p : ℂ[X]) :
    ⟪polynomialVector s p, coordinateVector s⟫_ℂ =
      conj (∫ x : ℝ, (x : ℂ) * p.eval (x : ℂ) ∂law s) := by
  rw [L2.inner_def, ← integral_conj]
  apply integral_congr_ae
  filter_upwards [polynomialVector_ae s p, coordinateVector_ae s] with x hp hx
  rw [hp, hx]
  simp [RCLike.inner_apply]

theorem test_constant_inner {s : ℝ} (hs : s ≠ 0) (p : ℂ[X]) (c : ℂ) :
    ⟪testVector hs p, constantVector ((law s).prod (law s)) c⟫_ℂ =
      conj (∫ z, dividedDifference p z.1 z.2 ∂(law s).prod (law s)) * c := by
  rw [L2.inner_def, ← integral_conj, ← integral_mul_const]
  apply integral_congr_ae
  filter_upwards [testVector_ae hs p, constantVector_ae ((law s).prod (law s)) c] with z hp hc
  rw [hp, hc]
  simp [RCLike.inner_apply, mul_comm]

/-- ALL complex product-L2 kernels and ALL complex polynomial tests, with fixed V=x²/2. -/
def IsSteinKernel {s : ℝ} (hs : s ≠ 0) (A : KernelSpace s) : Prop :=
  ∀ p : ℂ[X], ⟪polynomialVector s p, coordinateVector s⟫_ℂ = ⟪testVector hs p, A⟫_ℂ

theorem constant_isSteinKernel {s : ℝ} (hs : s ≠ 0) :
    IsSteinKernel hs (constantVector ((law s).prod (law s)) (s ^ 2 : ℝ)) := by
  intro p
  rw [polynomial_coordinate_inner, test_constant_inner, law_free_integration_by_parts hs]
  simp [mul_comm]

theorem testVector_X {s : ℝ} (hs : s ≠ 0) :
    testVector hs X = constantVector ((law s).prod (law s)) 1 := by
  apply Lp.ext
  filter_upwards [testVector_ae hs X, constantVector_ae ((law s).prod (law s)) 1] with z hz hc
  rw [hz, hc, dividedDifference_X]

theorem kernel_mean_constraint {s : ℝ} (hs : s ≠ 0) (A : KernelSpace s) (hA : IsSteinKernel hs A) :
    ⟪constantVector ((law s).prod (law s)) 1, A⟫_ℂ = (s ^ 2 : ℝ) := by
  have h := hA X
  rw [testVector_X, polynomial_coordinate_inner] at h
  simp only [eval_X, ← pow_two, law_second_moment hs, Complex.conj_ofReal] at h
  exact h.symm

theorem constant_one_inner (s : ℝ) :
    ⟪constantVector ((law s).prod (law s)) 1,
      constantVector ((law s).prod (law s)) 1⟫_ℂ = 1 := by
  rw [inner_self_eq_norm_sq_to_K, constantVector_norm]
  norm_num

theorem kernel_norm_lower {s : ℝ} (hs : s ≠ 0) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (A : KernelSpace s) (hA : IsSteinKernel hs A) :
    1 - s ^ 2 ≤ ‖A - constantVector ((law s).prod (law s)) 1‖ := by
  have hm : ⟪constantVector ((law s).prod (law s)) 1,
      A - constantVector ((law s).prod (law s)) 1⟫_ℂ = Complex.ofReal (s ^ 2 - 1) := by
    rw [inner_sub_right, kernel_mean_constraint hs A hA, constant_one_inner]
    push_cast
    rfl
  have ha : s ^ 2 - 1 ≤ 0 := by nlinarith
  calc
    1 - s ^ 2 = ‖Complex.ofReal (s ^ 2 - 1)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos ha]
      ring
    _ = ‖⟪constantVector ((law s).prod (law s)) 1,
        A - constantVector ((law s).prod (law s)) 1⟫_ℂ‖ := congrArg norm hm.symm
    _ ≤ ‖constantVector ((law s).prod (law s)) 1‖ *
        ‖A - constantVector ((law s).prod (law s)) 1‖ := norm_inner_le_norm _ _
    _ = ‖A - constantVector ((law s).prod (law s)) 1‖ := by
      rw [constantVector_norm]
      norm_num

theorem attained_kernel_distance {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ‖constantVector ((law s).prod (law s)) (s ^ 2 : ℝ) -
      constantVector ((law s).prod (law s)) 1‖ = 1 - s ^ 2 := by
  rw [constantVector_sub, constantVector_norm, ← Complex.ofReal_one, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by nlinarith : s ^ 2 - 1 ≤ 0)]
  ring

/-- The complete value set: no constant/symmetric/polynomial restriction on the kernel. -/
def discrepancyValues {s : ℝ} (hs : s ≠ 0) : Set ℝ :=
  {r | ∃ A : KernelSpace s, IsSteinKernel hs A ∧
    r = ‖A - constantVector ((law s).prod (law s)) 1‖}

theorem discrepancyValues_nonempty {s : ℝ} (hs : s ≠ 0) : (discrepancyValues hs).Nonempty := by
  exact ⟨_, constantVector ((law s).prod (law s)) (s ^ 2 : ℝ), constant_isSteinKernel hs, rfl⟩

theorem discrepancyValues_bddBelow {s : ℝ} (hs : s ≠ 0) : BddBelow (discrepancyValues hs) := by
  refine ⟨0, ?_⟩
  rintro r ⟨A, _, rfl⟩
  exact norm_nonneg _

/-- The true full-kernel infimum. Its nonemptiness and lower bound are proved above. -/
def discrepancy {s : ℝ} (hs : s ≠ 0) : ℝ := sInf (discrepancyValues hs)

theorem discrepancy_eq {s : ℝ} (hs : s ≠ 0) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    discrepancy hs = 1 - s ^ 2 := by
  apply le_antisymm
  · apply csInf_le (discrepancyValues_bddBelow hs)
    exact ⟨constantVector ((law s).prod (law s)) (s ^ 2 : ℝ), constant_isSteinKernel hs,
      (attained_kernel_distance hs0 hs1).symm⟩
  · apply le_csInf (discrepancyValues_nonempty hs)
    rintro r ⟨A, hA, rfl⟩
    exact kernel_norm_lower hs hs0 hs1 A hA

theorem standard_semicircle_discrepancy_zero : discrepancy (by norm_num : (1 : ℝ) ≠ 0) = 0 := by
  rw [discrepancy_eq _ (by norm_num) le_rfl]
  norm_num

theorem arbitrarily_small_positive_discrepancy (c : ℝ) (hc : 0 < c) :
    ∃ s : ℝ, ∃ hs : s ≠ 0, 0 < s ∧ s < 1 ∧
      0 < discrepancy hs ∧ discrepancy hs < c ∧
      NullSingletonClass (law s) ∧ (∀ᵐ x ∂law s, x ∈ Icc (-2 : ℝ) 2) := by
  let e := min (c / 4) (1 / 4 : ℝ)
  have he : 0 < e := lt_min (by positivity) (by norm_num)
  have he1 : e ≤ 1 / 4 := min_le_right _ _
  have hec : e ≤ c / 4 := min_le_left _ _
  have hs0 : 0 < 1 - e := by linarith
  have hs1 : 1 - e < 1 := by linarith
  refine ⟨1 - e, hs0.ne', hs0, hs1, ?_, ?_, law_noAtoms hs0.ne',
    law_supported hs0.le hs1.le⟩
  · rw [discrepancy_eq _ hs0.le hs1.le]
    nlinarith
  · rw [discrepancy_eq _ hs0.le hs1.le]
    nlinarith [sq_nonneg e]

def coordinateTop (s : ℝ) : Lp ℂ ∞ (law s) :=
  (law_memLp s (show Continuous (fun x : ℝ => (x : ℂ)) by fun_prop) ∞).toLp _

/-- Genuine bounded multiplication by the coordinate on the complex Hilbert space L²(μ_s). -/
def coordinateOperator (s : ℝ) : OneSpace s →L[ℂ] OneSpace s :=
  (ContinuousLinearMap.mul ℂ ℂ).holderL (law s) ∞ 2 2 (coordinateTop s)

theorem coordinateOperator_ae (s : ℝ) (f : OneSpace s) :
    coordinateOperator s f =ᵐ[law s] fun x : ℝ => (x : ℂ) * f x := by
  have h := (ContinuousLinearMap.mul ℂ ℂ).coeFn_holder (r := 2) (coordinateTop s) f
  change (coordinateOperator s f) =ᵐ[law s] fun x => coordinateTop s x * f x at h
  have hc : coordinateTop s =ᵐ[law s] fun x : ℝ => (x : ℂ) := MemLp.coeFn_toLp _
  filter_upwards [h, hc] with x hx hc
  simpa only [hc] using hx

theorem coordinateOperator_selfAdjoint (s : ℝ) : IsSelfAdjoint (coordinateOperator s) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro f g
  change ⟪coordinateOperator s f, g⟫_ℂ = ⟪f, coordinateOperator s g⟫_ℂ
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coordinateOperator_ae s f, coordinateOperator_ae s g] with x hf hg
  rw [hf, hg]
  simp only [RCLike.inner_apply, map_mul, Complex.conj_ofReal]
  ring

theorem coordinateOperator_norm_le {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ‖coordinateOperator s‖ ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro f
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [coordinateOperator_ae s f, law_supported hs0 hs1] with x hx hs
  rw [hx, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (abs_le.mpr hs) (norm_nonneg _)

def vacuum (s : ℝ) : OneSpace s := constantVector (law s) 1

theorem vacuum_norm (s : ℝ) : ‖vacuum s‖ = 1 := by simp [vacuum, constantVector_norm]

def vectorStateLinear (s : ℝ) : (OneSpace s →L[ℂ] OneSpace s) →ₗ[ℂ] ℂ where
  toFun T := ⟪vacuum s, T (vacuum s)⟫_ℂ
  map_add' T U := by simp only [add_apply, inner_add_right]
  map_smul' c T := by simp only [smul_apply, inner_smul_right, smul_eq_mul, RingHom.id_apply]

def vectorState (s : ℝ) : (OneSpace s →L[ℂ] OneSpace s) →L[ℂ] ℂ :=
  (vectorStateLinear s).mkContinuous 1 (by
    intro T
    change ‖⟪vacuum s, T (vacuum s)⟫_ℂ‖ ≤ 1 * ‖T‖
    calc
      _ ≤ ‖vacuum s‖ * ‖T (vacuum s)‖ := norm_inner_le_norm _ _
      _ ≤ ‖vacuum s‖ * (‖T‖ * ‖vacuum s‖) :=
        mul_le_mul_of_nonneg_left (T.le_opNorm _) (norm_nonneg _)
      _ = 1 * ‖T‖ := by rw [vacuum_norm]; ring)

theorem vectorState_one (s : ℝ) : vectorState s 1 = 1 := by
  change ⟪vacuum s, vacuum s⟫_ℂ = 1
  rw [inner_self_eq_norm_sq_to_K, vacuum_norm]
  norm_num

theorem vectorState_positive (s : ℝ) (T : OneSpace s →L[ℂ] OneSpace s) :
    0 ≤ (vectorState s (star T * T)).re := by
  change 0 ≤ (⟪vacuum s, (star T) (T (vacuum s))⟫_ℂ).re
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
  exact inner_self_nonneg (𝕜 := ℂ) (x := T (vacuum s))

theorem coordinateOperator_pow_vacuum_ae (s : ℝ) (n : ℕ) :
    ((coordinateOperator s) ^ n) (vacuum s) =ᵐ[law s] fun x : ℝ => (x : ℂ) ^ n := by
  induction n with
  | zero => simpa only [pow_zero, one_apply_eq_self, vacuum] using
      constantVector_ae (law s) 1
  | succ n ih =>
    simp only [pow_succ', mul_apply_eq_comp]
    filter_upwards [coordinateOperator_ae s (((coordinateOperator s) ^ n) (vacuum s)), ih] with x hx hi
    rw [hx, hi]

theorem coordinateOperator_polynomial_vacuum_ae (s : ℝ) (p : ℂ[X]) :
    (aeval (coordinateOperator s) p) (vacuum s) =ᵐ[law s] fun x : ℝ => p.eval (x : ℂ) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add, add_apply, eval_add]
    filter_upwards [Lp.coeFn_add ((aeval (coordinateOperator s) p) (vacuum s))
      ((aeval (coordinateOperator s) q) (vacuum s)), hp, hq] with x h hx hy
    simpa only [Pi.add_apply, hx, hy] using h
  | monomial n c =>
    simp only [aeval_monomial, Algebra.algebraMap_eq_smul_one, mul_apply_eq_comp,
      smul_apply, one_apply_eq_self, eval_monomial]
    filter_upwards [Lp.coeFn_smul c (((coordinateOperator s) ^ n) (vacuum s)),
      coordinateOperator_pow_vacuum_ae s n] with x hx hn
    simpa only [Pi.smul_apply, smul_eq_mul, hn] using hx

/-- Full complex polynomial distribution identity for the actual bounded self-adjoint operator. -/
theorem coordinateOperator_distribution (s : ℝ) (p : ℂ[X]) :
    vectorState s (aeval (coordinateOperator s) p) = ∫ x, p.eval (x : ℂ) ∂law s := by
  change ⟪vacuum s, (aeval (coordinateOperator s) p) (vacuum s)⟫_ℂ = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [constantVector_ae (law s) 1,
    coordinateOperator_polynomial_vacuum_ae s p] with x hv hp
  change ⟪constantVector (law s) 1 x, _⟫_ℂ = _
  rw [hv, hp]
  simp [RCLike.inner_apply]

def standardDensity (x : ℝ) : ℝ := (2 * Real.pi)⁻¹ * Real.sqrt (4 - x ^ 2)

theorem standardDensity_scaled (x : ℝ) :
    standardDensity (2 * x) = Real.pi⁻¹ * Real.sqrt (1 - x ^ 2) := by
  have h4 : Real.sqrt (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  rw [standardDensity, show 4 - (2 * x) ^ 2 = 4 * (1 - x ^ 2) by ring,
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), h4]
  norm_num
  field_simp

/-- Actual density identification at the fixed variance-one reference, for every continuous test. -/
theorem law_one_density_integral {f : ℝ → ℝ} (hf : Continuous f) :
    (∫ x, f x ∂law 1) = ∫ x in (-2 : ℝ)..2, f x * standardDensity x := by
  rw [law_integral 1 hf]
  simp only [mul_one]
  rw [base_integral_real]
  have h := intervalIntegral.integral_comp_mul_left
    (f := fun x => f x * standardDensity x) (a := (-1 : ℝ)) (b := 1) (c := 2) (by norm_num)
  have hs : (fun x : ℝ => f (2 * x) * standardDensity (2 * x)) =
      fun x => Real.pi⁻¹ * (f (2 * x) * Real.sqrt (1 - x ^ 2)) := by
    funext x
    rw [standardDensity_scaled]
    ring
  rw [hs, intervalIntegral.integral_const_mul] at h
  norm_num only [smul_eq_mul] at h
  linear_combination 2 * h

/-- Every positive proposed next value is surpassed by a genuine atomless operator law. -/
theorem operator_laws_have_no_positive_next_value (c : ℝ) (hc : 0 < c) :
    ∃ s : ℝ, ∃ hs : s ≠ 0, 0 < s ∧ s < 1 ∧
      NullSingletonClass (law s) ∧ (∀ᵐ x ∂law s, x ∈ Icc (-2 : ℝ) 2) ∧
      IsSelfAdjoint (coordinateOperator s) ∧ ‖coordinateOperator s‖ ≤ 2 ∧
      vectorState s 1 = 1 ∧
      (∀ T : OneSpace s →L[ℂ] OneSpace s, 0 ≤ (vectorState s (star T * T)).re) ∧
      (∀ p : ℂ[X], vectorState s (aeval (coordinateOperator s) p) =
        ∫ x, p.eval (x : ℂ) ∂law s) ∧
      0 < discrepancy hs ∧ discrepancy hs < c := by
  obtain ⟨s, hs, hs0, hs1, hd0, hdc, hn, hsupport⟩ := arbitrarily_small_positive_discrepancy c hc
  exact ⟨s, hs, hs0, hs1, hn, hsupport, coordinateOperator_selfAdjoint s,
    coordinateOperator_norm_le hs0.le hs1.le, vectorState_one s, vectorState_positive s,
    coordinateOperator_distribution s, hd0, hdc⟩

theorem no_positive_gap_on_admissible_family :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ s : ℝ, ∀ hs : s ≠ 0,
      0 < s → s < 1 → discrepancy hs = 0 ∨ c ≤ discrepancy hs := by
  rintro ⟨c, hc, h⟩
  obtain ⟨s, hs, hs0, hs1, hd0, hdc, _, _⟩ := arbitrarily_small_positive_discrepancy c hc
  rcases h s hs hs0 hs1 with hz | he
  · linarith
  · linarith

/-- Moments are native integrals of the actual measure, not a prescribed sequence. -/
def moment (s : ℝ) (n : ℕ) : ℂ := ∫ x : ℝ, (x : ℂ) ^ n ∂law s

theorem moment_zero (s : ℝ) : moment s 0 = 1 := by simp [moment]

theorem moment_one (s : ℝ) : moment s 1 = 0 := by simpa [moment] using law_centered s

theorem moment_two {s : ℝ} (hs : s ≠ 0) : moment s 2 = (s ^ 2 : ℝ) := law_second_moment hs

theorem dividedDifference_power_of_ne (n : ℕ) {x y : ℝ} (h : x ≠ y) :
    dividedDifference (X ^ (n + 1)) x y =
      ∑ i ∈ Finset.range (n + 1), (x : ℂ) ^ i * (y : ℂ) ^ (n - i) := by
  rw [dividedDifference, if_neg h, eval_pow, eval_pow, eval_X, eval_X]
  apply (div_eq_iff (sub_ne_zero.mpr (Complex.ofReal_injective.ne h))).mpr
  symm
  simpa only [Nat.add_sub_cancel] using geom_sum₂_mul (x : ℂ) (y : ℂ) (n + 1)

/-- The entire actual moment recursion, obtained from all polynomial Stein tests and Fubini. -/
theorem all_moments_recurrence {s : ℝ} (hs : s ≠ 0) (n : ℕ) :
    moment s (n + 2) = (s ^ 2 : ℝ) *
      ∑ i ∈ Finset.range (n + 1), moment s i * moment s (n - i) := by
  let _ := law_noAtoms hs
  have hoff : ∀ᵐ z ∂(law s).prod (law s), z.1 ≠ z.2 := by
    apply (Measure.ae_prod_iff_ae_ae (isClosed_eq continuous_fst continuous_snd).measurableSet.compl).mpr
    exact Eventually.of_forall fun x => ((law s).ae_ne x).mono fun _ hy => hy.symm
  have hae : (fun z : ℝ × ℝ => dividedDifference (X ^ (n + 1)) z.1 z.2) =ᵐ[(law s).prod (law s)]
      fun z => ∑ i ∈ Finset.range (n + 1), (z.1 : ℂ) ^ i * (z.2 : ℂ) ^ (n - i) :=
    hoff.mono fun _ hz => dividedDifference_power_of_ne n hz
  have h := law_free_integration_by_parts hs (X ^ (n + 1))
  simp only [eval_pow, eval_X, ← pow_succ'] at h
  change moment s (n + 2) = _ at h
  rw [integral_congr_ae hae, integral_finsetSum] at h
  · have hm (i : ℕ) : (∫ z : ℝ × ℝ, (z.1 : ℂ) ^ i * (z.2 : ℂ) ^ (n - i)
        ∂(law s).prod (law s)) = moment s i * moment s (n - i) :=
      integral_prod_mul (μ := law s) (ν := law s)
        (fun x : ℝ => (x : ℂ) ^ i) (fun y : ℝ => (y : ℂ) ^ (n - i))
    simp_rw [hm] at h
    exact h
  · intro i hi
    exact (law_integrable s (show Continuous (fun x : ℝ => (x : ℂ) ^ i) by fun_prop)).mul_prod
      (law_integrable s (show Continuous (fun x : ℝ => (x : ℂ) ^ (n - i)) by fun_prop))

/-- The vector state is tracial on the actual commutative polynomial operator algebra. -/
theorem vectorState_polynomial_tracial (s : ℝ) (p q : ℂ[X]) :
    vectorState s (aeval (coordinateOperator s) p * aeval (coordinateOperator s) q) =
      vectorState s (aeval (coordinateOperator s) q * aeval (coordinateOperator s) p) := by
  rw [← map_mul, ← map_mul, mul_comm p q]

end TLMC7733
