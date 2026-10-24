import Mathlib.Algebra.QuadraticAlgebra.NormDeterminant
import Mathlib.RingTheory.Norm.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Arithmetic incompatibility of the printed explicit square-root-golden-ratio
value and membership in the units of Q(sqrt5). No Stokes object is assigned a
value; the obstruction applies to every possible scalar with these properties. -/

noncomputable section
open scoped goldenRatio

namespace TLMC2101

theorem rational_no_sqrt_five (r : ℚ) : r ^ 2 ≠ (5 : ℚ) := by
  intro hr
  have hcast : (r : ℝ) ^ 2 = 5 := by exact_mod_cast hr
  have hroot : (Real.sqrt (5 : ℝ)) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hirr : Irrational (Real.sqrt (5 : ℝ)) :=
    Nat.Prime.irrational_sqrt (by norm_num : Nat.Prime 5)
  obtain h | h := sq_eq_sq_iff_eq_or_eq_neg.mp (hcast.trans hroot.symm)
  · exact hirr.ne_rat r h.symm
  · apply hirr.ne_rat (-r)
    push_cast
    linarith

instance rational_no_quadratic_root : Fact (∀ r : ℚ, r ^ 2 ≠ 5 + 0 * r) :=
  ⟨fun r => by simpa using rational_no_sqrt_five r⟩

/-- Native quadratic algebra with omega^2=5; the proved irreducibility fact
gives its genuine native Field instance, not a two-dimensional vector model. -/
abbrev QuadraticField := QuadraticAlgebra ℚ 5 0

def omega : QuadraticField := QuadraticAlgebra.omega

theorem quadratic_degree : Module.finrank ℚ QuadraticField = 2 :=
  QuadraticAlgebra.finrank_eq_two 5 0

theorem omega_sq : omega ^ 2 = (5 : QuadraticField) := by
  simpa [omega, pow_two] using
    (QuadraticAlgebra.omega_mul_omega_eq_algebraMap (R := ℚ) (a := 5) (b := 0))

def conjugation : QuadraticField ≃ₐ[ℚ] QuadraticField where
  toFun := star
  invFun := star
  left_inv := star_star
  right_inv := star_star
  map_mul' x y := by simp
  map_add' := star_add
  commutes' q := by ext <;> simp

theorem conjugation_apply (z : QuadraticField) : conjugation z = ⟨z.re, -z.im⟩ := by
  ext <;> simp [conjugation]

def realEmbedding : QuadraticField →ₐ[ℚ] ℝ :=
  QuadraticAlgebra.lift ⟨Real.sqrt 5, by
    norm_num [Algebra.smul_def, ← pow_two, Real.sq_sqrt]⟩

theorem realEmbedding_apply (z : QuadraticField) :
    realEmbedding z = (z.re : ℝ) + (z.im : ℝ) * Real.sqrt 5 := by
  change z.re • (1 : ℝ) + z.im • Real.sqrt 5 = _
  simp [Algebra.smul_def]

theorem realEmbedding_injective : Function.Injective realEmbedding := realEmbedding.injective

theorem realEmbedding_omega : realEmbedding omega = Real.sqrt 5 := by
  simp [realEmbedding_apply, omega, QuadraticAlgebra.omega]

theorem realEmbedding_conjugation (z : QuadraticField) :
    realEmbedding (conjugation z) = (z.re : ℝ) - (z.im : ℝ) * Real.sqrt 5 := by
  simp [realEmbedding_apply, conjugation_apply, sub_eq_add_neg]

def realQuadraticField : IntermediateField ℚ ℝ :=
  IntermediateField.adjoin ℚ ({Real.sqrt 5} : Set ℝ)

theorem realEmbedding_range : realEmbedding.fieldRange = realQuadraticField := by
  apply le_antisymm
  · intro x hx
    obtain ⟨z, rfl⟩ := AlgHom.mem_fieldRange.mp hx
    rw [realEmbedding_apply]
    exact realQuadraticField.add_mem (realQuadraticField.algebraMap_mem z.re)
      (realQuadraticField.mul_mem (realQuadraticField.algebraMap_mem z.im)
        (IntermediateField.subset_adjoin ℚ _ (by simp)))
  · apply IntermediateField.adjoin_le_iff.mpr
    intro x hx
    have hx' : x = Real.sqrt 5 := Set.mem_singleton_iff.mp hx
    subst x
    exact AlgHom.mem_fieldRange.mpr ⟨omega, realEmbedding_omega⟩

def quadraticFieldEquivalence : QuadraticField ≃ₐ[ℚ] realQuadraticField :=
  realEmbedding.equivFieldRange.trans (IntermediateField.equivOfEq realEmbedding_range)

/-- This equality connects the computed quadratic norm to the native
determinant-of-left-multiplication Algebra.norm on the actual field. -/
theorem nativeNorm_eq_quadraticNorm (z : QuadraticField) :
    Algebra.norm ℚ z = QuadraticAlgebra.norm z := by
  rw [Algebra.norm_apply]
  exact QuadraticAlgebra.det_toLinearMap_eq_norm z

theorem nativeNorm_formula (z : QuadraticField) :
    Algebra.norm ℚ z = z.re * z.re - 5 * z.im * z.im := by
  rw [nativeNorm_eq_quadraticNorm, QuadraticAlgebra.norm_def]
  ring

theorem nativeNorm_conjugation_product (z : QuadraticField) :
    algebraMap ℚ QuadraticField (Algebra.norm ℚ z) = z * conjugation z := by
  rw [nativeNorm_eq_quadraticNorm]
  exact QuadraticAlgebra.algebraMap_norm_eq_mul_star z

/-- The actual field element whose real image is the usual golden ratio. -/
def goldenElement : QuadraticField := ⟨1 / 2, 1 / 2⟩

theorem realEmbedding_goldenElement : realEmbedding goldenElement = Real.goldenRatio := by
  rw [realEmbedding_apply]
  norm_num [goldenElement, Real.goldenRatio]
  ring

theorem realEmbedding_conjugate_golden :
    realEmbedding (conjugation goldenElement) = Real.goldenConj := by
  rw [realEmbedding_conjugation]
  norm_num [goldenElement, Real.goldenConj]
  ring

theorem goldenElement_norm : Algebra.norm ℚ goldenElement = (-1 : ℚ) := by
  norm_num [nativeNorm_formula, goldenElement]

theorem actual_real_field_golden_image :
    ((quadraticFieldEquivalence goldenElement : realQuadraticField) : ℝ) =
      Real.goldenRatio := by
  change realEmbedding goldenElement = _
  exact realEmbedding_goldenElement

theorem actual_real_field_golden_norm :
    Algebra.norm ℚ (quadraticFieldEquivalence goldenElement) = (-1 : ℚ) := by
  rw [Algebra.norm_eq_of_algEquiv quadraticFieldEquivalence, goldenElement_norm]

theorem goldenElement_ne_zero : goldenElement ≠ 0 := by
  intro h
  have : Real.goldenRatio = 0 := by simpa [realEmbedding_goldenElement] using congrArg realEmbedding h
  exact Real.goldenRatio_ne_zero this

theorem goldenElement_unit : IsUnit goldenElement := isUnit_iff_ne_zero.mpr goldenElement_ne_zero

theorem no_square_goldenElement (x : QuadraticField) : x ^ 2 ≠ goldenElement := by
  intro hx
  have hn := congrArg (Algebra.norm ℚ) hx
  rw [map_pow, goldenElement_norm] at hn
  have hnonneg := sq_nonneg (Algebra.norm ℚ x)
  linarith

theorem no_square_root_in_real_field {x : ℝ} (hx : x ^ 2 = Real.goldenRatio) :
    x ∉ realQuadraticField := by
  intro hmem
  rw [← realEmbedding_range] at hmem
  obtain ⟨z, hz⟩ := AlgHom.mem_fieldRange.mp hmem
  apply no_square_goldenElement z
  apply realEmbedding_injective
  rw [map_pow, hz, realEmbedding_goldenElement]
  exact hx

def explicitValue : ℝ := Real.sqrt Real.goldenRatio

theorem explicitValue_pos : 0 < explicitValue := Real.sqrt_pos.mpr Real.goldenRatio_pos

theorem explicitValue_sq : explicitValue ^ 2 = Real.goldenRatio :=
  Real.sq_sqrt Real.goldenRatio_pos.le

theorem explicitValue_not_in_real_field : explicitValue ∉ realQuadraticField :=
  no_square_root_in_real_field explicitValue_sq

theorem real_square_root_branches (x : ℝ) :
    x ^ 2 = Real.goldenRatio ↔ x = explicitValue ∨ x = -explicitValue := by
  rw [← explicitValue_sq, sq_eq_sq_iff_eq_or_eq_neg]

end TLMC2101

namespace TLMC2101

def realToComplex : ℝ →ₐ[ℚ] ℂ where
  toRingHom := Complex.ofRealHom
  commutes' q := by simp

def complexEmbedding : QuadraticField →ₐ[ℚ] ℂ := realToComplex.comp realEmbedding

theorem complexEmbedding_apply (z : QuadraticField) :
    complexEmbedding z = (z.re : ℂ) + (z.im : ℂ) * (Real.sqrt 5 : ℂ) := by
  change (realEmbedding z : ℂ) = _
  rw [realEmbedding_apply]
  push_cast
  rfl

theorem complexEmbedding_goldenElement :
    complexEmbedding goldenElement = (Real.goldenRatio : ℂ) := by
  change (realEmbedding goldenElement : ℂ) = _
  rw [realEmbedding_goldenElement]

def complexQuadraticField : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ ({(Real.sqrt 5 : ℂ)} : Set ℂ)

theorem complexEmbedding_range : complexEmbedding.fieldRange = complexQuadraticField := by
  apply le_antisymm
  · intro x hx
    obtain ⟨z, rfl⟩ := AlgHom.mem_fieldRange.mp hx
    rw [complexEmbedding_apply]
    exact complexQuadraticField.add_mem (complexQuadraticField.algebraMap_mem z.re)
      (complexQuadraticField.mul_mem (complexQuadraticField.algebraMap_mem z.im)
        (IntermediateField.subset_adjoin ℚ _ (by simp)))
  · apply IntermediateField.adjoin_le_iff.mpr
    intro x hx
    have hx' : x = (Real.sqrt 5 : ℂ) := Set.mem_singleton_iff.mp hx
    subst x
    apply AlgHom.mem_fieldRange.mpr
    refine ⟨omega, ?_⟩
    change (realEmbedding omega : ℂ) = _
    rw [realEmbedding_omega]

def complexFieldEquivalence : QuadraticField ≃ₐ[ℚ] complexQuadraticField :=
  complexEmbedding.equivFieldRange.trans (IntermediateField.equivOfEq complexEmbedding_range)

theorem actual_complex_field_golden_image :
    ((complexFieldEquivalence goldenElement : complexQuadraticField) : ℂ) =
      (Real.goldenRatio : ℂ) := by
  change complexEmbedding goldenElement = _
  exact complexEmbedding_goldenElement

theorem actual_complex_field_golden_norm :
    Algebra.norm ℚ (complexFieldEquivalence goldenElement) = (-1 : ℚ) := by
  rw [Algebra.norm_eq_of_algEquiv complexFieldEquivalence, goldenElement_norm]

/-- The impossibility holds for any field embedding and any scalar whose
square is the actual embedded golden element; no analytic data are needed. -/
theorem no_embedded_square_root {K : Type*} [Field K] [Algebra ℚ K]
    (f : QuadraticField →ₐ[ℚ] K) {z : K} (hz : z ^ 2 = f goldenElement) :
    z ∉ f.fieldRange := by
  intro hmem
  obtain ⟨x, hx⟩ := AlgHom.mem_fieldRange.mp hmem
  apply no_square_goldenElement x
  apply f.injective
  rw [map_pow]
  change f x ^ 2 = f goldenElement
  rw [hx]
  exact hz

theorem no_square_root_in_complex_field {z : ℂ} (hz : z ^ 2 = (Real.goldenRatio : ℂ)) :
    z ∉ complexQuadraticField := by
  rw [← complexEmbedding_range]
  apply no_embedded_square_root complexEmbedding
  rwa [complexEmbedding_goldenElement]

theorem explicitValue_complex_sq : (explicitValue : ℂ) ^ 2 = (Real.goldenRatio : ℂ) := by
  exact_mod_cast explicitValue_sq

theorem complex_square_root_branches (z : ℂ) :
    z ^ 2 = (Real.goldenRatio : ℂ) ↔
      z = (explicitValue : ℂ) ∨ z = -(explicitValue : ℂ) := by
  rw [← explicitValue_complex_sq, sq_eq_sq_iff_eq_or_eq_neg]

theorem no_unit_square_root (z : ℂ) :
    ¬(z ^ 2 = (Real.goldenRatio : ℂ) ∧
      ∃ u : complexQuadraticFieldˣ, ((u : complexQuadraticField) : ℂ) = z) := by
  rintro ⟨hz, u, hu⟩
  apply no_square_root_in_complex_field hz
  rw [← hu]
  exact (u : complexQuadraticField).property

theorem explicitValue_not_unit_image :
    ¬ ∃ u : complexQuadraticFieldˣ,
      ((u : complexQuadraticField) : ℂ) = (explicitValue : ℂ) := by
  intro h
  exact no_unit_square_root (explicitValue : ℂ) ⟨explicitValue_complex_sq, h⟩

theorem pointwise_claims_impossible {ι : Type*} (value : ι → ℂ) (i : ι) :
    ¬((value i) ^ 2 = (Real.goldenRatio : ℂ) ∧
      ∃ u : complexQuadraticFieldˣ, ((u : complexQuadraticField) : ℂ) = value i) :=
  no_unit_square_root (value i)

theorem complete_counterexample :
    Module.finrank ℚ QuadraticField = 2 ∧
    realEmbedding.fieldRange = realQuadraticField ∧
    complexEmbedding.fieldRange = complexQuadraticField ∧
    Algebra.norm ℚ goldenElement = (-1 : ℚ) ∧
    0 < explicitValue ∧ explicitValue ^ 2 = Real.goldenRatio ∧
    explicitValue ∉ realQuadraticField ∧
    (∀ z : ℂ, z ^ 2 = (Real.goldenRatio : ℂ) → z ∉ complexQuadraticField) ∧
    (∀ z : ℂ, ¬(z ^ 2 = (Real.goldenRatio : ℂ) ∧
      ∃ u : complexQuadraticFieldˣ, ((u : complexQuadraticField) : ℂ) = z)) :=
  ⟨quadratic_degree, realEmbedding_range, complexEmbedding_range, goldenElement_norm,
    explicitValue_pos, explicitValue_sq, explicitValue_not_in_real_field,
    fun _ hz => no_square_root_in_complex_field hz, no_unit_square_root⟩

end TLMC2101
