import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

noncomputable section
open Complex Filter
open scoped Topology

namespace Conjecture5268

/-- The planar point-vortex field, with the constant time factor absorbed into circulations. -/
def vortexField (Γ : Fin 3 → ℝ) (z : Fin 3 → ℂ) (i : Fin 3) : ℂ :=
  ∑ j : Fin 3, if j = i then 0 else
    (Γ j : ℂ) * Complex.I * (z i - z j) / (Complex.normSq (z i - z j) : ℂ)

def circulation : Fin 3 → ℝ := ![-1073 / 84, -1073 / 140, 1073 / 224]
def center : ℂ := 3 / 8 - (15 / 56) * Complex.I
def shape : Fin 3 → ℂ :=
  ![-3 / 8 + (15 / 56) * Complex.I, 5 / 8 + (15 / 56) * Complex.I,
    (8 / 7) * Complex.I]
def eigenvalue : ℂ := -1 - (238 / 15) * Complex.I
def exponent : ℂ := 1 / 2 + (119 / 15) * Complex.I
def scale (t : ℝ) : ℂ := Complex.exp (exponent * (Real.log (1 - 2 * t) : ℂ))
def trajectory (t : ℝ) (i : Fin 3) : ℂ := center + scale t * shape i

theorem shape_distinct : Function.Injective shape := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    norm_num [shape, Complex.ext_iff] at h ⊢

theorem shape_field (i : Fin 3) : vortexField circulation shape i = eigenvalue * shape i := by
  fin_cases i <;>
    norm_num [vortexField, circulation, shape, eigenvalue, Fin.sum_univ_succ,
      Complex.normSq_apply, Complex.ext_iff, Complex.mul_re, Complex.mul_im] <;>
    norm_num [Complex.div_re, Complex.div_im, Fin.ext_iff]

theorem field_similarity (Γ : Fin 3 → ℝ) (w : Fin 3 → ℂ) (c u : ℂ) (i : Fin 3) :
    vortexField Γ (fun j => c + u * w j) i =
      (u / (Complex.normSq u : ℂ)) * vortexField Γ w i := by
  unfold vortexField
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : j = i
  · simp [h]
  · simp only [h, if_false]
    rw [show c + u * w i - (c + u * w j) = u * (w i - w j) by ring]
    simp only [Complex.normSq_mul, Complex.ofReal_mul, div_eq_mul_inv, mul_inv_rev]
    ring

theorem scale_normSq {t : ℝ} (ht : t < 1 / 2) :
    Complex.normSq (scale t) = 1 - 2 * t := by
  have hp : 0 < 1 - 2 * t := by linarith
  rw [Complex.normSq_eq_norm_sq, scale, Complex.norm_exp, ← Real.exp_nat_mul]
  convert Real.exp_log hp using 1
  congr 1
  norm_num [exponent, Complex.mul_re, Complex.mul_im]
  ring

theorem scale_derivative {t : ℝ} (ht : t < 1 / 2) :
    HasDerivAt scale (eigenvalue * scale t / ((1 - 2 * t : ℝ) : ℂ)) t := by
  have hp : 1 - 2 * t ≠ 0 := by linarith
  have hd : HasDerivAt (fun x : ℝ => 1 - 2 * x) (-2) t := by
    convert (hasDerivAt_id t).const_mul 2 |>.const_sub 1 using 1
    ring
  have he := ((hd.log hp).ofReal_comp.const_mul exponent).cexp
  convert he using 1
  simp only [scale, eigenvalue, exponent, Complex.ofReal_mul, Complex.ofReal_neg,
    Complex.ofReal_inv, Complex.ofReal_ofNat, Complex.ofReal_div]
  ring

theorem trajectory_distinct {t : ℝ} : Function.Injective (trajectory t) := by
  intro i j h
  apply shape_distinct
  exact mul_left_cancel₀ (Complex.exp_ne_zero _) (add_left_cancel h)

theorem trajectory_solves_normalized {t : ℝ} (ht : t < 1 / 2) (i : Fin 3) :
    HasDerivAt (fun s => trajectory s i) (vortexField circulation (trajectory t) i) t := by
  have h := (scale_derivative ht).mul_const (shape i) |>.const_add center
  convert h using 1
  change vortexField circulation (fun j => center + scale t * shape j) i = _
  rw [field_similarity, shape_field, scale_normSq ht]
  ring

theorem scale_collapses : Tendsto scale (𝓝[<] (1 / 2 : ℝ)) (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hc : Continuous (fun t : ℝ => Real.sqrt (1 - 2 * t)) := by fun_prop
  have hl : Tendsto (fun t : ℝ => Real.sqrt (1 - 2 * t))
      (𝓝[<] (1 / 2 : ℝ)) (𝓝 0) := by
    simpa using (hc.tendsto (1 / 2 : ℝ)).mono_left nhdsWithin_le_nhds
  apply hl.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [Complex.norm_def, scale_normSq ht]

theorem trajectory_collapses (i : Fin 3) :
    Tendsto (fun t => trajectory t i) (𝓝[<] (1 / 2 : ℝ)) (𝓝 center) := by
  simpa [trajectory] using tendsto_const_nhds.add (scale_collapses.mul_const (shape i))

/-- Physical circulations for the usual 1/(2 pi) convention. -/
def physicalCirculation (i : Fin 3) : ℝ := (2 * Real.pi) * circulation i

def standardVortexField (Γ : Fin 3 → ℝ) (z : Fin 3 → ℂ) (i : Fin 3) : ℂ :=
  ((2 * Real.pi : ℝ) : ℂ)⁻¹ * vortexField Γ z i

theorem field_circulation_scaling (r : ℝ) (Γ : Fin 3 → ℝ) (z : Fin 3 → ℂ)
    (i : Fin 3) :
    vortexField (fun j => r * Γ j) z i = (r : ℂ) * vortexField Γ z i := by
  unfold vortexField
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : j = i
  · simp [h]
  · simp only [h, if_false, Complex.ofReal_mul]
    ring

theorem standard_field_agrees (z : Fin 3 → ℂ) (i : Fin 3) :
    standardVortexField physicalCirculation z i = vortexField circulation z i := by
  have hp : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero
  unfold standardVortexField physicalCirculation
  rw [field_circulation_scaling, ← mul_assoc, inv_mul_cancel₀ hp, one_mul]

theorem trajectory_solves {t : ℝ} (ht : t < 1 / 2) (i : Fin 3) :
    HasDerivAt (fun s => trajectory s i)
      (standardVortexField physicalCirculation (trajectory t) i) t := by
  rw [standard_field_agrees]
  exact trajectory_solves_normalized ht i

theorem physical_circulation_nonzero (i : Fin 3) : physicalCirculation i ≠ 0 := by
  apply mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
  fin_cases i <;> norm_num [circulation]

theorem initial_positions (i : Fin 3) :
    trajectory 0 i = (![0, 1, 3 / 8 + (7 / 8) * Complex.I] : Fin 3 → ℂ) i := by
  fin_cases i <;> norm_num [trajectory, scale, center, shape, Complex.ext_iff]

/-- The necessary universal collision-exclusion assertion in the source. -/
def NoFiniteTimeThreeVortexCollision : Prop :=
  ∀ (Γ : Fin 3 → ℝ) (z : ℝ → Fin 3 → ℂ) (T : ℝ) (c : ℂ),
    (∀ i, Γ i ≠ 0) → 0 < T →
    (∀ t ∈ Set.Ico 0 T, Function.Injective (z t)) →
    (∀ t ∈ Set.Ico 0 T, ∀ i,
      HasDerivAt (fun s => z s i) (standardVortexField Γ (z t) i) t) →
    ¬ (∀ i, Tendsto (fun t => z t i) (𝓝[<] T) (𝓝 c))

theorem conjecture_false : ¬ NoFiniteTimeThreeVortexCollision := by
  intro h
  apply h physicalCirculation trajectory (1 / 2) center
  · exact physical_circulation_nonzero
  · norm_num
  · intro t _
    exact trajectory_distinct
  · intro t ht i
    exact trajectory_solves ht.2 i
  · exact trajectory_collapses

#print axioms shape_field
#print axioms trajectory_solves
#print axioms trajectory_collapses
#print axioms conjecture_false

end Conjecture5268
