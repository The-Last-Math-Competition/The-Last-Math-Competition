import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators

namespace Conjecture9755

/-- Four genuinely independent fair binary random choices. -/
abbrev Ω := Fin 2 × Fin 2 × Fin 2 × Fin 2
instance : MeasurableSpace Ω := ⊤
instance : MeasurableSingletonClass Ω := ⟨fun _ => trivial⟩

def μ : Measure Ω := (1 / 16 : ℝ≥0∞) • Measure.count

theorem mass_one : μ Set.univ = 1 := by
  norm_num [μ, Measure.smul_apply, Measure.count_univ, ENat.card_eq_coe_fintype_card,
    Fintype.card_prod, Fintype.card_fin]
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

instance : IsProbabilityMeasure μ := ⟨mass_one⟩

def sample (ω : Ω) : Fin 4 → Fin 2 := ![ω.1, ω.2.1, ω.2.2.1, ω.2.2.2]

theorem joint_outcome_mass (a b c d : Fin 2) :
    μ {ω | sample ω 0 = a ∧ sample ω 1 = b ∧ sample ω 2 = c ∧ sample ω 3 = d} =
      (1 / 2 : ℝ≥0∞) ^ 4 := by
  have hs : {ω | sample ω 0 = a ∧ sample ω 1 = b ∧ sample ω 2 = c ∧
      sample ω 3 = d} = {(a, b, c, d)} := by
    ext ω
    simp [sample, Prod.ext_iff, and_assoc]
  rw [hs]
  simp [μ, Measure.smul_apply, div_pow]
  rw [← ENNReal.inv_pow]
  norm_num

/-- The theorem and the proof generator stay fixed across all sample counts.
The successful output contains an actual Lean proof of True; the other output is failure. -/
def generate (coin : Fin 2) : Option (PLift True) :=
  if coin = 0 then none else some ⟨True.intro⟩

def success (k : ℕ) : Finset Ω :=
  Finset.univ.filter (fun ω => ∃ i : Fin 4, i.val < k ∧ (generate (sample ω i)).isSome)

def passRate (k : ℕ) : ℝ := (μ (success k : Set Ω)).toReal

theorem success_one_card : (success 1).card = 8 := by decide
theorem success_two_card : (success 2).card = 12 := by decide
theorem success_four_card : (success 4).card = 15 := by decide

theorem passRate_as_count (k : ℕ) : passRate k = (success k).card / 16 := by
  simp [passRate, μ, Measure.smul_apply, Measure.count_apply_finset,
    ENNReal.toReal_mul]
  ring

theorem pass_one : passRate 1 = 1 / 2 := by
  rw [passRate_as_count, success_one_card]
  norm_num

theorem pass_two : passRate 2 = 3 / 4 := by
  rw [passRate_as_count, success_two_card]
  norm_num

theorem pass_four : passRate 4 = 15 / 16 := by
  rw [passRate_as_count, success_four_card]
  norm_num

theorem log_four : Real.log (4 : ℝ) = 2 * Real.log 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 from by norm_num, Real.log_pow]
  norm_num

theorem no_affine_log_scaling : ¬ ∃ a b : ℝ,
    Real.log (passRate 1) = a + b * Real.log 1 ∧
    Real.log (passRate 2) = a + b * Real.log 2 ∧
    Real.log (passRate 4) = a + b * Real.log 4 := by
  rintro ⟨a, b, h1, h2, h4⟩
  rw [pass_one, Real.log_one, mul_zero, add_zero] at h1
  rw [pass_two] at h2
  rw [pass_four, log_four] at h4
  have hl : Real.log ((15 / 16 : ℝ) * (1 / 2)) =
      Real.log ((3 / 4 : ℝ) ^ 2) := by
    rw [Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    linarith
  have he : (15 / 16 : ℝ) * (1 / 2) = (3 / 4 : ℝ) ^ 2 :=
    Real.log_injOn_pos (by norm_num) (by norm_num) hl
  norm_num at he

theorem exact_scaling_on_sampling_range_false : ¬ ∃ a b : ℝ,
    ∀ k : ℕ, 1 ≤ k → k ≤ 4 → Real.log (passRate k) = a + b * Real.log (k : ℝ) := by
  rintro ⟨a, b, h⟩
  apply no_affine_log_scaling
  refine ⟨a, b, ?_, ?_, ?_⟩
  · simpa only [Nat.cast_one] using h 1 (by norm_num) (by norm_num)
  · simpa only [Nat.cast_ofNat] using h 2 (by norm_num) (by norm_num)
  · simpa only [Nat.cast_ofNat] using h 4 (by norm_num) (by norm_num)

#print axioms mass_one
#print axioms joint_outcome_mass
#print axioms pass_one
#print axioms pass_two
#print axioms pass_four
#print axioms no_affine_log_scaling
#print axioms exact_scaling_on_sampling_range_false

end Conjecture9755
