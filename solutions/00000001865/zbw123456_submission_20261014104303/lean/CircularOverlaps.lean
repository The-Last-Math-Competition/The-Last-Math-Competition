import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NormNum

namespace CircularOverlaps
open MeasureTheory
open scoped ComplexConjugate

/-- The exact formula printed in Conjecture 00000001865. -/
noncomputable def predicted (N β i : ℝ) : ℝ :=
  N ^ (-2 + 2 * β) * (i * (N - i)) ^ (β - 1)

/-- Even without any random-matrix assumptions the two claimed formulae
at N=2, beta=2, i=1 are incompatible. -/
theorem incompatible_specialization :
    ¬ ∃ m : ℝ, m = predicted 2 2 1 ∧ m = (2 : ℝ) ^ (-2 : ℝ) := by
  norm_num [predicted, Real.rpow_neg, Real.rpow_natCast]

/-- The actual overlap of any two distinct vectors from any orthonormal
family is zero, under any measure on the sampling space. -/
theorem mean_overlap_zero {Ω E ι : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (μ : Measure Ω) (v : Ω → ι → E) (hv : ∀ ω, Orthonormal ℂ (v ω))
    (i j : ι) (hij : i ≠ j) :
    (∫ ω, ‖inner (𝕜 := ℂ) (v ω i) (v ω j)‖ ^ 2 ∂μ) = 0 := by
  have hz : (fun ω => ‖inner (𝕜 := ℂ) (v ω i) (v ω j)‖ ^ 2) =
      (fun _ : Ω => (0 : ℝ)) := by
    funext ω
    simp [(hv ω).inner_eq_zero hij]
  rw [hz, integral_zero]

/-- A mean function satisfying the conjecture would specialize to the
impossible numerical pair above. -/
theorem conjecture_false : ¬ ∃ m : ℕ → ℝ → ℕ → ℝ,
    (∀ N : ℕ, 2 ≤ N → ∀ β : ℝ, 0 < β → ∀ i : ℕ, 1 ≤ i → i < N →
      m N β i = predicted N β i) ∧
    (∀ N : ℕ, 2 ≤ N → ∀ i : ℕ, 1 ≤ i → i < N →
      m N 2 i = (N : ℝ) ^ (-2 : ℝ)) := by
  rintro ⟨m, h, hs⟩
  apply incompatible_specialization
  refine ⟨m 2 2 1, ?_, ?_⟩
  · simpa using h 2 (by decide) 2 (by norm_num) 1 (by decide) (by decide)
  · simpa using hs 2 (by decide) 1 (by decide) (by decide)
#print axioms conjecture_false
#print axioms mean_overlap_zero
end CircularOverlaps
