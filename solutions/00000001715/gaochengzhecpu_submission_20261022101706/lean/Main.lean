import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Data.Real.Irrational
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open Filter
open scoped Topology

namespace Conjecture1715

/-- The usual additive character `e(t) = exp(2 pi i t)`. -/
noncomputable def character (t : ℝ) : ℂ :=
  Complex.exp ((t : ℂ) * (2 * Real.pi * Complex.I))

/-- Index `n` represents the positive Fourier frequency `k = n+1`. -/
noncomputable def coefficient (α : ℝ) (n : ℕ) : ℂ :=
  (1 - character ((n + 1 : ℕ) * α))⁻¹

theorem character_ne_one {α : ℝ} (hα : Irrational α) {k : ℕ} (hk : k ≠ 0) :
    character (k * α) ≠ 1 := by
  intro h
  obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.mp h
  have heq : ((k * α : ℝ) : ℂ) = (m : ℂ) :=
    mul_right_cancel₀ Complex.two_pi_I_ne_zero hm
  have hr : (k : ℝ) * α = (m : ℝ) := by exact_mod_cast heq
  exact (hα.natCast_mul hk).ne_int m hr

theorem character_norm (t : ℝ) : ‖character t‖ = 1 := by
  simp [character, Complex.norm_exp]

theorem denominator_ne_zero {α : ℝ} (hα : Irrational α) (n : ℕ) :
    1 - character ((n + 1 : ℕ) * α) ≠ 0 := by
  exact sub_ne_zero.mpr (Ne.symm (character_ne_one hα (Nat.succ_ne_zero n)))

theorem coefficient_norm_lower_bound {α : ℝ} (hα : Irrational α) (n : ℕ) :
    (1 / 2 : ℝ) ≤ ‖coefficient α n‖ := by
  have hpos : 0 < ‖1 - character ((n + 1 : ℕ) * α)‖ :=
    norm_pos_iff.mpr (denominator_ne_zero hα n)
  have hupper : ‖1 - character ((n + 1 : ℕ) * α)‖ ≤ 2 := by
    calc
      _ ≤ ‖(1 : ℂ)‖ + ‖character ((n + 1 : ℕ) * α)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_one, character_norm]; norm_num
  rw [coefficient, norm_inv]
  simpa only [one_div] using one_div_le_one_div_of_le hpos hupper

theorem coefficient_not_tendsto_zero {α : ℝ} (hα : Irrational α) :
    ¬ Tendsto (coefficient α) atTop (𝓝 0) := by
  intro h
  have hlower : ∀ᶠ n in atTop, (1 / 2 : ℝ) ≤ ‖coefficient α n‖ :=
    Filter.Eventually.of_forall (coefficient_norm_lower_bound hα)
  have hlim : Tendsto (fun n : ℕ => ‖coefficient α n‖) atTop (𝓝 ‖(0 : ℂ)‖) := h.norm
  have hle : (1 / 2 : ℝ) ≤ ‖(0 : ℂ)‖ := ge_of_tendsto hlim hlower
  norm_num at hle

/-- The explicit decay assertion required by the source, for irrational rotations. -/
def DecayAssertion : Prop :=
  ∀ α : ℝ, Irrational α → Tendsto (coefficient α) atTop (𝓝 0)

theorem sqrt_two_counterexample :
    Irrational (Real.sqrt 2) ∧
      ¬ Tendsto (coefficient (Real.sqrt 2)) atTop (𝓝 0) :=
  ⟨irrational_sqrt_two, coefficient_not_tendsto_zero irrational_sqrt_two⟩

theorem disprove_decay_assertion : ¬ DecayAssertion := by
  intro h
  exact sqrt_two_counterexample.2 (h _ sqrt_two_counterexample.1)

end Conjecture1715

#print axioms Conjecture1715.coefficient_norm_lower_bound
#print axioms Conjecture1715.coefficient_not_tendsto_zero
#print axioms Conjecture1715.sqrt_two_counterexample
#print axioms Conjecture1715.disprove_decay_assertion
