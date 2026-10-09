import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

open Filter
open scoped Topology Asymptotics

namespace GenericRate

/-- A reciprocal-linear lower bound forces the quadratic normalization to diverge. -/
theorem quadratic_tendsto_atTop (D : ℕ → ℝ)
    (hD : ∀ N : ℕ, 1 / (4 * ((N : ℝ) + 1)) ≤ D N) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ 2 * D N) atTop atTop := by
  have hlin : Tendsto (fun N : ℕ => (N : ℝ) / 8) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_div_const (by norm_num)
  refine tendsto_atTop_mono' atTop ?_ hlin
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hpos : 0 < 4 * ((N : ℝ) + 1) := by positivity
  calc
    (N : ℝ) / 8 ≤ (N : ℝ) ^ 2 * (1 / (4 * ((N : ℝ) + 1))) := by
      rw [mul_one_div, le_div_iff₀ hpos]
      nlinarith
    _ ≤ (N : ℝ) ^ 2 * D N := mul_le_mul_of_nonneg_left (hD N) (sq_nonneg _)

/-- In particular, the quadratic normalization cannot approach any finite constant. -/
theorem quadratic_not_tendsto_nhds (D : ℕ → ℝ)
    (hD : ∀ N : ℕ, 1 / (4 * ((N : ℝ) + 1)) ≤ D N) (c : ℝ) :
    ¬ Tendsto (fun N : ℕ => (N : ℝ) ^ 2 * D N) atTop (𝓝 c) :=
  not_tendsto_nhds_of_tendsto_atTop (quadratic_tendsto_atTop D hD) c

/-- The ratio to every positive inverse-square candidate diverges to infinity. -/
theorem inverse_square_ratio_tendsto_atTop (D : ℕ → ℝ)
    (hD : ∀ N : ℕ, 1 / (4 * ((N : ℝ) + 1)) ≤ D N) (c : ℝ) (hc : 0 < c) :
    Tendsto (fun N : ℕ => D N / (c / (N : ℝ) ^ 2)) atTop atTop := by
  convert (quadratic_tendsto_atTop D hD).atTop_div_const hc using 1
  ext N
  rw [div_div_eq_mul_div]
  ring

/-- The asymptotic ratio asserted by an inverse-square law cannot tend to one. -/
theorem inverse_square_ratio_not_tendsto_one (D : ℕ → ℝ)
    (hD : ∀ N : ℕ, 1 / (4 * ((N : ℝ) + 1)) ≤ D N) (c : ℝ) (hc : 0 < c) :
    ¬ Tendsto (fun N : ℕ => D N / (c / (N : ℝ) ^ 2)) atTop (𝓝 1) :=
  not_tendsto_nhds_of_tendsto_atTop (inverse_square_ratio_tendsto_atTop D hD c hc) 1

/-- A reciprocal-linear lower bound rules out asymptotic equivalence to `c / N²`. -/
theorem not_isEquivalent_inverse_square (D : ℕ → ℝ)
    (hD : ∀ N : ℕ, 1 / (4 * ((N : ℝ) + 1)) ≤ D N) (c : ℝ) (hc : 0 < c) :
    ¬ (D ~[atTop] (fun N : ℕ => c / (N : ℝ) ^ 2)) := by
  intro h
  have hz : ∀ᶠ N : ℕ in atTop, c / (N : ℝ) ^ 2 ≠ 0 := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hn : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    exact div_ne_zero (ne_of_gt hc) (pow_ne_zero _ (ne_of_gt hn))
  exact inverse_square_ratio_not_tendsto_one D hD c hc
    ((Asymptotics.isEquivalent_iff_tendsto_one hz).mp h)

/-- The literal real-power spelling used by the dimension-two conjecture. -/
theorem real_power_ratio_tendsto_atTop (D : ℕ → ℝ)
    (hD : ∀ N : ℕ, 1 / (4 * ((N : ℝ) + 1)) ≤ D N) (c : ℝ) (hc : 0 < c) :
    Tendsto (fun N : ℕ => D N / (c * (N : ℝ) ^ (-2 : ℝ))) atTop atTop := by
  simpa only [Real.rpow_neg (Nat.cast_nonneg _), Real.rpow_two, ← div_eq_mul_inv]
    using inverse_square_ratio_tendsto_atTop D hD c hc

/-- In dimension two the asserted real-power asymptotic ratio cannot tend to one. -/
theorem real_power_ratio_not_tendsto_one (D : ℕ → ℝ)
    (hD : ∀ N : ℕ, 1 / (4 * ((N : ℝ) + 1)) ≤ D N) (c : ℝ) (hc : 0 < c) :
    ¬ Tendsto (fun N : ℕ => D N / (c * (N : ℝ) ^ (-2 : ℝ))) atTop (𝓝 1) :=
  not_tendsto_nhds_of_tendsto_atTop (real_power_ratio_tendsto_atTop D hD c hc) 1

/-- No positive constant yields the conjectured dimension-two asymptotic equivalence. -/
theorem not_isEquivalent_real_power (D : ℕ → ℝ)
    (hD : ∀ N : ℕ, 1 / (4 * ((N : ℝ) + 1)) ≤ D N) (c : ℝ) (hc : 0 < c) :
    ¬ (D ~[atTop] (fun N : ℕ => c * (N : ℝ) ^ (-2 : ℝ))) := by
  simpa only [Real.rpow_neg (Nat.cast_nonneg _), Real.rpow_two, ← div_eq_mul_inv]
    using not_isEquivalent_inverse_square D hD c hc

end GenericRate
