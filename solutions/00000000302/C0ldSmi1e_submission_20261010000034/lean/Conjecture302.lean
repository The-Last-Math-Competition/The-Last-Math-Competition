import Mathlib.NumberTheory.Transcendental.Liouville.Measure
import Mathlib.Topology.MetricSpace.HausdorffDimension

/-!
# Conjecture 00000000302

The source leaves the domains and the quantification of `p/q` implicit. We use the
usual Diophantine meaning: real `x`, integer `p`, and every positive natural `q`.
The inequality is strict and the constant is uniform in both `p` and `q`.
-/

open Filter Set MeasureTheory
open scoped Topology ENNReal

namespace Conjecture302

/-- The exponent-badly-approximable set in the original assertion. -/
def II (α : ℝ) : Set ℝ :=
  {x | ∃ c : ℝ, 0 < c ∧ ∀ (p : ℤ) (q : ℕ), 0 < q →
    c / (q : ℝ) ^ (2 + α) < |x - (p : ℝ) / q|}

/-- An irrational number without infinitely many approximations at this exponent
has a uniform, strictly positive approximation constant. -/
theorem mem_II_of_not_liouvilleWith {α x : ℝ} (hα : 0 < α)
    (hx : Irrational x) (h : ¬LiouvilleWith (2 + α) x) : x ∈ II α := by
  have hevent : ∀ᶠ q : ℕ in atTop, ∀ p : ℤ,
      1 / (q : ℝ) ^ (2 + α) ≤ |x - (p : ℝ) / q| := by
    have hn : ¬∃ᶠ q : ℕ in atTop, ∃ p : ℤ,
        x ≠ (p : ℝ) / q ∧ |x - (p : ℝ) / q| < 1 / (q : ℝ) ^ (2 + α) :=
      fun hf => h ⟨1, hf⟩
    filter_upwards [not_frequently.mp hn] with q hq p
    apply le_of_not_gt
    intro hp
    apply hq
    refine ⟨p, ?_, hp⟩
    simpa only [Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast] using
      hx.ne_rat ((p : ℚ) / q)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hevent
  obtain ⟨ε, hε, hsep⟩ :=
    (hx.eventually_forall_le_dist_cast_div_of_denom_le N).exists_gt
  let c : ℝ := min 1 ε / 2
  have hc : 0 < c := div_pos (lt_min zero_lt_one hε) (by norm_num)
  have hcmin : c < min 1 ε := by dsimp [c]; linarith [lt_min zero_lt_one hε]
  have hc1 : c < 1 := hcmin.trans_le (min_le_left _ _)
  have hcε : c < ε := hcmin.trans_le (min_le_right _ _)
  refine ⟨c, hc, ?_⟩
  intro p q hq
  have hqreal : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hp : 0 < (q : ℝ) ^ (2 + α) := Real.rpow_pos_of_pos hqreal _
  by_cases hNq : N ≤ q
  · exact (div_lt_div_of_pos_right hc1 hp).trans_le (hN q hNq p)
  · have hqone : (1 : ℝ) ≤ q := by exact_mod_cast hq
    have hpowone : (1 : ℝ) ≤ (q : ℝ) ^ (2 + α) :=
      Real.one_le_rpow hqone (by linarith)
    have hsmall : ε ≤ |x - (p : ℝ) / q| := by
      simpa only [Real.dist_eq] using hsep q (le_of_lt (lt_of_not_ge hNq)) p
    exact (div_le_self hc.le hpowone).trans_lt (hcε.trans_le hsmall)

/-- Irrational numbers form a set of full Lebesgue measure. -/
theorem ae_irrational : ∀ᵐ x : ℝ, Irrational x :=
  (countable_range (Rat.cast : ℚ → ℝ)).ae_not_mem volume

/-- For every positive parameter, the original set has full Lebesgue measure. -/
theorem ae_mem_II {α : ℝ} (hα : 0 < α) : ∀ᵐ x : ℝ, x ∈ II α := by
  filter_upwards [ae_irrational, ae_not_liouvilleWith] with x hx hxl
  exact mem_II_of_not_liouvilleWith hα hx (hxl (2 + α) (by linarith))

/-- A full-Lebesgue-measure subset of the real line has Hausdorff dimension one. -/
theorem dimH_eq_one_of_ae_mem {s : Set ℝ} (hs : ∀ᵐ x : ℝ, x ∈ s) : dimH s = 1 := by
  apply le_antisymm
  · exact (dimH_mono (subset_univ s)).trans_eq Real.dimH_univ
  · have heq : s =ᵐ[volume] (univ : Set ℝ) := by
      filter_upwards [hs] with x hx
      exact propext (iff_of_true hx (mem_univ x))
    have hv : volume s = ∞ := by rw [measure_congr heq, Real.volume_univ]
    have hh : (MeasureTheory.Measure.hausdorffMeasure 1 : Measure ℝ) s = ∞ := by
      rwa [hausdorffMeasure_real]
    simpa using le_dimH_of_hausdorffMeasure_eq_top (d := 1) hh

/-- Every positive exponent parameter gives Hausdorff dimension one. -/
theorem dimH_II {α : ℝ} (hα : 0 < α) : dimH (II α) = 1 :=
  dimH_eq_one_of_ae_mem (ae_mem_II hα)

/-- Intersections at any two positive parameters have Hausdorff dimension one. -/
theorem dimH_inter_II {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    dimH (II α ∩ II β) = 1 :=
  dimH_eq_one_of_ae_mem ((ae_mem_II hα).and (ae_mem_II hβ))

/-- The conjecture, with its original parameters and strict approximation inequality. -/
theorem conjecture : dimH (II (1 / 3) ∩ II (1 / 2)) = dimH (II (1 / 2)) := by
  rw [dimH_inter_II (by norm_num) (by norm_num), dimH_II (by norm_num)]

end Conjecture302
