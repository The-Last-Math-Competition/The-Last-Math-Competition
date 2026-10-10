import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Semicontinuous
import Mathlib.Analysis.Convex.Basic
import Mathlib.Tactic

/-! A fixed symmetric two-atom probability law and its good, nonconvex rate function. -/

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology
attribute [local instance] Classical.propDecidable

namespace Conjecture2821

def support : Set ℝ := {-1, 1}

def law : Measure ℝ := (2 : ℝ≥0∞)⁻¹ • Measure.dirac (-1) +
  (2 : ℝ≥0∞)⁻¹ • Measure.dirac 1

def rate (x : ℝ) : ℝ≥0∞ := if x ∈ support then 0 else ⊤

theorem support_compact : IsCompact support := by
  exact ((Set.finite_singleton (1 : ℝ)).insert (-1)).isCompact

theorem support_closed : IsClosed support := support_compact.isClosed

@[simp] theorem rate_neg_one : rate (-1) = 0 := by simp [rate, support]
@[simp] theorem rate_one : rate 1 = 0 := by simp [rate, support]
@[simp] theorem rate_zero : rate 0 = ⊤ := by norm_num [rate, support]

theorem rate_sublevel {r : ℝ≥0∞} (hr : r ≠ ⊤) : {x | rate x ≤ r} = support := by
  ext x
  by_cases hx : x ∈ support
  · simp [rate, hx]
  · simp [rate, hx, top_le_iff, hr]

theorem rate_lowerSemicontinuous : LowerSemicontinuous rate := by
  rw [lowerSemicontinuous_iff_isClosed_preimage]
  intro r
  by_cases hr : r = ⊤
  · simp [hr]
  · change IsClosed {x | rate x ≤ r}
    rw [rate_sublevel hr]
    exact support_closed

theorem rate_good (r : ℝ≥0) : IsCompact {x | rate x ≤ (r : ℝ≥0∞)} := by
  rw [rate_sublevel ENNReal.coe_ne_top]
  exact support_compact

theorem rate_proper : ∃ x, rate x < ⊤ := ⟨1, by simp⟩

theorem exact_zero_level : {x | rate x = 0} = support := by
  ext x
  simp [rate]

theorem support_not_convex : ¬ Convex ℝ support := by
  intro h
  have hmid := h (by simp [support] : (-1 : ℝ) ∈ support)
    (by simp [support] : (1 : ℝ) ∈ support)
    (by norm_num : 0 ≤ (1 / 2 : ℝ)) (by norm_num : 0 ≤ (1 / 2 : ℝ))
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  norm_num [support] at hmid

theorem every_finite_sublevel_not_convex (r : ℝ≥0) :
    ¬ Convex ℝ {x | rate x ≤ (r : ℝ≥0∞)} := by
  rw [rate_sublevel ENNReal.coe_ne_top]
  exact support_not_convex

theorem zero_exact_level_not_convex : ¬ Convex ℝ {x | rate x = 0} := by
  rw [exact_zero_level]
  exact support_not_convex

theorem law_apply (A : Set ℝ) : law A =
    (if (-1 : ℝ) ∈ A then (2 : ℝ≥0∞)⁻¹ else 0) +
    (if (1 : ℝ) ∈ A then (2 : ℝ≥0∞)⁻¹ else 0) := by
  classical
  simp only [law, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply,
    smul_eq_mul, Set.indicator_apply, Pi.one_apply]
  split_ifs <;> simp

instance law_probability : IsProbabilityMeasure law where
  measure_univ := by
    rw [law_apply]
    norm_num only [Set.mem_univ, if_true]
    rw [← two_mul, ENNReal.mul_inv_cancel]
    · norm_num
    · norm_num

theorem law_ne_top (A : Set ℝ) : law A ≠ ⊤ := measure_ne_top law A

theorem law_pos_iff (A : Set ℝ) : law A ≠ 0 ↔ ∃ x ∈ A, x ∈ support := by
  classical
  rw [law_apply]
  by_cases hm : (-1 : ℝ) ∈ A <;> by_cases hp : (1 : ℝ) ∈ A <;>
    simp [hm, hp, support] <;> aesop

theorem rate_inf_of_hits {A : Set ℝ} (h : ∃ x ∈ A, x ∈ support) :
    (⨅ x ∈ A, rate x) = 0 := by
  obtain ⟨x, hxA, hxs⟩ := h
  apply le_antisymm _ (zero_le _)
  exact (iInf₂_le x hxA).trans (by simp [rate, hxs])

theorem rate_inf_of_misses {A : Set ℝ} (h : ¬ ∃ x ∈ A, x ∈ support) :
    (⨅ x ∈ A, rate x) = ⊤ := by
  apply top_unique
  refine le_iInf fun x => le_iInf fun hx => ?_
  have hs : x ∉ support := fun hs => h ⟨x, hx, hs⟩
  simp [rate, hs]

end Conjecture2821
