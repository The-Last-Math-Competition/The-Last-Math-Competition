import Mathlib.Analysis.Normed.Group.Int
import Mathlib.Topology.Instances.Int
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

namespace CompleteNotGeodesic
/-- A constant-speed minimizing segment from x to y on the unit interval. -/
def IsSegment {X : Type*} [MetricSpace X] (γ : Set.Icc (0 : ℝ) 1 → X) (x y : X) : Prop :=
  γ ⟨0, by norm_num⟩ = x ∧ γ ⟨1, by norm_num⟩ = y ∧
  ∀ s t, dist (γ s) (γ t) = |(s : ℝ) - (t : ℝ)| * dist x y

theorem integers_complete : CompleteSpace ℤ := inferInstance

theorem no_half_distance (z : ℤ) : dist z 0 ≠ (1 / 2 : ℝ) := by
  intro h
  have h' : (2 : ℝ) * (z.natAbs : ℝ) = 1 := by
    simpa [Int.dist_eq, Int.norm_eq_abs, ← Int.cast_abs, ← Int.natCast_natAbs] using (by linarith : 2 * dist z 0 = 1)
  have h'' : 2 * z.natAbs = 1 := by exact_mod_cast h'
  omega

theorem no_segment_zero_one :
    ¬ ∃ γ : Set.Icc (0 : ℝ) 1 → ℤ, IsSegment γ 0 1 := by
  rintro ⟨γ, h0, _, hd⟩
  have h := hd ⟨1 / 2, by norm_num⟩ ⟨0, by norm_num⟩
  rw [h0] at h
  apply no_half_distance (γ ⟨1 / 2, by norm_num⟩)
  have hz : dist (0 : ℤ) 1 = 1 := by norm_num [Int.dist_eq]
  simp only [hz, mul_one, sub_zero] at h
  exact h.trans (abs_of_nonneg (by norm_num))

#print axioms no_segment_zero_one
#print axioms integers_complete
end CompleteNotGeodesic
