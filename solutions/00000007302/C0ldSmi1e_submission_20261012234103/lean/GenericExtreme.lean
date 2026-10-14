import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.NormedSpace.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum

open Set Metric

namespace GenericExtreme

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E]

/-- Every extreme point of the closed unit ball of a nontrivial real normed space
belongs to its unit sphere. -/
theorem extremePoints_closedBall_subset_sphere :
    (closedBall (0 : E) 1).extremePoints ℝ ⊆ sphere (0 : E) 1 := by
  intro x hx
  have hxle : ‖x‖ ≤ 1 := by simpa using hx.1
  have hxeq : ‖x‖ = 1 := by
    by_contra hne
    have hxlt : ‖x‖ < 1 := lt_of_le_of_ne hxle hne
    obtain ⟨y, hy⟩ := exists_norm_eq E (show 0 ≤ (1 - ‖x‖) / 2 by linarith)
    have hyne : y ≠ 0 := by
      intro hz
      rw [hz, norm_zero] at hy
      linarith
    have hplus : x + y ∈ closedBall (0 : E) 1 := by
      simp only [mem_closedBall, dist_zero_right]
      have h := norm_add_le x y
      rw [hy] at h
      linarith
    have hminus : x - y ∈ closedBall (0 : E) 1 := by
      simp only [mem_closedBall, dist_zero_right]
      have h := norm_sub_le x y
      rw [hy] at h
      linarith
    have hsegment : x ∈ openSegment ℝ (x + y) (x - y) := by
      refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
      module
    have heq : x + y = x := (hx.2 hplus hminus hsegment).1
    exact hyne (add_left_cancel (heq.trans (add_zero x).symm))
  simpa using hxeq

/-- The extreme points are not dense relative to the closed unit ball:
the ball itself is not contained in their ambient closure. -/
theorem closedBall_not_subset_closure_extremePoints :
    ¬ closedBall (0 : E) 1 ⊆ closure ((closedBall (0 : E) 1).extremePoints ℝ) := by
  intro h
  have hclosure : closure ((closedBall (0 : E) 1).extremePoints ℝ) ⊆
      sphere (0 : E) 1 :=
    closure_minimal extremePoints_closedBall_subset_sphere isClosed_sphere
  have hz : (0 : E) ∈ sphere (0 : E) 1 := hclosure (h (by simp))
  simp at hz

end GenericExtreme
