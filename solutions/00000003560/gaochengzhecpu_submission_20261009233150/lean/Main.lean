import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

noncomputable section
open Set MeasureTheory
open scoped Pointwise
namespace Conjecture3560

def A : Set ℝ := Icc 0 1
def B : Set ℝ := Icc 0 2

/-- Euclidean congruence of the original, unscaled summands. -/
def Congruent (S T : Set ℝ) : Prop := ∃ f : ℝ → ℝ, Isometry f ∧ f '' S = T

/-- The equality in Brunn--Minkowski in dimension one. -/
def BMEquality (S T : Set ℝ) : Prop :=
  (volume (S + T)).toReal ^ (1 / 1 : ℝ) =
    (volume S).toReal ^ (1 / 1 : ℝ) + (volume T).toReal ^ (1 / 1 : ℝ)

theorem minkowski_sum : A + B = Icc (0 : ℝ) 3 := by
  ext z
  change (∃ a ∈ A, ∃ b ∈ B, a + b = z) ↔ 0 ≤ z ∧ z ≤ 3
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    change 0 ≤ a ∧ a ≤ 1 at ha
    change 0 ≤ b ∧ b ≤ 2 at hb
    constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]
  · intro hz
    by_cases h : z ≤ 1
    · exact ⟨z, ⟨hz.1, h⟩, 0, ⟨by norm_num, by norm_num⟩, by ring⟩
    · refine ⟨1, ⟨by norm_num, by norm_num⟩, z - 1, ?_, by ring⟩
      change 0 ≤ z - 1 ∧ z - 1 ≤ 2
      constructor <;> linarith [hz.2]

theorem volume_A : (volume A).toReal = 1 := by
  simp [A, Real.volume_Icc]

theorem volume_B : (volume B).toReal = 2 := by
  norm_num [B, Real.volume_Icc]

theorem equality_holds : BMEquality A B := by
  rw [BMEquality, minkowski_sum, volume_A, volume_B]
  norm_num [Real.volume_Icc]

theorem admissible_bodies : IsCompact A ∧ Convex ℝ A ∧ 0 < (volume A).toReal ∧
    IsCompact B ∧ Convex ℝ B ∧ 0 < (volume B).toReal := by
  refine ⟨isCompact_Icc, convex_Icc 0 1, ?_, isCompact_Icc, convex_Icc 0 2, ?_⟩
  · rw [volume_A]; norm_num
  · rw [volume_B]; norm_num

theorem diameter_A : Metric.diam A = 1 := by
  rw [A, Real.diam_Icc (by norm_num)]
  norm_num

theorem diameter_B : Metric.diam B = 2 := by
  rw [B, Real.diam_Icc (by norm_num)]
  norm_num

theorem not_congruent : ¬ Congruent A B := by
  rintro ⟨f, hf, himage⟩
  have hd := hf.diam_image A
  rw [himage, diameter_B, diameter_A] at hd
  norm_num at hd

theorem are_homothetic : (fun x : ℝ => 2 * x) '' A = B := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change 0 ≤ x ∧ x ≤ 1 at hx
    change 0 ≤ 2 * x ∧ 2 * x ≤ 2
    constructor <;> linarith [hx.1, hx.2]
  · intro hy
    change 0 ≤ y ∧ y ≤ 2 at hy
    refine ⟨y / 2, ?_, by ring⟩
    change 0 ≤ y / 2 ∧ y / 2 ≤ 1
    constructor <;> linarith [hy.1, hy.2]

theorem congruence_claim_false :
    ¬ ∀ S T : Set ℝ, IsCompact S → Convex ℝ S → 0 < (volume S).toReal →
      IsCompact T → Convex ℝ T → 0 < (volume T).toReal → BMEquality S T → Congruent S T := by
  intro h
  rcases admissible_bodies with ⟨hA, hcA, hpA, hB, hcB, hpB⟩
  exact not_congruent (h A B hA hcA hpA hB hcB hpB equality_holds)

#print axioms minkowski_sum
#print axioms equality_holds
#print axioms admissible_bodies
#print axioms not_congruent
#print axioms are_homothetic
#print axioms congruence_claim_false
end Conjecture3560
