import Mathlib.Combinatorics.SimpleGraph.Dart
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace Conjecture7915
open scoped BigOperators
open SimpleGraph Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Legal consecutive oriented edges with immediate reversal excluded. -/
def follows (d e : G.Dart) : Prop := d.snd = e.fst ∧ e.snd ≠ d.fst

instance (d e : G.Dart) : Decidable (follows G d e) := by
  unfold follows
  infer_instance

def successors (d : G.Dart) : Finset G.Dart :=
  Finset.univ.filter (follows G d)

def nonbacktracking : Matrix G.Dart G.Dart ℂ := fun d e =>
  if follows G d e then 1 else 0

theorem successors_card_le (hdegree : ∀ v, G.degree v = 3) (d : G.Dart) :
    (successors G d).card ≤ 2 := by
  have hcard : (successors G d).card ≤
      ((G.neighborFinset d.snd).erase d.fst).card := by
    apply Finset.card_le_card_of_injOn (fun e : G.Dart => e.snd)
    · intro e he
      have hf := (Finset.mem_filter.mp he).2
      change d.snd = e.fst ∧ e.snd ≠ d.fst at hf
      apply Finset.mem_erase.mpr
      refine ⟨hf.2, ?_⟩
      rw [SimpleGraph.mem_neighborFinset, hf.1]
      exact e.adj
    · intro e he f hf hef
      have he' := (Finset.mem_filter.mp he).2.1
      have hf' := (Finset.mem_filter.mp hf).2.1
      apply SimpleGraph.Dart.ext
      exact Prod.ext (he'.symm.trans hf') hef
  have hmem : d.fst ∈ G.neighborFinset d.snd := by
    exact (SimpleGraph.mem_neighborFinset G d.snd d.fst).mpr d.adj.symm
  rw [Finset.card_erase_of_mem hmem, SimpleGraph.card_neighborFinset_eq_degree,
    hdegree] at hcard
  exact hcard

theorem nonbacktracking_mulVec (x : G.Dart → ℂ) (d : G.Dart) :
    (nonbacktracking G *ᵥ x) d = ∑ e ∈ successors G d, x e := by
  simp [nonbacktracking, Matrix.mulVec, dotProduct, successors,
    Finset.sum_filter]

theorem row_norm_bound (hdegree : ∀ v, G.degree v = 3)
    (x : G.Dart → ℂ) (d a : G.Dart) (hmax : ∀ e, ‖x e‖ ≤ ‖x a‖) :
    ‖(nonbacktracking G *ᵥ x) d‖ ≤ 2 * ‖x a‖ := by
  rw [nonbacktracking_mulVec]
  calc
    ‖∑ e ∈ successors G d, x e‖ ≤ ∑ e ∈ successors G d, ‖x e‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _e ∈ successors G d, ‖x a‖ :=
      Finset.sum_le_sum (fun e _ => hmax e)
    _ = ((successors G d).card : ℝ) * ‖x a‖ := by simp
    _ ≤ 2 * ‖x a‖ := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast successors_card_le G hdegree d)
        (norm_nonneg _)

/-- The denominator in the actual Hashimoto determinant formula for Ihara zeta. -/
noncomputable def iharaDenominator (u : ℂ) : ℂ :=
  Matrix.det (1 - u • nonbacktracking G)

theorem ihara_denominator_nonzero (hdegree : ∀ v, G.degree v = 3)
    (u : ℂ) (hu : ‖u‖ < 1 / 2) : iharaDenominator G u ≠ 0 := by
  intro hz
  obtain ⟨x, hx, hker⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hz
  have hex : ∃ d : G.Dart, x d ≠ 0 := by
    by_contra hn
    apply hx
    funext d
    simpa using not_exists.mp hn d
  obtain ⟨d, hd⟩ := hex
  have hne : (Finset.univ : Finset G.Dart).Nonempty := ⟨d, Finset.mem_univ d⟩
  obtain ⟨a, _, hmax⟩ := Finset.exists_max_image Finset.univ (fun e => ‖x e‖) hne
  have hm : ∀ e, ‖x e‖ ≤ ‖x a‖ := fun e => hmax e (Finset.mem_univ e)
  have hpos : 0 < ‖x a‖ := lt_of_lt_of_le (norm_pos_iff.mpr hd) (hm d)
  have hentry := congrFun hker a
  have heq : x a = u * (nonbacktracking G *ᵥ x) a := by
    simpa [Matrix.sub_mulVec, Matrix.smul_mulVec_assoc, sub_eq_zero] using hentry
  have hn : ‖x a‖ ≤ ‖u‖ * (2 * ‖x a‖) := by
    calc
      ‖x a‖ = ‖u‖ * ‖(nonbacktracking G *ᵥ x) a‖ := by rw [heq, norm_mul]
      _ ≤ ‖u‖ * (2 * ‖x a‖) :=
        mul_le_mul_of_nonneg_left (row_norm_bound G hdegree x a a hm) (norm_nonneg _)
  nlinarith

theorem every_pole_modulus_ge_half (hdegree : ∀ v, G.degree v = 3)
    {u : ℂ} (hu : iharaDenominator G u = 0) : (1 : ℝ) / 2 ≤ ‖u‖ := by
  by_contra h
  exact ihara_denominator_nonzero G hdegree u (lt_of_not_ge h) hu

noncomputable def claimedRadius : ℝ := 1 / (2 * Real.sqrt 2)

theorem claimed_radius_positive : 0 < claimedRadius := by
  unfold claimedRadius
  positivity

theorem claimed_radius_lt_half : claimedRadius < 1 / 2 := by
  have hs : 1 < Real.sqrt 2 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  unfold claimedRadius
  apply (div_lt_div_iff₀ (by positivity) (by norm_num)).mpr
  nlinarith

theorem uniform_separation_from_claimed_circle
    (hdegree : ∀ v, G.degree v = 3) {u w : ℂ}
    (hu : iharaDenominator G u = 0) (hw : ‖w‖ = claimedRadius) :
    0 < 1 / 2 - claimedRadius ∧ 1 / 2 - claimedRadius ≤ dist u w := by
  refine ⟨sub_pos.mpr claimed_radius_lt_half, ?_⟩
  have hp := every_pole_modulus_ge_half G hdegree hu
  have ht := norm_sub_norm_le u w
  rw [hw, ← dist_eq_norm] at ht
  linarith

/-- The hypotheses are realized by a concrete connected cubic graph. -/
theorem concrete_cubic_graph :
    ∀ v : Fin 4, (⊤ : SimpleGraph (Fin 4)).degree v = 3 := by decide

#print axioms successors_card_le
#print axioms ihara_denominator_nonzero
#print axioms every_pole_modulus_ge_half
#print axioms uniform_separation_from_claimed_circle
end Conjecture7915
