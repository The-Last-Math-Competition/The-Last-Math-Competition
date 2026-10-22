import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Dynamics.OmegaLimit
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FunProp

/-! The formula printed in both source languages has constant second coordinate b.
This is not the usual Henon map with second coordinate b*x. -/
namespace TLMC1491
open Set Function Filter
open scoped ENNReal Topology

abbrev E := EuclideanSpace ℝ (Fin 2)

noncomputable def printedMap (a b : ℝ) (v : E) : E :=
  WithLp.toLp 2 ![1 - a * (v 0) ^ 2 + v 1, b]

theorem printedMap_continuous (a b : ℝ) : Continuous (printedMap a b) := by
  unfold printedMap
  fun_prop

def horizontalLine (b : ℝ) : Set E := {v | v 1 = b}

theorem map_mem_line (a b : ℝ) (v : E) : printedMap a b v ∈ horizontalLine b := by
  rfl

theorem positive_iterate_mem_line (a b : ℝ) (v : E) {n : ℕ} (hn : 0 < n) :
    (printedMap a b)^[n] v ∈ horizontalLine b := by
  cases n with
  | zero => exact False.elim (Nat.lt_irrefl 0 hn)
  | succ n => rw [Function.iterate_succ_apply']; exact map_mem_line a b _

theorem line_isClosed (b : ℝ) : IsClosed (horizontalLine b) := by
  exact isClosed_eq (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1) continuous_const

noncomputable def linePoint (b x : ℝ) : E := WithLp.toLp 2 ![x, b]

theorem linePoint_isometry (b : ℝ) : Isometry (linePoint b) := by
  apply isometry_iff_dist_eq.mpr
  intro x y
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_two]
  simp [linePoint, Real.sqrt_sq (dist_nonneg : 0 ≤ dist x y)]

theorem line_eq_image (b : ℝ) : horizontalLine b = linePoint b '' (univ : Set ℝ) := by
  ext v
  constructor
  · intro hv
    refine ⟨v 0, mem_univ _, ?_⟩
    ext i
    fin_cases i
    · rfl
    · exact hv.symm
  · rintro ⟨x, _, rfl⟩
    rfl

theorem line_dimension (b : ℝ) : dimH (horizontalLine b) = 1 := by
  rw [line_eq_image, (linePoint_isometry b).dimH_image, Real.dimH_univ]

theorem subset_line_dimension_le_one {b : ℝ} {A : Set E} (hA : A ⊆ horizontalLine b) :
    dimH A ≤ 1 := (dimH_mono hA).trans_eq (line_dimension b)

theorem subset_line_dimension_finite {b : ℝ} {A : Set E} (hA : A ⊆ horizontalLine b) :
    dimH A < ⊤ := lt_of_le_of_lt (subset_line_dimension_le_one hA) (by simp)

theorem subset_line_real_dimension_le_one {b : ℝ} {A : Set E} (hA : A ⊆ horizontalLine b) :
    (dimH A).toReal ≤ 1 := by
  have h := ENNReal.toReal_mono (by simp : (1 : ℝ≥0∞) ≠ ⊤)
    (subset_line_dimension_le_one hA)
  simpa using h

noncomputable def forwardOmega (a b : ℝ) (S : Set E) : Set E :=
  omegaLimit atTop (fun n v => (printedMap a b)^[n] v) S

theorem omega_subset_line (a b : ℝ) (S : Set E) : forwardOmega a b S ⊆ horizontalLine b := by
  apply (omegaLimit_subset_closure_image2 atTop
    (fun n v => (printedMap a b)^[n] v) S (u := Ici 1) (eventually_ge_atTop 1)).trans
  apply closure_minimal ?_ (line_isClosed b)
  rintro v ⟨n, hn, x, _, rfl⟩
  exact positive_iterate_mem_line a b x (lt_of_lt_of_le (by decide : 0 < (1 : ℕ)) hn)

theorem omega_dimension_le_one (a b : ℝ) (S : Set E) : dimH (forwardOmega a b S) ≤ 1 :=
  subset_line_dimension_le_one (omega_subset_line a b S)

noncomputable def closedOrbitLimitUnion (a b : ℝ) : Set E :=
  closure (⋃ v : E, forwardOmega a b {v})

theorem closedOrbitLimitUnion_subset_line (a b : ℝ) :
    closedOrbitLimitUnion a b ⊆ horizontalLine b := by
  apply closure_minimal ?_ (line_isClosed b)
  exact iUnion_subset fun v => omega_subset_line a b {v}

theorem closedOrbitLimitUnion_dimension_le_one (a b : ℝ) :
    dimH (closedOrbitLimitUnion a b) ≤ 1 :=
  subset_line_dimension_le_one (closedOrbitLimitUnion_subset_line a b)

theorem fully_invariant_subset_line (a b : ℝ) (A : Set E)
    (hA : printedMap a b '' A = A) : A ⊆ horizontalLine b := by
  intro v hv
  rw [← hA] at hv
  obtain ⟨x, _, rfl⟩ := hv
  exact map_mem_line a b x

theorem fully_invariant_dimension_le_one (a b : ℝ) (A : Set E)
    (hA : printedMap a b '' A = A) : dimH A ≤ 1 :=
  subset_line_dimension_le_one (fully_invariant_subset_line a b A hA)

theorem no_large_compact_fully_invariant_set (a b : ℝ) :
    ¬∃ A : Set E, IsCompact A ∧ printedMap a b '' A = A ∧
      (63 / 50 : ℝ≥0∞) < dimH A := by
  rintro ⟨A, _, hA, hd⟩
  have hbad := lt_of_lt_of_le hd (fully_invariant_dimension_le_one a b A hA)
  norm_num [ENNReal.div_lt_iff] at hbad

theorem no_large_omega_dimension (a b : ℝ) (S : Set E) :
    ¬(63 / 50 : ℝ≥0∞) < dimH (forwardOmega a b S) := by
  intro h
  have hbad := lt_of_lt_of_le h (omega_dimension_le_one a b S)
  norm_num [ENNReal.div_lt_iff] at hbad

theorem no_large_closedOrbitLimitUnion_dimension (a b : ℝ) :
    ¬(63 / 50 : ℝ≥0∞) < dimH (closedOrbitLimitUnion a b) := by
  intro h
  have hbad := lt_of_lt_of_le h (closedOrbitLimitUnion_dimension_le_one a b)
  norm_num [ENNReal.div_lt_iff] at hbad

theorem source_parameters_counterexample :
    (∀ S : Set E, dimH (forwardOmega (7 / 5) (3 / 10) S) ≤ 1) ∧
    dimH (closedOrbitLimitUnion (7 / 5) (3 / 10)) ≤ 1 ∧
    ¬∃ A : Set E, IsCompact A ∧ printedMap (7 / 5) (3 / 10) '' A = A ∧
      (63 / 50 : ℝ≥0∞) < dimH A :=
  ⟨omega_dimension_le_one _ _, closedOrbitLimitUnion_dimension_le_one _ _,
    no_large_compact_fully_invariant_set _ _⟩

theorem source_parameters_real_dimensions :
    (∀ S : Set E, (dimH (forwardOmega (7 / 5) (3 / 10) S)).toReal ≤ 1) ∧
    (dimH (closedOrbitLimitUnion (7 / 5) (3 / 10))).toReal ≤ 1 ∧
    ¬∃ A : Set E, IsCompact A ∧ printedMap (7 / 5) (3 / 10) '' A = A ∧
      (63 / 50 : ℝ) < (dimH A).toReal := by
  refine ⟨fun S => subset_line_real_dimension_le_one (omega_subset_line _ _ S),
    subset_line_real_dimension_le_one (closedOrbitLimitUnion_subset_line _ _), ?_⟩
  rintro ⟨A, _, hA, hd⟩
  have h := subset_line_real_dimension_le_one (fully_invariant_subset_line _ _ A hA)
  linarith

end TLMC1491
