import Exceptions
import Mathlib.Topology.MetricSpace.HausdorffDimension

open Polynomial MeasureTheory

set_option autoImplicit false
set_option maxSynthPendingDepth 3
noncomputable section
namespace TLMC7768

theorem real_axis_dimension : dimH (Set.range Complex.ofReal) = 1 := by
  have h := Complex.isometry_ofReal.dimH_image (Set.univ : Set ℝ)
  simpa [Real.dimH_univ] using h

theorem candidate_julia_dimension : dimH (juliaSet candidate) ≤ 1 :=
  (dimH_mono julia_real).trans_eq real_axis_dimension

def DimensionClause : Prop :=
  ∀ p : ℂ[X], 2 ≤ p.natDegree → ¬ Exceptional p → 1 < dimH (juliaSet p)

theorem source_counterexample :
    ∃ p : ℂ[X], 2 ≤ p.natDegree ∧
      (∀ n : ℕ, IsAlgebraic ℚ (p.coeff n)) ∧
      ¬ Exceptional p ∧ IsClosed (juliaSet p) ∧
      (juliaSet p).Nonempty ∧ dimH (juliaSet p) ≤ 1 := by
  refine ⟨candidate, ?_, candidate_algebraic_coefficients, candidate_not_exceptional,
    julia_closed candidate, ⟨3, three_mem_julia⟩, candidate_julia_dimension⟩
  simp [candidate_degree]

theorem disproves_dimension_clause : ¬ DimensionClause := by
  intro h
  have hd : 2 ≤ candidate.natDegree := by simp [candidate_degree]
  exact (h candidate hd candidate_not_exceptional).not_ge candidate_julia_dimension

end TLMC7768

#print axioms TLMC7768.source_counterexample
#print axioms TLMC7768.disproves_dimension_clause
