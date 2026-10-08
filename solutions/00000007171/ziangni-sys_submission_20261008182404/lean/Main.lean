import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Tactic

noncomputable section
open scoped Matrix
namespace FixedTrace

abbrev M := Matrix (Fin 2) (Fin 2) ℝ
def A (t : ℝ) : M := Matrix.diagonal ![t, 1-t]
def Feasible (B : M) : Prop := B.IsHermitian ∧ Matrix.trace B = 1

theorem symmetric (t : ℝ) : (A t).IsHermitian := by
  simp [A, Matrix.IsHermitian]

theorem trace_one (t : ℝ) : Matrix.trace (A t) = 1 := by
  simp [A, Matrix.trace, Fin.sum_univ_two]

theorem feasible (t : ℝ) : Feasible (A t) := ⟨symmetric t, trace_one t⟩

theorem spectrum_exact (t : ℝ) : spectrum ℝ (A t) = {t, 1-t} := by
  ext z
  have hd : (algebraMap ℝ M z - A t).det = (z-t)*(z-(1-t)) := by
    simp [Matrix.det_fin_two, Matrix.algebraMap_eq_diagonal, A]
  simp [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, hd,
    isUnit_iff_ne_zero, mul_eq_zero, sub_eq_zero]
  tauto

/-- The genuine extremal spectral value for the displayed symmetric family. -/
def largestEigenvalue (B : M) : ℝ := sSup (spectrum ℝ B)
def spectralRadius (B : M) : ℝ := sSup ((fun z : ℝ => |z|) '' spectrum ℝ B)

theorem largest_exact (t : ℝ) (ht : 1 ≤ t) : largestEigenvalue (A t) = t := by
  rw [largestEigenvalue, spectrum_exact, csSup_pair]
  exact max_eq_left (by linarith)

theorem largest_is_attained (t : ℝ) (ht : 1 ≤ t) :
    IsGreatest (spectrum ℝ (A t)) t := by
  rw [spectrum_exact]
  constructor
  · simp
  · intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl <;> linarith

theorem radius_exact (t : ℝ) (ht : 1 ≤ t) : spectralRadius (A t) = t := by
  have h0 : 0 ≤ t := by linarith
  have h1 : 1-t ≤ 0 := by linarith
  simp only [spectralRadius, spectrum_exact, Set.image_insert_eq, Set.image_singleton,
    csSup_pair, abs_of_nonneg h0, abs_of_nonpos h1]
  exact max_eq_left (by linarith)

theorem unbounded_largest : ∀ C : ℝ, ∃ B : M,
    Feasible B ∧ C < largestEigenvalue B := by
  intro C
  refine ⟨A (|C|+1), feasible _, ?_⟩
  rw [largest_exact _ (by linarith [abs_nonneg C])]
  have := le_abs_self C
  linarith

theorem unbounded_radius : ∀ C : ℝ, ∃ B : M,
    Feasible B ∧ C < spectralRadius B := by
  intro C
  refine ⟨A (|C|+1), feasible _, ?_⟩
  rw [radius_exact _ (by linarith [abs_nonneg C])]
  have := le_abs_self C
  linarith

theorem no_finite_bound : ¬ ∃ C : ℝ, ∀ B : M,
    Feasible B → largestEigenvalue B ≤ C := by
  rintro ⟨C, hC⟩
  obtain ⟨B, hB, hlt⟩ := unbounded_largest C
  exact (not_lt_of_ge (hC B hB)) hlt

/-- There is no extremizer in the whole fixed-trace symmetric class. -/
theorem no_maximizer : ¬ ∃ B : M, Feasible B ∧ ∀ D : M,
    Feasible D → largestEigenvalue D ≤ largestEigenvalue B := by
  rintro ⟨B, _, hB⟩
  obtain ⟨D, hD, hlt⟩ := unbounded_largest (largestEigenvalue B)
  exact (not_lt_of_ge (hB D hD)) hlt

theorem concentrated_loses : Feasible (A 1) ∧ Feasible (A 2) ∧
    largestEigenvalue (A 1) = 1 ∧ largestEigenvalue (A 2) = 2 := by
  exact ⟨feasible _, feasible _, largest_exact _ (by norm_num), largest_exact _ (by norm_num)⟩

/-- Strict majorization in dimension two, for descending spectral lists:
strict first-prefix inequality and equality of the full sums. -/
def StrictlyMajorizesTwo (x y : Fin 2 → ℝ) : Prop :=
  y 1 ≤ y 0 ∧ x 1 ≤ x 0 ∧ y 0 < x 0 ∧ x 0 + x 1 = y 0 + y 1

/-- Every ordered trace-one spectral list is strictly majorized by the
actual spectrum of another feasible matrix. -/
theorem no_majorization_maximal_list (y : Fin 2 → ℝ)
    (horder : y 1 ≤ y 0) (htrace : y 0 + y 1 = 1) :
    ∃ t : ℝ, 1 ≤ t ∧ Feasible (A t) ∧
      spectrum ℝ (A t) = {t, 1-t} ∧ StrictlyMajorizesTwo ![t, 1-t] y := by
  refine ⟨|y 0|+1, by linarith [abs_nonneg (y 0)], feasible _, spectrum_exact _, ?_⟩
  have habs := le_abs_self (y 0)
  have hnonneg := abs_nonneg (y 0)
  refine ⟨horder, ?_, ?_, ?_⟩ <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  · linarith
  · linarith
  · linarith

#print axioms symmetric
#print axioms trace_one
#print axioms spectrum_exact
#print axioms largest_exact
#print axioms largest_is_attained
#print axioms radius_exact
#print axioms unbounded_largest
#print axioms unbounded_radius
#print axioms no_finite_bound
#print axioms no_maximizer
#print axioms concentrated_loses
#print axioms no_majorization_maximal_list
end FixedTrace
