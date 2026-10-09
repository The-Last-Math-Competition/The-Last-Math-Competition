import Solution

open MeasureTheory Conjecture934
open scoped ENNReal

-- These checks use the frozen result as-is. They neither redefine nor repair it.
example : μ Set.univ = 1 := measure_univ
example : MeasureTheory.Measure.IsAddHaarMeasure μ := inferInstance
example (f : L2) : (inclusion f).1 = f.1 := by
  rw [inclusion_apply, inclusionLinear_apply]
example (f : L2) : ‖inclusion f‖ ≤ ‖f‖ := by
  rw [inclusion_apply]
  exact inclusion_norm_le f
example : ∃ f : ℕ → Lp ℂ 1 (AddCircle.haarAddCircle (T := (1 : ℝ))),
    Summable f ∧
    (∀ ε : ℕ → ℂ, (∀ n, ε n = 1 ∨ ε n = -1) →
      Summable (fun n => ε n • f n)) ∧
    (∀ π : Equiv.Perm ℕ, ¬ Summable (fun n => ‖f (π n)‖)) :=
  conjecture
