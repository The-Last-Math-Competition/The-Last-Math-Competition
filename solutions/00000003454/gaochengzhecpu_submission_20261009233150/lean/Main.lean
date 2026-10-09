import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

noncomputable section
open Filter
open scoped Topology unitInterval

namespace Conjecture3454

def midpoint : I := ⟨1 / 2, by constructor <;> norm_num⟩

def quadratic (x : ℝ) : ℝ := (x - 1 / 2) ^ 2

def quadraticOnUnit : C(I, ℝ) :=
  ⟨fun x => quadratic x, by unfold quadratic; continuity⟩

theorem quadratic_smooth : ContDiff ℝ ⊤ quadratic :=
  (contDiff_id.sub contDiff_const).pow 2

theorem quadratic_first_derivative :
    deriv quadratic = fun x : ℝ => 2 * (x - 1 / 2) := by
  funext x
  have h := ((hasDerivAt_id x).sub_const (1 / 2)).pow 2
  convert h.deriv using 1
  simp [quadratic]

theorem quadratic_second_derivative (x : ℝ) :
    deriv (deriv quadratic) x = 2 := by
  rw [quadratic_first_derivative]
  have h := ((hasDerivAt_id x).sub_const (1 / 2)).const_mul 2
  simpa only [mul_one] using h.deriv

theorem approximation_at_midpoint (n : ℕ) (hn : 0 < n) :
    bernsteinApproximation n quadraticOnUnit midpoint = (1 / 4 : ℝ) / n := by
  have h := bernstein.variance (n := n) (by exact_mod_cast hn) midpoint
  rw [bernsteinApproximation.apply]
  calc
    (∑ k : Fin (n + 1), quadraticOnUnit (bernstein.z k) * bernstein n k midpoint) =
        ∑ k : Fin (n + 1), ((midpoint : ℝ) - bernstein.z k) ^ 2 *
          bernstein n k midpoint := by
      apply Finset.sum_congr rfl
      intro k _
      dsimp [quadraticOnUnit, quadratic, midpoint]
      rw [sub_sq_comm]
    _ = (1 / 4 : ℝ) / n := by
      convert h using 1
      norm_num [midpoint]

def deviation (n : ℕ) : ℝ :=
  bernsteinApproximation (n + 1) quadraticOnUnit midpoint - quadratic midpoint

theorem deviation_exact (n : ℕ) : deviation n = (1 / 4 : ℝ) / (n + 1) := by
  rw [deviation, approximation_at_midpoint (n + 1) (Nat.succ_pos n)]
  simp [quadratic, midpoint]

theorem scaled_deviation_exact (n : ℕ) : (n + 1 : ℝ) * deviation n = 1 / 4 := by
  rw [deviation_exact]
  have hn : (n + 1 : ℝ) ≠ 0 := by positivity
  field_simp
  ring

theorem scaled_deviation_limit :
    Tendsto (fun n : ℕ => (n + 1 : ℝ) * deviation n) atTop (𝓝 (1 / 4 : ℝ)) := by
  simpa only [scaled_deviation_exact] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 / 4 : ℝ)) atTop (𝓝 (1 / 4 : ℝ)))

theorem deviation_limit : Tendsto deviation atTop (𝓝 (0 : ℝ)) := by
  have h := (tendsto_const_div_atTop_nhds_zero_nat (1 / 4 : ℝ)).comp
    (tendsto_add_atTop_nat 1)
  have hd : deviation = fun n : ℕ => (1 / 4 : ℝ) / (n + 1) :=
    funext deviation_exact
  rw [hd]
  simpa [Function.comp_def, Nat.cast_add, Nat.cast_one] using h

theorem scaled_second_derivative_limit_false :
    ¬ Tendsto (fun n : ℕ => (n + 1 : ℝ) * deviation n) atTop
      (𝓝 (deriv (deriv quadratic) (midpoint : ℝ))) := by
  intro h
  have heq := tendsto_nhds_unique scaled_deviation_limit h
  rw [quadratic_second_derivative] at heq
  norm_num at heq

theorem raw_second_derivative_limit_false :
    ¬ Tendsto deviation atTop (𝓝 (deriv (deriv quadratic) (midpoint : ℝ))) := by
  intro h
  have heq := tendsto_nhds_unique deviation_limit h
  rw [quadratic_second_derivative] at heq
  norm_num at heq

end Conjecture3454

#print axioms Conjecture3454.quadratic_smooth
#print axioms Conjecture3454.approximation_at_midpoint
#print axioms Conjecture3454.scaled_second_derivative_limit_false
#print axioms Conjecture3454.raw_second_derivative_limit_false
