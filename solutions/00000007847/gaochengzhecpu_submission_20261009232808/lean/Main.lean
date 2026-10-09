import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators

namespace Conjecture7847

abbrev Vector := Fin 1 → ℝ

/-- One decision variable, two distinct upper-bound constraints. -/
def A : Fin 2 → Fin 1 → ℝ := fun _ _ => 1
def rhs : Fin 2 → ℝ := ![1, 2]
def objective (x : Vector) : ℝ := ∑ j, x j

def LPFeasible (x : Vector) : Prop :=
  (∀ j, 0 ≤ x j ∧ x j ≤ 1) ∧
    ∀ i, (∑ j, A i j * x j) ≤ rhs i

def IPFeasible (x : Vector) : Prop :=
  LPFeasible x ∧ ∀ j, x j = 0 ∨ x j = 1

def IsLPMax (x : Vector) : Prop :=
  LPFeasible x ∧ ∀ y, LPFeasible y → objective y ≤ objective x

def optimum : Vector := fun _ => 1

theorem objective_eq (x : Vector) : objective x = x 0 := by
  simp [objective, Fin.sum_univ_one]

theorem optimum_lp_feasible : LPFeasible optimum := by
  constructor
  · intro j; norm_num [optimum]
  · intro i; fin_cases i <;> norm_num [A, rhs, optimum, Fin.sum_univ_one]

theorem optimum_ip_feasible : IPFeasible optimum :=
  ⟨optimum_lp_feasible, fun _ => Or.inr rfl⟩

theorem objective_upper (x : Vector) (hx : LPFeasible x) : objective x ≤ 1 := by
  rw [objective_eq]
  exact (hx.1 0).2

theorem optimum_objective : objective optimum = 1 := by
  simp [objective_eq, optimum]

theorem optimum_lp_max : IsLPMax optimum := by
  refine ⟨optimum_lp_feasible, ?_⟩
  intro x hx
  rw [optimum_objective]
  exact objective_upper x hx

theorem unique_lp_optimum (x : Vector) (hx : IsLPMax x) : x = optimum := by
  have hu := objective_upper x hx.1
  have hl := hx.2 optimum optimum_lp_feasible
  rw [optimum_objective, objective_eq] at hl
  rw [objective_eq] at hu
  have h : x 0 = 1 := le_antisymm hu hl
  funext j
  fin_cases j
  exact h

theorem optimum_ip_max (x : Vector) (hx : IPFeasible x) :
    objective x ≤ objective optimum := by
  rw [optimum_objective]
  exact objective_upper x hx.1

/-- Standard independent Bernoulli rounding; there is just one coordinate. -/
def rounded (b : Bool) : Vector := fun _ => cond b 1 0

def roundingLaw : PMF Bool := PMF.bernoulli 1 (by norm_num)

theorem rounding_masses : roundingLaw true = 1 ∧ roundingLaw false = 0 := by
  simp [roundingLaw, PMF.bernoulli_apply]

theorem rounding_feasible (b : Bool) : IPFeasible (rounded b) := by
  cases b
  · constructor
    · constructor
      · intro j; norm_num [rounded]
      · intro i; fin_cases i <;> norm_num [A, rhs, rounded, Fin.sum_univ_one]
    · intro j; exact Or.inl rfl
  · exact optimum_ip_feasible

theorem rounding_has_lp_marginal (j : Fin 1) :
    (∫ b, rounded b j ∂roundingLaw.toMeasure) = optimum j := by
  simpa [rounded, roundingLaw, optimum] using
    (PMF.bernoulli_expectation (p := 1) (by norm_num))

/-- Profit divided by the exact integer optimum, not a separately assigned ratio. -/
def approximationRatio (b : Bool) : ℝ :=
  objective (rounded b) / objective optimum

theorem expected_approximation_ratio :
    (∫ b, approximationRatio b ∂roundingLaw.toMeasure) = 1 := by
  have h : approximationRatio = (fun b : Bool => cond b (1 : ℝ) 0) := by
    funext b
    simp [approximationRatio, objective_eq, rounded, optimum]
  rw [h]
  simpa [roundingLaw] using (PMF.bernoulli_expectation (p := 1) (by norm_num))

def claimedRatio (m : ℕ) : ℝ := 1 - (1 - 1 / (m : ℝ)) ^ m

theorem claimed_two_constraints : claimedRatio 2 = 3 / 4 := by
  norm_num [claimedRatio]

theorem exact_expectation_claim_false :
    (∫ b, approximationRatio b ∂roundingLaw.toMeasure) ≠ claimedRatio 2 := by
  rw [expected_approximation_ratio, claimed_two_constraints]
  norm_num

#print axioms optimum_lp_max
#print axioms unique_lp_optimum
#print axioms optimum_ip_max
#print axioms rounding_feasible
#print axioms rounding_has_lp_marginal
#print axioms expected_approximation_ratio
#print axioms exact_expectation_claim_false

end Conjecture7847
