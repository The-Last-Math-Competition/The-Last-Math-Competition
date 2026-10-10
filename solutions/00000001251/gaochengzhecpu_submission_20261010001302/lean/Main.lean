import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option maxRecDepth 2000
set_option maxHeartbeats 2000000

open scoped BigOperators

namespace Conjecture1251

abbrev State := Fin 3 × Fin 3 × Fin 3

def occupation (x : State) (i : Fin 3) : ℕ :=
  if i = 0 then x.1.val else if i = 1 then x.2.1.val else x.2.2.val

/-- A legal one-particle jump from site i to a different site j. -/
def Moves (x y : State) (i j : Fin 3) : Prop :=
  i ≠ j ∧ 0 < occupation x i ∧ occupation x j < 2 ∧
    ∀ v : Fin 3, occupation y v =
      if v = i then occupation x v - 1
      else if v = j then occupation x v + 1
      else occupation x v

instance (x y : State) (i j : Fin 3) : Decidable (Moves x y i j) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- On the three-cycle every distinct pair is neighboring. The standard
partial-exclusion jump rate is eta_i * (2 - eta_j). -/
def rate (x y : State) : ℕ :=
  ∑ i : Fin 3, ∑ j : Fin 3,
    if Moves x y i j then (occupation x i * (2 - occupation x j) : ℕ) else 0

def exitRate (x : State) : ℕ := ∑ y : State, rate x y

def generator (x y : State) : ℚ :=
  if x = y then -(exitRate x : ℚ) else rate x y

def singleMass (a : Fin 3) : ℚ := if a = 1 then 1 / 2 else 1 / 4

def multiplicity (a : Fin 3) : ℕ := if a = 1 then 2 else 1

def weight (x : State) : ℕ := multiplicity x.1 * multiplicity x.2.1 * multiplicity x.2.2

/-- Three independent Binomial(2,1/2) occupation variables. -/
def mass (x : State) : ℚ := weight x / 64

theorem capacity_two (x : State) (i : Fin 3) : occupation x i ≤ 2 := by
  rcases x with ⟨a, b, c⟩
  fin_cases i <;> simp [occupation] <;> omega

theorem rate_self_zero : ∀ x : State, rate x x = 0 := by decide

theorem weight_positive : ∀ x : State, 0 < weight x := by decide

theorem mass_positive (x : State) : 0 < mass x := by
  unfold mass
  exact div_pos (by exact_mod_cast weight_positive x) (by norm_num)

theorem weight_sum : ∑ x : State, weight x = 64 := by decide

theorem mass_sum : ∑ x : State, mass x = 1 := by
  simp only [mass, ← Finset.sum_div, ← Nat.cast_sum, weight_sum]
  norm_num

theorem weighted_balance :
    ∀ x y : State, weight x * rate x y = weight y * rate y x := by decide

theorem detailed_balance :
    ∀ x y : State, mass x * rate x y = mass y * rate y x := by
  intro x y
  simp only [mass, div_mul_eq_mul_div, ← Nat.cast_mul, weighted_balance x y]

theorem generator_row_sum (x : State) : ∑ y : State, generator x y = 0 := by
  classical
  have h : generator x = fun y => (rate x y : ℚ) - if x = y then (exitRate x : ℚ) else 0 := by
    funext y
    by_cases hxy : x = y
    · subst y
      simp [generator, rate_self_zero]
    · simp [generator, hxy]
  rw [h, Finset.sum_sub_distrib]
  simp [exitRate, Nat.cast_sum]

theorem generator_nonnegative_off_diagonal (x y : State) (h : x ≠ y) :
    0 ≤ generator x y := by
  simp only [generator, if_neg h]
  exact Nat.cast_nonneg _

theorem generator_detailed_balance (x y : State) :
    mass x * generator x y = mass y * generator y x := by
  by_cases h : x = y
  · subst y
    rfl
  · simp only [generator, if_neg h, if_neg (Ne.symm h)]
    exact detailed_balance x y

/-- The actual finite continuous-time stationarity equation pi Q = 0. -/
theorem stationary (y : State) : ∑ x : State, mass x * generator x y = 0 := by
  simp_rw [generator_detailed_balance]
  rw [← Finset.mul_sum, generator_row_sum, mul_zero]

def mean (i : Fin 3) : ℚ := ∑ x : State, mass x * occupation x i

def threePoint : ℚ :=
  ∑ x : State, mass x * occupation x 0 * occupation x 1 * occupation x 2

theorem weighted_means : ∀ i : Fin 3, ∑ x : State, weight x * occupation x i = 64 := by decide

theorem means_one (i : Fin 3) : mean i = 1 := by
  simp only [mean, mass, div_mul_eq_mul_div, ← Nat.cast_mul, ← Finset.sum_div,
    ← Nat.cast_sum, weighted_means]
  norm_num

theorem weighted_three_point :
    ∑ x : State, weight x * occupation x 0 * occupation x 1 * occupation x 2 = 64 := by decide

theorem three_point_one : threePoint = 1 := by
  simp only [threePoint, mass, div_mul_eq_mul_div, ← Nat.cast_mul, ← Finset.sum_div,
    ← Nat.cast_sum, weighted_three_point]
  norm_num

theorem three_point_deficit_zero : threePoint - mean 0 * mean 1 * mean 2 = 0 := by
  rw [three_point_one, means_one, means_one, means_one]
  norm_num

theorem weighted_marginals : ∀ i a : Fin 3,
    (∑ x : State, if occupation x i = a.val then weight x else 0) = 16 * multiplicity a :=
  by decide

theorem occupation_marginals (i : Fin 3) (a : Fin 3) :
    (∑ x : State, if occupation x i = a.val then mass x else 0) = singleMass a := by
  have hterm (x : State) : (if occupation x i = a.val then mass x else 0) =
      ((if occupation x i = a.val then weight x else 0 : ℕ) : ℚ) / 64 := by
    split_ifs <;> simp [mass]
  simp_rw [hterm]
  rw [← Finset.sum_div, ← Nat.cast_sum, weighted_marginals]
  fin_cases a <;> norm_num [multiplicity, singleMass]

theorem product_formula (x : State) :
    mass x = singleMass x.1 * singleMass x.2.1 * singleMass x.2.2 := by
  rcases x with ⟨a, b, c⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    norm_num [mass, weight, multiplicity, singleMass]

theorem nontrivial_jump :
    rate (1, 0, 0) (0, 1, 0) = 2 ∧ mass (1, 0, 0) > 0 :=
  ⟨by decide, mass_positive _⟩

theorem real_mass_sum : ∑ x : State, (mass x : ℝ) = 1 := by
  exact_mod_cast mass_sum

/-- The finite weights define a genuine Mathlib probability mass function. -/
noncomputable def probabilityMass : PMF State :=
  PMF.ofFintype (fun x => ENNReal.ofReal (mass x)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (by
      intro x _
      exact_mod_cast (mass_positive x).le), real_mass_sum]
    simp)

theorem probabilityMass_full_support (x : State) : 0 < probabilityMass x := by
  apply ENNReal.ofReal_pos.mpr
  exact_mod_cast mass_positive x

theorem probabilityMass_product (x : State) :
    probabilityMass x = ENNReal.ofReal ((singleMass x.1 : ℝ) *
      (singleMass x.2.1 : ℝ) * (singleMass x.2.2 : ℝ)) := by
  change ENNReal.ofReal (mass x) = _
  rw [product_formula]
  push_cast
  rfl

theorem probabilityMass_toReal (x : State) : (probabilityMass x).toReal = (mass x : ℝ) := by
  apply ENNReal.toReal_ofReal
  exact_mod_cast (mass_positive x).le

theorem probabilityMass_stationary (y : State) :
    ∑ x : State, (probabilityMass x).toReal * (generator x y : ℝ) = 0 := by
  simp only [probabilityMass_toReal]
  exact_mod_cast stationary y

/-- The other common k-exclusion convention: each legal directed jump
has unit rate, regardless of its source and target occupations. -/
def unitRate (x y : State) : ℕ :=
  ∑ i : Fin 3, ∑ j : Fin 3, if Moves x y i j then 1 else 0

def unitExitRate (x : State) : ℕ := ∑ y : State, unitRate x y

def unitGenerator (x y : State) : ℚ :=
  if x = y then -(unitExitRate x : ℚ) else unitRate x y

def uniformMass (_ : State) : ℚ := 1 / 27

theorem unit_rate_symmetric : ∀ x y : State, unitRate x y = unitRate y x := by decide

theorem unit_rate_self_zero : ∀ x : State, unitRate x x = 0 := by decide

theorem unit_generator_symmetric (x y : State) : unitGenerator x y = unitGenerator y x := by
  by_cases h : x = y
  · subst y; rfl
  · simp only [unitGenerator, if_neg h, if_neg (Ne.symm h), unit_rate_symmetric x y]

theorem unit_generator_row_sum (x : State) : ∑ y : State, unitGenerator x y = 0 := by
  classical
  have h : unitGenerator x = fun y => (unitRate x y : ℚ) -
      if x = y then (unitExitRate x : ℚ) else 0 := by
    funext y
    by_cases hxy : x = y
    · subst y; simp [unitGenerator, unit_rate_self_zero]
    · simp [unitGenerator, hxy]
  rw [h, Finset.sum_sub_distrib]
  simp [unitExitRate, Nat.cast_sum]

theorem unit_generator_nonnegative_off_diagonal (x y : State) (h : x ≠ y) :
    0 ≤ unitGenerator x y := by
  simp only [unitGenerator, if_neg h]
  exact Nat.cast_nonneg _

theorem uniform_mass_positive (x : State) : 0 < uniformMass x := by
  norm_num [uniformMass]

theorem uniform_mass_sum : ∑ x : State, uniformMass x = 1 := by
  norm_num [uniformMass, Fintype.card_prod]

theorem uniform_mass_product (x : State) :
    uniformMass x = (1 / 3 : ℚ) * (1 / 3) * (1 / 3) := by
  norm_num [uniformMass]

theorem uniform_stationary (y : State) :
    ∑ x : State, uniformMass x * unitGenerator x y = 0 := by
  simp_rw [uniformMass, unit_generator_symmetric]
  rw [← Finset.mul_sum, unit_generator_row_sum, mul_zero]

noncomputable def uniformProbabilityMass : PMF State :=
  PMF.ofFintype (fun x => ENNReal.ofReal (uniformMass x)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (by
      intro x _
      exact_mod_cast (uniform_mass_positive x).le)]
    have h : ∑ x : State, (uniformMass x : ℝ) = 1 := by exact_mod_cast uniform_mass_sum
    rw [h]
    simp)

theorem uniformProbabilityMass_toReal (x : State) :
    (uniformProbabilityMass x).toReal = (uniformMass x : ℝ) := by
  apply ENNReal.toReal_ofReal
  exact_mod_cast (uniform_mass_positive x).le

theorem uniformProbabilityMass_full_support (x : State) : 0 < uniformProbabilityMass x := by
  apply ENNReal.ofReal_pos.mpr
  exact_mod_cast uniform_mass_positive x

theorem uniformProbabilityMass_stationary (y : State) :
    ∑ x : State, (uniformProbabilityMass x).toReal * (unitGenerator x y : ℝ) = 0 := by
  simp only [uniformProbabilityMass_toReal]
  exact_mod_cast uniform_stationary y

theorem counterexample :
    (2 : ℕ) ≠ 1 ∧
    (∀ x : State, 0 < mass x) ∧
    (∑ x : State, mass x = 1) ∧
    (∀ y : State, ∑ x : State, mass x * generator x y = 0) ∧
    (∀ x : State, mass x = singleMass x.1 * singleMass x.2.1 * singleMass x.2.2) ∧
    threePoint - mean 0 * mean 1 * mean 2 = 0 := by
  exact ⟨by decide, mass_positive, mass_sum, stationary, product_formula,
    three_point_deficit_zero⟩

#print axioms stationary
#print axioms probabilityMass_stationary
#print axioms uniformProbabilityMass_stationary
#print axioms counterexample

end Conjecture1251
