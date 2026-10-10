import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Tactic

namespace MatchingStatistics
open MvPolynomial
open scoped ENNReal

/-- A perfect matching is its fixed-point-free involution on the labeled vertices. -/
def Matching (n : ℕ) :=
  {m : Equiv.Perm (Bool × Fin n) // (∀ v, m (m v) = v) ∧ (∀ v, m v ≠ v)}

noncomputable instance (n : ℕ) : Fintype (Matching n) := by
  classical
  unfold Matching
  infer_instance

def toggle (n : ℕ) : Equiv.Perm (Bool × Fin n) where
  toFun v := (!v.1, v.2)
  invFun v := (!v.1, v.2)
  left_inv v := by rcases v with ⟨b,i⟩; cases b <;> rfl
  right_inv v := by rcases v with ⟨b,i⟩; cases b <;> rfl

instance (n : ℕ) : Nonempty (Matching n) := ⟨⟨toggle n, by
  constructor
  · rintro ⟨b,i⟩; cases b <;> rfl
  · rintro ⟨b,i⟩ h
    have := congrArg Prod.fst h
    cases b <;> simp [toggle] at this⟩⟩

/-- Relabeling a matching by a vertex permutation. -/
def relabel {n : ℕ} (r : Equiv.Perm (Bool × Fin n)) (m : Matching n) : Matching n :=
  ⟨r * m.val * r.symm, by
    constructor
    · intro v
      simpa only [Equiv.Perm.mul_apply, Equiv.apply_symm_apply, Equiv.symm_apply_apply]
        using congrArg r (m.property.1 (r.symm v))
    · intro v h
      apply m.property.2 (r.symm v)
      have := congrArg r.symm h
      simpa only [Equiv.Perm.mul_apply, Equiv.apply_symm_apply, Equiv.symm_apply_apply] using this⟩

/-- Setting the final variable equal to zero: the usual stability restriction. -/
noncomputable def restrict (k : ℕ) : MvPolynomial (Fin (k+1)) ℝ →+* MvPolynomial (Fin k) ℝ :=
  eval₂Hom C (fun i => if h : i.val < k then X ⟨i.val,h⟩ else 0)

/-- A concrete model for symmetric functions: compatible symmetric polynomials. -/
structure SymFunction where
  component : (k : ℕ) → MvPolynomial (Fin k) ℝ
  symmetric : ∀ k, (component k).IsSymmetric
  stable : ∀ k, restrict k (component (k+1)) = component k

noncomputable def constant (c : ℝ) : SymFunction where
  component _ := C c
  symmetric _ := IsSymmetric.C c
  stable k := by simp [restrict]

/-- Actual degree-zero symmetric-function statistics, not just numerical statistics. -/
noncomputable def statistic (c : ℝ) {n : ℕ} (_ : Matching n) : SymFunction := constant c

theorem degree_zero (c : ℝ) {n : ℕ} (m : Matching n) (k : ℕ) :
    ((statistic c m).component k).totalDegree = 0 := totalDegree_C c

/-- Symmetric components are invariant under the actual variable-permutation action. -/
theorem equivariant (c : ℝ) {n : ℕ} (r : Equiv.Perm (Bool × Fin n))
    (m : Matching n) (k : ℕ) (q : Equiv.Perm (Fin k)) :
    (statistic c (relabel r m)).component k = rename q ((statistic c m).component k) := by
  simp [statistic, constant]

/-- One common coefficient observable: constant coefficient, evaluated by setting variables to0. -/
noncomputable def coordinate (s : SymFunction) : ℝ := eval (fun _ => 0) (s.component 1)

theorem coordinate_constant (c : ℝ) : coordinate (constant c) = c := by
  simp [coordinate, constant]

noncomputable def uniform (n : ℕ) : PMF (Matching n) := PMF.uniformOfFintype _
noncomputable def law (n : ℕ) (c : ℝ) : PMF ℝ :=
  (uniform n).map (fun m => coordinate (statistic c m))

theorem law_constant (n : ℕ) (c : ℝ) : law n c = PMF.pure c := by
  unfold law
  simp only [statistic, coordinate_constant]
  exact PMF.map_const _ _

/-- The pushforward laws remain separated by a full unit of probability for every size. -/
theorem probability_gap (n : ℕ) : (law n 0) 0 = 1 ∧ (law n 1) 0 = 0 := by
  simp [law_constant]

/-- A common bounded continuous coordinate test separates the constant laws. -/
noncomputable def test (x : ℝ) : ℝ := min 1 (max 0 x)

theorem test_continuous : Continuous test := by
  unfold test
  fun_prop

theorem test_bounded (x : ℝ) : 0 ≤ test x ∧ test x ≤ 1 := by
  unfold test
  constructor
  · exact le_min (by norm_num) (le_max_left _ _)
  · exact min_le_left _ _

theorem test_gap : test 1 - test 0 = 1 := by norm_num [test]

theorem bounded_test_laws (n : ℕ) :
    (law n 0).map test = PMF.pure 0 ∧ (law n 1).map test = PMF.pure 1 := by
  simp [law_constant, PMF.pure_map, test]

/-- Even the exact coordinate laws cannot become indistinguishable in the limit. -/
theorem not_asymptotically_same :
    ¬ Filter.Tendsto (fun n : ℕ => (law n 0) 0 - (law n 1) 0) Filter.atTop (nhds 0) := by
  have h : (fun n : ℕ => (law n 0) 0 - (law n 1) 0) = fun _ => (1 : ℝ≥0∞) := by
    funext n
    rw [(probability_gap n).1, (probability_gap n).2]
    simp
  rw [h]
  intro hlim
  have hEq := tendsto_nhds_unique hlim tendsto_const_nhds
  norm_num at hEq

#print axioms equivariant
#print axioms degree_zero
#print axioms law_constant
#print axioms probability_gap
#print axioms test_continuous
#print axioms not_asymptotically_same
end MatchingStatistics
