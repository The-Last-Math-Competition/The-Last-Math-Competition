import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Real.StarOrdered
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace DuplicateConstraintDuality

noncomputable def matrix (y : ℝ) : Matrix (Fin 1) (Fin 1) ℝ :=
  Matrix.diagonal (fun _ => Real.exp y)

theorem positive_definite (y : ℝ) : (matrix y).PosDef := by
  rw [matrix, Matrix.posDef_diagonal_iff]
  intro i
  exact Real.exp_pos y

theorem matrix_entry (y : ℝ) : matrix y 0 0 = Real.exp y := by simp [matrix]

/-- The two actual monomial constraints on the one-dimensional PD cone. -/
noncomputable def constraint (_ : Fin 2) (y : ℝ) : ℝ := (matrix y 0 0)⁻¹
noncomputable def logConstraint (_ : Fin 2) (y : ℝ) : ℝ := -y

theorem logarithmic_bridge (i : Fin 2) (y : ℝ) :
    Real.log (constraint i y) = logConstraint i y := by
  simp [constraint, matrix_entry, logConstraint, Real.log_inv]

theorem objective_bridge (y : ℝ) : Real.log (matrix y 0 0) = y := by
  simp [matrix_entry]

def feasible (y : ℝ) : Prop := ∀ i : Fin 2, constraint i y ≤ 1

theorem feasibility_bridge (y : ℝ) : feasible y ↔ 0 ≤ y := by
  have hc : constraint (0 : Fin 2) y = Real.exp (-y) := by
    simp [constraint, matrix_entry, Real.exp_neg]
  have hi : ∀ i : Fin 2, constraint i y = Real.exp (-y) := fun _ => hc
  simp only [feasible, hi]
  constructor
  · intro h
    have ht : Real.exp (-y) ≤ Real.exp 0 := by simpa using h 0
    have := Real.exp_le_exp.mp ht
    linarith
  · intro h i
    have ht : -y ≤ (0 : ℝ) := by linarith
    simpa using Real.exp_le_exp.mpr ht

/-- The true Lagrangian of min y under the duplicated constraints -y≤0. -/
noncomputable def lagrangian (a b y : ℝ) : ℝ :=
  y + a * logConstraint 0 y + b * logConstraint 1 y

theorem lagrangian_witness (y : ℝ) : lagrangian 1 0 y = 0 := by
  simp [lagrangian, logConstraint]

/-- The actual infimum of this Lagrangian over unrestricted logarithmic coordinates. -/
theorem lagrangian_infimum : IsGLB (Set.range (lagrangian 1 0)) 0 := by
  constructor
  · rintro z ⟨y,rfl⟩
    simp [lagrangian_witness]
  · intro z hz
    exact hz (by exact ⟨0, lagrangian_witness 0⟩)

/-- Any finite true Lagrangian infimum is at most zero, by evaluating at y=0. -/
theorem dual_upper_bound (a b d : ℝ) (h : IsGLB (Set.range (lagrangian a b)) d) : d ≤ 0 := by
  apply h.1
  exact ⟨0, by simp [lagrangian, logConstraint]⟩

noncomputable def primalValues : Set ℝ :=
  {v | ∃ y : ℝ, feasible y ∧ v = matrix y 0 0}

/-- Original-scale geometric dual values are exponentials of true log-dual infima. -/
noncomputable def dualValues : Set ℝ :=
  {v | ∃ a b d : ℝ, 0 ≤ a ∧ 0 ≤ b ∧
    IsGLB (Set.range (lagrangian a b)) d ∧ v = Real.exp d}

theorem primal_optimum : IsGLB primalValues 1 := by
  constructor
  · rintro v ⟨y,hy,rfl⟩
    rw [matrix_entry]
    have h := Real.exp_le_exp.mpr ((feasibility_bridge y).mp hy)
    simpa using h
  · intro z hz
    apply hz
    exact ⟨0, (feasibility_bridge 0).mpr (by norm_num), by simp [matrix_entry]⟩

theorem dual_optimum : IsLUB dualValues 1 := by
  constructor
  · rintro v ⟨a,b,d,ha,hb,hd,rfl⟩
    have h := Real.exp_le_exp.mpr (dual_upper_bound a b d hd)
    simpa using h
  · intro z hz
    apply hz
    exact ⟨1,0,0,by norm_num,by norm_num,lagrangian_infimum,by simp⟩

theorem duplicated_logs_dependent : ¬ LinearIndependent ℝ logConstraint := by
  intro h
  have hi : (0 : Fin 2) = 1 := h.injective (by rfl)
  norm_num at hi

/-- Zero original-scale duality gap with dependent logarithmic constraints. -/
theorem counterexample : IsGLB primalValues 1 ∧ IsLUB dualValues 1 ∧
    (1 : ℝ) - 1 = 0 ∧ ¬ LinearIndependent ℝ logConstraint := by
  exact ⟨primal_optimum, dual_optimum, by norm_num, duplicated_logs_dependent⟩

#print axioms positive_definite
#print axioms logarithmic_bridge
#print axioms feasibility_bridge
#print axioms lagrangian_infimum
#print axioms primal_optimum
#print axioms dual_optimum
#print axioms counterexample
end DuplicateConstraintDuality
