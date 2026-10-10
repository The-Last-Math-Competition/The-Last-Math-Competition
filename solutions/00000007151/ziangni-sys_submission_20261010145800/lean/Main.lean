import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

noncomputable section
namespace TraceVertex
abbrev Mat := Matrix Unit Unit ℝ

def gram (A : Mat) : Mat := A.transpose * A

theorem gram_entry (A : Mat) : gram A () () = (A () ()) ^ 2 := by
  simp [gram, Matrix.mul_apply, Matrix.transpose_apply, pow_two]

-- The Gram matrix has this eigenvalue on every nonzero vector.
theorem gram_eigenvector (A : Mat) (v : Unit → ℝ) :
    (gram A).mulVec v = ((A () ()) ^ 2) • v := by
  funext i
  cases i
  simp [Matrix.mulVec, dotProduct, gram_entry]

theorem gram_eigenvalue_unique (A : Mat) (v : Unit → ℝ) (hv : v ≠ 0) (l : ℝ)
    (h : (gram A).mulVec v = l • v) : l = (A () ()) ^ 2 := by
  have hn : v () ≠ 0 := by
    intro hz
    apply hv
    funext i
    cases i
    exact hz
  have he := congrFun (h.symm.trans (gram_eigenvector A v)) ()
  simpa using (mul_right_cancel₀ hn he)

def singularValue (A : Mat) : ℝ := Real.sqrt (gram A () ())
def traceNorm (A : Mat) : ℝ := ∑ _i : Unit, singularValue A

theorem traceNorm_formula (A : Mat) : traceNorm A = |A () ()| := by
  simp [traceNorm, singularValue, gram_entry, Real.sqrt_sq_eq_abs]

def body : Set Mat := {A | traceNorm A ≤ 1}
def vertex : Mat := fun _ _ => -1

theorem body_iff (A : Mat) : A ∈ body ↔ -1 ≤ A () () ∧ A () () ≤ 1 := by
  simp [body, traceNorm_formula, abs_le]

theorem vertex_mem : vertex ∈ body := by
  simp [body_iff, vertex]

def expose : Mat →ₗ[ℝ] ℝ where
  toFun A := -A () ()
  map_add' A B := by simp; ring
  map_smul' c A := by simp

-- The unique maximizer of an actual linear functional on the norm unit body.
theorem exposing_face : {A : Mat | A ∈ body ∧ ∀ B ∈ body, expose B ≤ expose A} =
    {vertex} := by
  ext A
  constructor
  · rintro ⟨ha, hmax⟩
    have hbounds := (body_iff A).1 ha
    have h := hmax vertex vertex_mem
    have he : A () () = -1 := by
      change -(-1 : ℝ) ≤ -A () () at h
      linarith
    apply Set.mem_singleton_iff.mpr
    funext i j
    cases i
    cases j
    exact he
  · intro h
    have he := Set.mem_singleton_iff.mp h
    subst A
    refine ⟨vertex_mem, ?_⟩
    intro B hb
    have hh := (body_iff B).1 hb
    change -B () () ≤ -(-1 : ℝ)
    linarith

theorem extreme_vertex : vertex ∈ body.extremePoints ℝ := by
  apply (mem_extremePoints_iff_left).2
  refine ⟨vertex_mem, ?_⟩
  intro A ha B hb hseg
  obtain ⟨a,b,ha0,hb0,hab,he⟩ := hseg
  have hA := (body_iff A).1 ha
  have hB := (body_iff B).1 hb
  have hentry := congrFun (congrFun he ()) ()
  change a * A () () + b * B () () = -1 at hentry
  have hnon : 0 ≤ b * (B () () + 1) := mul_nonneg hb0.le (by linarith)
  have heq : A () () = -1 := by nlinarith
  funext i j
  cases i
  cases j
  exact heq

-- Every standard unsigned partial permutation matrix has 0/1 entries.
def PartialPermutation (A : Mat) : Prop :=
  (∀ i j, A i j = 0 ∨ A i j = 1) ∧
  (∀ i, ∀ j k, A i j = 1 → A i k = 1 → j = k) ∧
  (∀ j, ∀ i k, A i j = 1 → A k j = 1 → i = k)

theorem not_partial : ¬ PartialPermutation vertex := by
  intro h
  have hh := h.1 () ()
  norm_num [vertex] at hh

theorem counterexample : ∃ A : Mat, A ∈ body.extremePoints ℝ ∧ ¬ PartialPermutation A :=
  ⟨vertex, extreme_vertex, not_partial⟩

#print axioms gram_eigenvalue_unique
#print axioms traceNorm_formula
#print axioms exposing_face
#print axioms extreme_vertex
#print axioms counterexample
end TraceVertex
