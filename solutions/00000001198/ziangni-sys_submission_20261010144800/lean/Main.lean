import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Tactic

noncomputable section
namespace ZonalUnit
open MvPolynomial

-- The zero partition has no boxes: its normalized monomial is 1.
-- This is the actual degree-zero Jack/Zonal polynomial, in any number of variables.
def emptyZonal (σ : Type*) : MvPolynomial σ ℚ := monomial 0 1

theorem emptyZonal_eq_one (σ : Type*) : emptyZonal σ = 1 := by
  simp [emptyZonal]

theorem symmetric_empty (σ : Type*) (e : Equiv.Perm σ) :
    rename e (emptyZonal σ) = emptyZonal σ := by
  simp [emptyZonal_eq_one]

-- Degree-zero symmetric polynomials have precisely the single constant basis vector.
def DegreeZero {σ : Type*} (p : MvPolynomial σ ℚ) : Prop :=
  ∀ d, d ≠ 0 → coeff d p = 0

theorem constant_basis_spans {σ : Type*} (p : MvPolynomial σ ℚ)
    (h : DegreeZero p) : p = C (coeff 0 p) := by
  classical
  ext d
  by_cases hd : d = 0
  · subst d; simp
  · simp [coeff_C, hd, Ne.symm hd, h d hd]

theorem empty_degree_zero (σ : Type*) : DegreeZero (emptyZonal σ) := by
  classical
  intro d hd
  simp [emptyZonal_eq_one, coeff_one, hd, Ne.symm hd]

theorem product_empty (σ : Type*) :
    emptyZonal σ * emptyZonal σ = C 1 * emptyZonal σ := by
  simp [emptyZonal_eq_one]

-- Extracting the constant coefficient proves uniqueness of this LR coefficient.
theorem unique_LR_coefficient (σ : Type*) (c : ℚ)
    (h : emptyZonal σ * emptyZonal σ = C c * emptyZonal σ) : c = 1 := by
  have hc := congrArg (coeff (0 : σ →₀ ℕ)) h
  simpa [emptyZonal_eq_one] using hc.symm

def alternatingEven : List ℤ → ℤ
  | [] => 0
  | a :: rest => 2 * a - alternatingEven rest

theorem alternating_even (l : List ℤ) : ∃ k : ℤ, alternatingEven l = 2 * k := by
  induction l with
  | nil => exact ⟨0, by simp [alternatingEven]⟩
  | cons a rest ih =>
    obtain ⟨k, hk⟩ := ih
    exact ⟨a-k, by simp [alternatingEven, hk]; ring⟩

theorem one_not_alternating_even (l : List ℤ) : alternatingEven l ≠ 1 := by
  obtain ⟨k, hk⟩ := alternating_even l
  omega

theorem counterexample (σ : Type*) :
    (emptyZonal σ * emptyZonal σ = C 1 * emptyZonal σ) ∧
    (∀ c : ℚ, emptyZonal σ * emptyZonal σ = C c * emptyZonal σ → c = 1) ∧
    (∀ l : List ℤ, alternatingEven l ≠ 1) :=
  ⟨product_empty σ, unique_LR_coefficient σ, one_not_alternating_even⟩

#print axioms constant_basis_spans
#print axioms symmetric_empty
#print axioms unique_LR_coefficient
#print axioms counterexample
end ZonalUnit
