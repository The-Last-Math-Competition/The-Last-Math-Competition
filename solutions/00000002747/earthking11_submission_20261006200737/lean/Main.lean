import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Tactic.FinCases

/-!
Disproof of the capacity formula in TLMC conjecture 00000002747, at m = n = 1.

We use the standard interpretation over Q: M_1(M_1(Q)) is the space of
1-by-1 matrices. The determinant is its sole entry. Consequently every
linear subspace on which the determinant vanishes is the zero subspace,
so the maximum possible dimension is 0, while the stated formula gives 1.
-/
namespace TLMC2747

abbrev K := ℚ
abbrev M1 := Matrix (Fin 1) (Fin 1) K

/-- A linear matrix space on which determinant vanishes identically. -/
def IsDetZeroSpace (W : Submodule K M1) : Prop :=
  ∀ A ∈ W, Matrix.det A = 0

/-- The displayed determinant formula specialized to m = n = 1. -/
def ClaimedCapacity : ℕ := (1 - 1) * 1 ^ 2 + 1

/-- `n` is the maximal capacity when it bounds every admissible subspace
and is attained by an admissible subspace. -/
def IsMaximumCapacity (n : ℕ) : Prop :=
  (∀ W : Submodule K M1, IsDetZeroSpace W → Module.finrank K W ≤ n) ∧
  ∃ W : Submodule K M1, IsDetZeroSpace W ∧ Module.finrank K W = n

theorem det_fin_one_eq_entry (A : M1) : Matrix.det A = A 0 0 := by
  simp

theorem det_zero_space_eq_bot (W : Submodule K M1) (hW : IsDetZeroSpace W) :
    W = ⊥ := by
  apply Submodule.ext
  intro A
  constructor
  · intro hA
    have hdet : Matrix.det A = 0 := hW A hA
    have hA0 : A 0 0 = 0 := by simpa [det_fin_one_eq_entry] using hdet
    have hAeq : A = 0 := by
      ext i j
      fin_cases i
      fin_cases j
      simpa using hA0
    simp [hAeq]
  · intro hA
    rw [hA]
    exact W.zero_mem

theorem det_zero_space_finrank_zero (W : Submodule K M1)
    (hW : IsDetZeroSpace W) : Module.finrank K W = 0 := by
  rw [det_zero_space_eq_bot W hW]
  rw [finrank_bot]

theorem zero_space_is_det_zero : IsDetZeroSpace (⊥ : Submodule K M1) := by
  intro A hA
  have hA0 : A = 0 := by simpa using hA
  rw [hA0]
  simp

theorem actual_capacity_is_zero : IsMaximumCapacity 0 := by
  constructor
  · intro W hW
    rw [det_zero_space_finrank_zero W hW]
  · refine ⟨⊥, zero_space_is_det_zero, ?_⟩
    rw [finrank_bot]

theorem claimed_capacity_is_one : ClaimedCapacity = 1 := by
  rfl

/-- The actual maximum is 0, contradicting the formula's asserted value 1. -/
theorem capacity_formula_false :
    ¬ ∃ n : ℕ, IsMaximumCapacity n ∧ n = ClaimedCapacity := by
  rintro ⟨n, hmax, hformula⟩
  have hzero : n = 0 := by
    rcases hmax.2 with ⟨W, hW, hdim⟩
    rw [det_zero_space_finrank_zero W hW] at hdim
    exact hdim.symm
  rw [hzero, claimed_capacity_is_one] at hformula
  exact Nat.zero_ne_one hformula

end TLMC2747

#print axioms TLMC2747.actual_capacity_is_zero
#print axioms TLMC2747.capacity_formula_false
