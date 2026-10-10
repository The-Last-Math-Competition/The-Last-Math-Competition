import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.RingTheory.Nilpotent.Lemmas
import Mathlib.Tactic

namespace DeterminantKernel
open Matrix

def U : Matrix (Fin 2) (Fin 2) ℚ := !![1, 1; 0, 1]

theorem det_U : U.det = 1 := by norm_num [U, Matrix.det_fin_two]

def stabilized (n : ℕ) : Matrix (Fin 2 ⊕ Fin n) (Fin 2 ⊕ Fin n) ℚ :=
  Matrix.fromBlocks U 0 0 1

theorem det_stabilized (n : ℕ) : (stabilized n).det = 1 := by
  rw [stabilized, Matrix.det_fromBlocks_zero₂₁, det_U, Matrix.det_one, mul_one]

def witness (n : ℕ) : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin n) ℚ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (stabilized n) (by rw [det_stabilized]; norm_num)

theorem witness_det (n : ℕ) : Matrix.GeneralLinearGroup.det (witness n) = 1 := by
  apply Units.ext
  change (stabilized n).det = 1
  exact det_stabilized n

theorem witness_nonidentity (n : ℕ) : witness n ≠ 1 := by
  intro h
  have e := congrArg (fun g : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin n) ℚ =>
    (g : Matrix (Fin 2 ⊕ Fin n) (Fin 2 ⊕ Fin n) ℚ) (Sum.inl 0) (Sum.inl 1)) h
  norm_num [witness, Matrix.GeneralLinearGroup.mkOfDetNeZero,
    Matrix.GeneralLinearGroup.mk', Matrix.unitOfDetInvertible, stabilized, U] at e

theorem rational_nilradical_zero : nilradical ℚ = 0 := nilradical_eq_zero ℚ

theorem counterexample : nilradical ℚ = 0 ∧ ∀ n : ℕ,
    ∃ g : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin n) ℚ,
      Matrix.GeneralLinearGroup.det g = 1 ∧ g ≠ 1 := by
  exact ⟨rational_nilradical_zero, fun n => ⟨witness n, witness_det n, witness_nonidentity n⟩⟩

#print axioms rational_nilradical_zero
#print axioms witness_det
#print axioms witness_nonidentity
#print axioms counterexample
end DeterminantKernel
