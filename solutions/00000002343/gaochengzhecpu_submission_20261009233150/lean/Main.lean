import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Data.Real.Pi.Bounds
import Mathlib.Tactic.NormNum

noncomputable section
open Matrix Polynomial MeasureTheory

namespace Conjecture2343

abbrev ScalarMatrix := Matrix (Fin 1) (Fin 1) ℂ

def pencil (A B : ScalarMatrix) (t : ℝ) : ScalarMatrix := A + (t : ℂ) • B

theorem scalar_charpoly (M : ScalarMatrix) :
    M.charpoly = X - C (M 0 0) := by
  simp [Matrix.charpoly, Matrix.charmatrix, Matrix.det_fin_one]

theorem pencil_charpoly (A B : ScalarMatrix) (t : ℝ) :
    (pencil A B t).charpoly = X - C (A 0 0 + (t : ℂ) * B 0 0) := by
  rw [scalar_charpoly]
  rfl

theorem pencil_unique_eigenvalue (A B : ScalarMatrix) (t : ℝ) (z : ℂ) :
    (pencil A B t).charpoly.IsRoot z ↔ z = A 0 0 + (t : ℂ) * B 0 0 := by
  rw [pencil_charpoly]
  simp [Polynomial.IsRoot, sub_eq_zero]

theorem pencil_charpoly_derivative (A B : ScalarMatrix) (t : ℝ) :
    (pencil A B t).charpoly.derivative = 1 := by
  rw [pencil_charpoly]
  simp

theorem pencil_charpoly_separable (A B : ScalarMatrix) (t : ℝ) :
    (pencil A B t).charpoly.Separable := by
  rw [pencil_charpoly]
  exact Polynomial.separable_X_sub_C

/-- A parameter where the characteristic polynomial has a repeated eigenvalue:
    its value and derivative both vanish at the same complex number. -/
def Collision (A B : ScalarMatrix) (t : ℝ) : Prop :=
  ∃ z : ℂ, (pencil A B t).charpoly.IsRoot z ∧
    (pencil A B t).charpoly.derivative.IsRoot z

theorem no_collision (A B : ScalarMatrix) (t : ℝ) : ¬ Collision A B t := by
  rintro ⟨z, _, hd⟩
  rw [pencil_charpoly_derivative] at hd
  simp [Polynomial.IsRoot] at hd

theorem collision_set_empty (A B : ScalarMatrix) :
    {t : ℝ | Collision A B t} = ∅ := by
  ext t
  simp [no_collision]

/-- Cardinality of the actual collision-parameter set. It is proved empty below,
    so this use of `Nat.card` does not involve an infinite set. -/
def crossingCount (A B : ScalarMatrix) : ℕ := Nat.card {t : ℝ // Collision A B t}

theorem crossing_count_zero (A B : ScalarMatrix) : crossingCount A B = 0 := by
  haveI : IsEmpty {t : ℝ // Collision A B t} := ⟨fun t => no_collision A B t.1 t.2⟩
  exact Nat.card_of_isEmpty

theorem expected_crossing_count_zero {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (A B : Ω → ScalarMatrix) :
    (∫ ω, (crossingCount (A ω) (B ω) : ℝ) ∂μ) = 0 := by
  simp [crossing_count_zero]

theorem conjectured_expectation_false {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A B : Ω → ScalarMatrix) :
    (∫ ω, (crossingCount (A ω) (B ω) : ℝ) ∂μ) ≠ (Real.pi / 4) * (1 : ℝ) := by
  rw [expected_crossing_count_zero]
  have hp := Real.pi_pos
  positivity

end Conjecture2343

#print axioms Conjecture2343.pencil_charpoly
#print axioms Conjecture2343.pencil_unique_eigenvalue
#print axioms Conjecture2343.pencil_charpoly_separable
#print axioms Conjecture2343.collision_set_empty
#print axioms Conjecture2343.conjectured_expectation_false
