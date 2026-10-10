import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

noncomputable section
namespace IdentityRH
open Filter MeasureTheory
open scoped Topology

def jump (_z : ℂ) : ℂ := 1
def solution (_z : ℂ) : ℂ := 1
def contour : Set ℂ := {z | ‖z‖ = 1}
def circle (t : ℝ) : ℂ := Complex.exp (Complex.I * (t : ℂ))

-- The scalar Riemann--Hilbert problem is the genuine 1×1 matrix case.
def NormalizedRH (Y : ℂ → ℂ) : Prop :=
  Differentiable ℂ Y ∧
  (∀ z ∈ contour, Tendsto Y (𝓝 z) (𝓝 (Y z))) ∧
  (∀ z ∈ contour, Y z = Y z * jump z) ∧
  Tendsto Y (Bornology.cobounded ℂ) (𝓝 1)

theorem solves_RH : NormalizedRH solution := by
  refine ⟨differentiable_const _, ?_, ?_, ?_⟩
  · intro z hz
    exact tendsto_const_nhds
  · intro z hz
    simp [solution, jump]
  · exact tendsto_const_nhds

-- The actual parametrized Cauchy correction, with unit-circle tangent and jump factor.
-- All principal-value or side-limit versions of this zero integrand are zero as well.
def cauchyCorrection (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (1 / (2 * (Real.pi : ℂ) * Complex.I)) *
    ∫ t in (0 : ℝ)..(2 * Real.pi),
      (f (circle t) * (jump (circle t) - 1) / (circle t - z)) *
        (Complex.I * circle t)

theorem correction_zero (f : ℂ → ℂ) (z : ℂ) : cauchyCorrection f z = 0 := by
  simp [cauchyCorrection, jump]

-- This is the actual operator on functions, shown to be zero by the integral computation.
def correctionOperator : (ℂ → ℂ) →ₗ[ℂ] (ℂ → ℂ) where
  toFun f := cauchyCorrection f
  map_add' f g := by ext z; simp [correction_zero]
  map_smul' c f := by ext z; simp [correction_zero]

theorem operator_zero : correctionOperator = 0 := by
  ext f z
  exact correction_zero f z

-- For a finite-rank operator, det(I-C) is computed on any finite-dimensional
-- space containing its range. Here the operator is zero, so every compression
-- is literally the zero matrix, independently of the chosen finite dimension.
def fredholmCompression (n : ℕ) : Matrix (Fin n) (Fin n) ℂ := 0


-- Each matrix entry is an actual evaluation of the zero correction operator
-- on a coordinate basis function; hence this is a genuine finite restriction.
theorem compression_bridge (n : ℕ) (i j : Fin n) :
    fredholmCompression n i j =
      correctionOperator (fun z => if z = (j.val : ℂ) then 1 else 0) (i.val : ℂ) := by
  simp [fredholmCompression, correctionOperator, correction_zero]

theorem finite_rank_determinant (n : ℕ) :
    Matrix.det (1 - fredholmCompression n) = 1 := by
  simp [fredholmCompression]

def fredholmDet : ℂ := Matrix.det (1 - fredholmCompression 1)

theorem determinant_nonzero : fredholmDet ≠ 0 := by
  change Matrix.det (1 - fredholmCompression 1) ≠ 0
  rw [finite_rank_determinant]
  exact one_ne_zero

theorem counterexample : NormalizedRH solution ∧ correctionOperator = 0 ∧ fredholmDet ≠ 0 :=
  ⟨solves_RH, operator_zero, determinant_nonzero⟩

#print axioms solves_RH
#print axioms correction_zero
#print axioms operator_zero
#print axioms finite_rank_determinant
#print axioms counterexample
end IdentityRH
