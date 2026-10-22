import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Eigenspace.Matrix
import Mathlib.Data.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

noncomputable section
open Matrix
open scoped ComplexOrder
namespace Conjecture8262

/-- The continuous-time covariance algebraic Riccati equation, with
isotropic system and observation noises and observation matrix H. -/
def RiccatiSteady {n : Type} [Fintype n] [DecidableEq n]
    (A H P : Matrix n n ℝ) (σsys σobs : ℝ) : Prop :=
  A * P + P * A.transpose + (σsys^2) • (1 : Matrix n n ℝ) -
    (σobs^2)⁻¹ • (P * H.transpose * H * P) = 0

/-- Continuous-time stability uses the complex spectrum of the real matrix. -/
def Hurwitz {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ) : Prop :=
  ∀ z ∈ spectrum ℂ (A.map (algebraMap ℝ ℂ)), z.re < 0

/-- For a positive-definite symmetric matrix, the spectral condition
number is its largest eigenvalue divided by its smallest eigenvalue. -/
def SpectralCondition {n : Type} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℝ) (c : ℝ) : Prop :=
  ∃ lo hi : ℝ, IsLeast (spectrum ℝ P) lo ∧ IsGreatest (spectrum ℝ P) hi ∧
    0 < lo ∧ c = hi / lo

def ClaimedBound : Prop :=
  ∀ (d : ℕ) (A H P : Matrix (Fin d) (Fin d) ℝ) (σsys σobs c : ℝ),
    0 < σsys → 0 < σobs → P.PosDef → RiccatiSteady A H P σsys σobs →
    Hurwitz (A - (σobs^2)⁻¹ • (P * H.transpose * H)) →
    SpectralCondition P c → c ≤ (σobs / σsys)^2

def A : Matrix (Fin 2) (Fin 2) ℝ := diagonal ![3/4, -3/4]
def H : Matrix (Fin 2) (Fin 2) ℝ := 1
def P : Matrix (Fin 2) (Fin 2) ℝ := diagonal ![2, 1/2]

theorem covariance_positive : P.PosDef := by
  apply Matrix.PosDef.diagonal
  intro i
  fin_cases i <;> norm_num

theorem riccati_equation : RiccatiSteady A H P 1 1 := by
  unfold RiccatiSteady A H P
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal]

theorem closed_loop : A - (1 : ℝ) • (P * H.transpose * H) =
    diagonal (![(-5/4 : ℝ), -5/4]) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [A, H, P, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal]

theorem stabilizing : Hurwitz (A - ((1 : ℝ)^2)⁻¹ • (P * H.transpose * H)) := by
  norm_num only [one_pow, inv_one]
  rw [closed_loop]
  intro z hz
  have hm : (diagonal (![(-5/4 : ℝ), -5/4])).map (algebraMap ℝ ℂ) =
      diagonal (![(-5/4 : ℂ), -5/4]) := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.diagonal]
  rw [hm, spectrum_diagonal] at hz
  obtain ⟨i, rfl⟩ := hz
  fin_cases i <;> norm_num

theorem covariance_spectrum (x : ℝ) : x ∈ spectrum ℝ P ↔ x = 2 ∨ x = 1/2 := by
  rw [P, spectrum_diagonal]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · rintro (rfl | rfl)
    · exact ⟨0, by norm_num⟩
    · exact ⟨1, by norm_num⟩

theorem condition_number : SpectralCondition P 4 := by
  refine ⟨1/2, 2, ?_, ?_, by norm_num, by norm_num⟩
  · constructor
    · exact (covariance_spectrum _).2 (Or.inr rfl)
    · intro x hx
      rcases (covariance_spectrum x).1 hx with rfl | rfl <;> norm_num
  · constructor
    · exact (covariance_spectrum _).2 (Or.inl rfl)
    · intro x hx
      rcases (covariance_spectrum x).1 hx with rfl | rfl <;> norm_num

theorem conjecture8262_false : ¬ ClaimedBound := by
  intro h
  have hc := h 2 A H P 1 1 4 (by norm_num) (by norm_num)
    covariance_positive riccati_equation stabilizing condition_number
  norm_num at hc

#print axioms covariance_positive
#print axioms stabilizing
#print axioms condition_number
#print axioms conjecture8262_false
end Conjecture8262
