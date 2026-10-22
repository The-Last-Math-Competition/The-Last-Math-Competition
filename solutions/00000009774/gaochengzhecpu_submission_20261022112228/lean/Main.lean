import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

noncomputable section
open Matrix Filter Topology
namespace Conjecture9774

def tri (n : ℕ) (d a : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if i = j then d else if i.val + 1 = j.val ∨ j.val + 1 = i.val then a else 0

theorem tri_succ (n : ℕ) (d a : ℝ) :
    (tri (n+1) d a).submatrix Fin.succ Fin.succ = tri n d a := by
  ext i j
  simp [tri, Fin.ext_iff]

theorem tri_minor_one (n : ℕ) (d a : ℝ) :
    ((tri (n+2) d a).submatrix Fin.succ (1 : Fin (n+2)).succAbove).det =
      a * (tri n d a).det := by
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  have hsmall :
      ((tri (n+2) d a).submatrix Fin.succ (1 : Fin (n+2)).succAbove).submatrix
        Fin.succ Fin.succ = tri n d a := by
    ext i j
    simp [tri, Fin.ext_iff, Fin.succAbove]
  rw [show (0 : Fin (n+1)).succAbove = Fin.succ from rfl, hsmall]
  have hcol (i : Fin n) :
      (tri (n+2) d a) (Fin.succ (Fin.succ i))
        ((1 : Fin (n+2)).succAbove 0) = 0 := by
    simp [tri, Fin.ext_iff, Fin.succAbove]
  simp [Matrix.submatrix_apply, hcol, tri, Fin.ext_iff, Fin.succAbove]

theorem det_recurrence (n : ℕ) (d a : ℝ) :
    (tri (n+2) d a).det = d * (tri (n+1) d a).det - a^2 * (tri n d a).det := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  rw [show (0 : Fin (n+2)).succAbove = Fin.succ from rfl, tri_succ]
  rw [Fin.sum_univ_succ]
  have hrow (i : Fin n) : (tri (n+2) d a) 0 (Fin.succ (Fin.succ i)) = 0 := by
    simp [tri, Fin.ext_iff]
  simp only [hrow, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
  simp only [Fin.succ_zero_eq_one]
  rw [tri_minor_one]
  simp [tri, Fin.ext_iff]
  ring

def coefficient (a : ℝ) (k : ℤ) : ℝ :=
  if k = 0 then 1+a^2 else if k = 1 ∨ k = -1 then a else 0

/-- Finite-section Toeplitz matrix of the Laurent polynomial
1+a^2+a*z+a*z^(-1). -/
def toeplitz (a : ℝ) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => coefficient a ((i : ℤ) - (j : ℤ))

theorem toeplitz_eq_tri (a : ℝ) (n : ℕ) :
    toeplitz a n = tri n (1+a^2) a := by
  ext i j
  simp only [toeplitz, coefficient, tri]
  have heq : (i : ℤ) - (j : ℤ) = 0 ↔ i = j := by
    rw [sub_eq_zero, Nat.cast_inj, Fin.ext_iff]
  have hadj : (i : ℤ) - (j : ℤ) = 1 ∨ (i : ℤ) - (j : ℤ) = -1 ↔
      i.val + 1 = j.val ∨ j.val + 1 = i.val := by omega
  simp only [heq, hadj]

theorem determinant_formula (n : ℕ) :
    (toeplitz (1/2) n).det = (4/3 : ℝ) * (1 - (1/4 : ℝ)^(n+1)) := by
  simp only [toeplitz_eq_tri]
  induction n using Nat.twoStepInduction with
  | zero => norm_num [Matrix.det_isEmpty]
  | one => norm_num [tri, Matrix.det_unique]
  | more n ih₀ ih₁ =>
    rw [det_recurrence, ih₁, ih₀]
    simp only [pow_succ]
    ring

theorem determinant_positive (n : ℕ) : 0 < (toeplitz (1/2) n).det := by
  rw [determinant_formula]
  apply mul_pos (by norm_num)
  apply sub_pos.mpr
  have hp : (1/4 : ℝ)^n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  rw [pow_succ]
  linarith

def symbol (a θ : ℝ) : ℝ := 1+a^2+2*a*Real.cos θ

theorem symbol_periodic (a : ℝ) : Function.Periodic (symbol a) (2*Real.pi) := by
  intro θ
  simp only [symbol, Real.cos_add_two_pi]

theorem symbol_smooth (a : ℝ) : ContDiff ℝ ⊤ (symbol a) := by
  exact contDiff_const.add (contDiff_const.mul Real.contDiff_cos)

theorem symbol_positive (θ : ℝ) : 0 < symbol (1/2) θ := by
  have h := Real.neg_one_le_cos θ
  dsimp [symbol]
  linarith

theorem determinant_limit :
    Tendsto (fun n : ℕ => (toeplitz (1/2) n).det) atTop (𝓝 (4/3 : ℝ)) := by
  simp only [determinant_formula]
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one
    (show (0 : ℝ) ≤ 1/4 by norm_num) (show (1/4 : ℝ) < 1 by norm_num)
  have hp' : Tendsto (fun n : ℕ => (1/4 : ℝ)^(n+1)) atTop (𝓝 0) := by
    simpa only [pow_succ, zero_mul] using hp.mul_const (1/4 : ℝ)
  convert (tendsto_const_nhds.sub hp').const_mul (4/3 : ℝ) using 1
  norm_num

theorem logdet_limit :
    Tendsto (fun n : ℕ => Real.log (toeplitz (1/2) n).det)
      atTop (𝓝 (Real.log (4/3))) := by
  exact (Real.continuousAt_log (by norm_num)).tendsto.comp determinant_limit

theorem leading_zero :
    Tendsto (fun n : ℕ => Real.log (toeplitz (1/2) n).det / (n : ℝ))
      atTop (𝓝 0) := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  simpa only [div_eq_mul_inv, mul_zero] using logdet_limit.mul hn

/-- A necessary universal subclause of the source: every positive smooth
Laurent symbol in this family has vanishing logarithmic secondary term. -/
def SmoothSecondaryVanishes : Prop :=
  ∀ a : ℝ, ContDiff ℝ ⊤ (symbol a) → (∀ θ : ℝ, 0 < symbol a θ) →
    ∀ L : ℝ,
      Tendsto (fun n : ℕ => Real.log (toeplitz a n).det / (n : ℝ)) atTop (𝓝 L) →
      Tendsto (fun n : ℕ => Real.log (toeplitz a n).det - (n : ℝ)*L) atTop (𝓝 0)

theorem conjecture9774_false : ¬ SmoothSecondaryVanishes := by
  intro h
  have hz := h (1/2) (symbol_smooth (1/2)) symbol_positive 0 leading_zero
  simp only [mul_zero, sub_zero] at hz
  have he : Real.log (4/3 : ℝ) = 0 := tendsto_nhds_unique logdet_limit hz
  have hp : 0 < Real.log (4/3 : ℝ) := Real.log_pos (by norm_num)
  exact (ne_of_gt hp) he

#print axioms det_recurrence
#print axioms determinant_formula
#print axioms determinant_positive
#print axioms symbol_smooth
#print axioms symbol_periodic
#print axioms symbol_positive
#print axioms logdet_limit
#print axioms leading_zero
#print axioms conjecture9774_false
end Conjecture9774
