import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Logic.Function.Iterate
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

noncomputable section
namespace CriticalRelations
open Polynomial

/-- R_n(c)=f_c^[n](0), f_c(z)=z^2+c, as actual polynomials. -/
def R : ℕ → Polynomial ℝ
  | 0 => 0
  | n+1 => R n ^ 2 + X

theorem orbit_correspondence (n : ℕ) (c : ℝ) :
    (R n).eval c = (fun z : ℝ => z^2+c)^[n] 0 := by
  induction n with
  | zero => simp [R]
  | succ n ih => simp [R, Function.iterate_succ_apply', ih]

@[simp] theorem eval_at_zero (n : ℕ) : (R n).eval 0 = 0 := by
  induction n with
  | zero => simp [R]
  | succ n ih => simp [R, ih]

theorem eval_at_one_strict : StrictMono (fun n => (R n).eval 1) := by
  apply strictMono_nat_of_lt_succ
  intro n
  simp only [R, eval_add, eval_pow, eval_X]
  nlinarith [sq_nonneg ((R n).eval 1 - 1 / 2)]

theorem nontrivial (n : ℕ) : R (n+1) ≠ 0 := by
  intro h
  have hp := eval_at_one_strict (Nat.zero_lt_succ n)
  change (R 0).eval 1 < (R (n+1)).eval 1 at hp
  rw [h] at hp
  simp only [R, eval_zero] at hp
  exact (lt_irrefl 0) hp

theorem distinct : Function.Injective R := by
  intro m n h
  apply eval_at_one_strict.injective
  exact congrArg (fun P : Polynomial ℝ => P.eval 1) h

/-- Two critical equations are compatible when the same parameter solves
both. All witnesses below use c=0, so they also have zero resultant. -/
def Compatible (P Q : Polynomial ℝ) : Prop := ∃ c : ℝ, P.eval c = 0 ∧ Q.eval c = 0

theorem pairwise_compatible (m n : ℕ) : Compatible (R m) (R n) :=
  ⟨0, eval_at_zero m, eval_at_zero n⟩

/-- The standard Sylvester coefficient matrix, with nominal degrees m,n.
Its rows are shifted, descending coefficient lists of P and Q. -/
def sylvester (P Q : Polynomial ℝ) (m n : ℕ) : Matrix (Fin (m+n)) (Fin (m+n)) ℝ :=
  fun i j => if i.val < n then
    if i.val ≤ j.val ∧ j.val ≤ m + i.val then P.coeff (m + i.val - j.val) else 0
  else
    if i.val - n ≤ j.val ∧ j.val ≤ i.val then Q.coeff (i.val - j.val) else 0

theorem sylvester_det_zero (P Q : Polynomial ℝ) (m n : ℕ) (hsize : 0 < m+n)
    (hP : P.coeff 0 = 0) (hQ : Q.coeff 0 = 0) : (sylvester P Q m n).det = 0 := by
  apply Matrix.det_eq_zero_of_column_eq_zero ⟨m+n-1, by omega⟩
  intro i
  unfold sylvester
  split_ifs with hi hj hj
  · have hz : m + i.val - (m+n-1) = 0 := by omega
    simp only [hz, hP]
  · rfl
  · have hz : i.val - (m+n-1) = 0 := by omega
    simp only [hz, hQ]
  · rfl

theorem positive_degree (n : ℕ) : 0 < (R (n+1)).natDegree := by
  by_contra hn
  have hd : (R (n+1)).natDegree = 0 := by omega
  have he := Polynomial.eq_C_of_natDegree_eq_zero hd
  have hc : (R (n+1)).coeff 0 = 0 := by
    rw [Polynomial.coeff_zero_eq_eval_zero]
    exact eval_at_zero _
  rw [hc, map_zero] at he
  exact nontrivial n he

/-- The Sylvester determinant at the true polynomial degrees. -/
theorem pairwise_resultant_zero (m n : ℕ) :
    (sylvester (R (m+1)) (R (n+1)) (R (m+1)).natDegree (R (n+1)).natDegree).det = 0 := by
  apply sylvester_det_zero
  · have := positive_degree m
    omega
  · rw [Polynomial.coeff_zero_eq_eval_zero]
    exact eval_at_zero _
  · rw [Polynomial.coeff_zero_eq_eval_zero]
    exact eval_at_zero _

/-- The indices refer to the actual critical-orbit polynomials, not arbitrary
polynomials. Nontrivial means the equation is not the zero polynomial. -/
def ValidChain (N : ℕ) (indices : Fin N → ℕ) : Prop :=
  (∀ i, 0 < indices i) ∧ Function.Injective (fun i => R (indices i)) ∧
  (∀ i, R (indices i) ≠ 0) ∧
  (∀ i j, Compatible (R (indices i)) (R (indices j))) ∧
  (∀ i j, (sylvester (R (indices i)) (R (indices j))
    (R (indices i)).natDegree (R (indices j)).natDegree).det = 0)

/-- Compatible critical-relation lists of every finite length. -/
theorem arbitrary_length (N : ℕ) : ∃ indices : Fin N → ℕ, ValidChain N indices := by
  refine ⟨fun i => i.val+1, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact Nat.zero_lt_succ i.val
  · intro i j h
    have h' : i.val + 1 = j.val + 1 := distinct h
    exact Fin.ext (Nat.add_right_cancel h')
  · intro i
    exact nontrivial i.val
  · intro i j
    exact pairwise_compatible _ _
  · intro i j
    exact pairwise_resultant_zero i.val j.val

theorem no_depth_three_bound :
    ¬ (∀ N : ℕ, (∃ indices : Fin N → ℕ, ValidChain N indices) → N ≤ 3) := by
  intro h
  have := h 4 (arbitrary_length 4)
  omega

#print axioms no_depth_three_bound
#print axioms pairwise_resultant_zero
#print axioms orbit_correspondence
end CriticalRelations
