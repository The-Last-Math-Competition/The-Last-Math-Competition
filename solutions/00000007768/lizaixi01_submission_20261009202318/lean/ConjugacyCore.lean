import Orbit
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp

open Polynomial

set_option autoImplicit false
set_option maxSynthPendingDepth 3

noncomputable section
namespace TLMC7768

def affine (a b : ℂ) : ℂ[X] := C a * X + C b
def AffineConjugate (p q : ℂ[X]) : Prop :=
  ∃ a b : ℂ, a ≠ 0 ∧ p.comp (affine a b) = (affine a b).comp q

theorem candidate_degree : candidate.natDegree = 2 := by
  simp [candidate]

theorem affine_degree (a b : ℂ) (ha : a ≠ 0) : (affine a b).natDegree = 1 := by
  simp [affine, Polynomial.natDegree_C_mul_X a ha]

theorem conjugate_degree (q : ℂ[X]) (h : AffineConjugate candidate q) : q.natDegree = 2 := by
  rcases h with ⟨a, b, ha, heq⟩
  have hd := congrArg Polynomial.natDegree heq
  simpa [Polynomial.natDegree_comp, candidate_degree, affine_degree a b ha] using hd.symm

theorem affine_bijective (a b : ℂ) (ha : a ≠ 0) :
    Function.Bijective (fun z : ℂ => a * z + b) := by
  constructor
  · intro x y hxy
    exact (mul_left_cancel₀ ha) (add_right_cancel hxy)
  · intro z
    refine ⟨(z - b) / a, ?_⟩
    field_simp [ha]
    ring

theorem affine_conjugate_iff_functional (p q : ℂ[X]) :
    AffineConjugate p q ↔
      ∃ a b : ℂ, a ≠ 0 ∧ ∀ z : ℂ, p.eval (a * z + b) = a * q.eval z + b := by
  constructor
  · rintro ⟨a, b, ha, heq⟩
    refine ⟨a, b, ha, ?_⟩
    intro z
    have he := congrArg (fun r : ℂ[X] => r.eval z) heq
    simpa [affine] using he
  · rintro ⟨a, b, ha, he⟩
    refine ⟨a, b, ha, ?_⟩
    apply Polynomial.funext
    intro z
    simpa [affine] using he z

theorem conjugate_eval (q : ℂ[X]) (a b : ℂ)
    (h : candidate.comp (affine a b) = (affine a b).comp q) (z : ℂ) :
    (a * z + b) ^ 2 - 6 = a * q.eval z + b := by
  have he := congrArg (fun p : ℂ[X] => p.eval z) h
  simpa [candidate, affine] using he

theorem shift_zero_of_even_evals (q : ℂ[X]) (a b : ℂ) (ha : a ≠ 0)
    (h : candidate.comp (affine a b) = (affine a b).comp q)
    (he : q.eval 1 = q.eval (-1)) : b = 0 := by
  have hp := conjugate_eval q a b h 1
  have hm := conjugate_eval q a b h (-1)
  rw [he] at hp
  have hab : (4 : ℂ) * a * b = 0 := by
    linear_combination hp - hm
  exact (mul_eq_zero.mp hab).resolve_left (mul_ne_zero (by norm_num) ha)

theorem not_conjugate_square : ¬ AffineConjugate candidate (X ^ 2) := by
  rintro ⟨a, b, ha, heq⟩
  have hb := shift_zero_of_even_evals (X ^ 2) a b ha heq (by norm_num)
  have h0 := conjugate_eval (X ^ 2) a b heq 0
  norm_num [hb] at h0

theorem not_conjugate_cheb_two_positive :
    ¬ AffineConjugate candidate (2 * X ^ 2 - 1) := by
  rintro ⟨a, b, ha, heq⟩
  have hb := shift_zero_of_even_evals (2 * X ^ 2 - 1) a b ha heq (by norm_num)
  have h0 := conjugate_eval (2 * X ^ 2 - 1) a b heq 0
  have h1 := conjugate_eval (2 * X ^ 2 - 1) a b heq 1
  norm_num [hb] at h0 h1
  have ha6 : a = (6 : ℂ) := h0.symm
  norm_num [ha6] at h1

theorem not_conjugate_cheb_two_negative :
    ¬ AffineConjugate candidate (-(2 * X ^ 2 - 1)) := by
  rintro ⟨a, b, ha, heq⟩
  have hb := shift_zero_of_even_evals (-(2 * X ^ 2 - 1)) a b ha heq (by norm_num)
  have h0 := conjugate_eval (-(2 * X ^ 2 - 1)) a b heq 0
  have h1 := conjugate_eval (-(2 * X ^ 2 - 1)) a b heq 1
  norm_num [hb] at h0 h1
  have ha6 : a = (-6 : ℂ) := by linear_combination -h0
  norm_num [ha6] at h1

theorem candidate_algebraic_coefficients (n : ℕ) : IsAlgebraic ℚ (candidate.coeff n) := by
  have hm : candidate = (X ^ 2 - C 6 : ℚ[X]).map (algebraMap ℚ ℂ) := by
    simp [candidate]
  rw [hm, Polynomial.coeff_map]
  exact isAlgebraic_algebraMap _

end TLMC7768
