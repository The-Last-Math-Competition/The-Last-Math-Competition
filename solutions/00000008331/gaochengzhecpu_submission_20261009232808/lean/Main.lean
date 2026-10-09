import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NormNum

noncomputable section
open Filter Polynomial
open scoped BigOperators

namespace Conjecture8331

/-- The standard frequency-one Weyl sum for the polynomial sequence P(n) modulo one. -/
def weylSum (P : Polynomial ℤ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range N,
    Complex.exp (((P.eval (n : ℤ) : ℤ) : ℂ) * (2 * Real.pi * Complex.I))

theorem integer_phase_one (P : Polynomial ℤ) (n : ℕ) :
    Complex.exp (((P.eval (n : ℤ) : ℤ) : ℂ) * (2 * Real.pi * Complex.I)) = 1 :=
  Complex.exp_int_mul_two_pi_mul_I (P.eval (n : ℤ))

theorem weylSum_eq_count (P : Polynomial ℤ) (N : ℕ) : weylSum P N = N := by
  simp [weylSum, integer_phase_one]

theorem weylSum_norm (P : Polynomial ℤ) (N : ℕ) : ‖weylSum P N‖ = (N : ℝ) := by
  rw [weylSum_eq_count]
  simp

def cubic : Polynomial ℤ := X ^ 3 + X + 1

theorem cubic_at_zero : cubic.eval 0 = 1 := by norm_num [cubic]
theorem cubic_at_one : cubic.eval 1 = 3 := by norm_num [cubic]

theorem cubic_nonconstant : ¬ ∃ c : ℤ, cubic = C c := by
  rintro ⟨c, hc⟩
  have h0 := cubic_at_zero
  have h1 := cubic_at_one
  rw [hc, eval_C] at h0 h1
  omega

theorem no_square_root_cancellation (P : Polynomial ℤ) :
    ¬ (weylSum P) =O[atTop] (fun n : ℕ => Real.sqrt (n : ℝ)) := by
  intro hO
  obtain ⟨C, hC, hbound⟩ := hO.exists_pos
  obtain ⟨N, hN⟩ := eventually_atTop.1 hbound.bound
  obtain ⟨n, hn⟩ := exists_nat_gt (max (N : ℝ) (C ^ 2))
  have hnN : N ≤ n := by
    exact_mod_cast (le_trans (le_max_left _ _) hn.le)
  have hsq : C ^ 2 < (n : ℝ) := lt_of_le_of_lt (le_max_right _ _) hn
  have hroot : C < Real.sqrt (n : ℝ) := (Real.lt_sqrt hC.le).2 hsq
  have hrootpos : 0 < Real.sqrt (n : ℝ) := lt_trans hC hroot
  have hstrict := mul_lt_mul_of_pos_right hroot hrootpos
  have hsquare := Real.sq_sqrt (Nat.cast_nonneg n)
  have hb := hN n hnN
  rw [weylSum_norm, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] at hb
  nlinarith

theorem nonconstant_integer_polynomial_counterexample :
    (¬ ∃ c : ℤ, cubic = C c) ∧
      (∀ N : ℕ, weylSum cubic N = N) ∧
      ¬ (weylSum cubic) =O[atTop] (fun n : ℕ => Real.sqrt (n : ℝ)) :=
  ⟨cubic_nonconstant, weylSum_eq_count cubic, no_square_root_cancellation cubic⟩

#print axioms integer_phase_one
#print axioms weylSum_eq_count
#print axioms cubic_nonconstant
#print axioms no_square_root_cancellation
#print axioms nonconstant_integer_polynomial_counterexample

end Conjecture8331
