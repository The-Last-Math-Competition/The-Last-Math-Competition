import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Nat.Choose.Central
import Mathlib.RingTheory.Congruence.Hom
import Mathlib.Tactic

noncomputable section

namespace Gaussian7686

open Polynomial

def gaussian : ℕ → ℕ → Polynomial ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 1
  | n + 1, k + 1 => gaussian n k + X ^ (k + 1) * gaussian n (k + 1)

theorem gaussian_zero_column (n : ℕ) : gaussian n 0 = 1 := by
  cases n <;> rfl

theorem gaussian_pascal (n k : ℕ) :
    gaussian (n + 1) (k + 1) = gaussian n k + X ^ (k + 1) * gaussian n (k + 1) := rfl

theorem gaussian_eval_one (n k : ℕ) : (gaussian n k).eval 1 = n.choose k := by
  induction n generalizing k with
  | zero => cases k <;> simp [gaussian]
  | succ n ih =>
      cases k with
      | zero => simp [gaussian]
      | succ k => simp [gaussian, ih, Nat.choose_succ_succ]

def coefficientSum (p : Polynomial ℕ) : ℕ := p.sum (fun _ a => a)

theorem coefficientSum_eq_eval (p : Polynomial ℕ) : coefficientSum p = p.eval 1 := by
  simp [coefficientSum, Polynomial.eval_eq_sum]

def coefficientSequence (n : ℕ) : ℕ := coefficientSum (gaussian (2 * n) n)

theorem coefficientSequence_eq_centralBinom (n : ℕ) :
    coefficientSequence n = Nat.centralBinom n := by
  rw [coefficientSequence, coefficientSum_eq_eval, gaussian_eval_one,
    Nat.centralBinom_eq_two_mul_choose]

theorem coefficientSequence_strictMono : StrictMono coefficientSequence := by
  intro a b hab
  rw [coefficientSequence_eq_centralBinom, coefficientSequence_eq_centralBinom]
  exact Nat.centralBinom_strictMono hab

def EventuallyPeriodic {A : Type*} (f : ℕ → A) : Prop :=
  ∃ T : ℕ, 0 < T ∧ ∃ N : ℕ, ∀ n, N ≤ n → f (n + T) = f n

theorem coefficientSequence_not_eventuallyPeriodic : ¬ EventuallyPeriodic coefficientSequence := by
  rintro ⟨T, hT, N, hN⟩
  have hlt := coefficientSequence_strictMono (Nat.lt_add_of_pos_right hT : N < N + T)
  exact hlt.ne' (hN N le_rfl)

def atOne : RingCon (Polynomial ℕ) := RingCon.ker (Polynomial.evalRingHom 1)

theorem atOne_constant_iff (m n : ℕ) : atOne (C m) (C n) ↔ m = n := by
  simp [atOne, RingCon.ker_apply]

theorem atOne_poly_constant (p : Polynomial ℕ) : atOne p (C (coefficientSum p)) := by
  simp [atOne, RingCon.ker_apply, coefficientSum_eq_eval]

def constantClass (n : ℕ) : atOne.Quotient := (C (coefficientSequence n) : Polynomial ℕ)

theorem constantClass_eq_iff (m n : ℕ) : constantClass m = constantClass n ↔
    coefficientSequence m = coefficientSequence n := by
  change ((C (coefficientSequence m) : Polynomial ℕ) : atOne.Quotient) =
      ((C (coefficientSequence n) : Polynomial ℕ) : atOne.Quotient) ↔ _
  rw [RingCon.eq, atOne_constant_iff]

theorem constantClass_not_eventuallyPeriodic : ¬ EventuallyPeriodic constantClass := by
  rintro ⟨T, hT, N, hN⟩
  apply coefficientSequence_not_eventuallyPeriodic
  refine ⟨T, hT, N, ?_⟩
  intro n hn
  exact (constantClass_eq_iff _ _).mp (hN n hn)

end Gaussian7686
