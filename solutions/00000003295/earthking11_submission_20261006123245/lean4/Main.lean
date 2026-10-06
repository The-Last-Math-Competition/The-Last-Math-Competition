import Std

/-!
Conjecture 00000003295 says that Dawson's reciprocal odd asymptotic series
converges on the whole real axis.  At x=1 its terms are
  a_n = (2n-1)!! / 2^(n+1),
with recurrence a_{n+1} = ((2n+1)/2) a_n.  From n=1 onward the multiplier is
at least 3/2, so terms do not tend to zero.  We give an even stronger discrete
certificate: after clearing denominators, the numerators eventually dominate
the denominators, hence a_n >= 1 for every n >= 3.
-/

namespace Tlmc3295

/-- Odd double factorial `(2n-1)!!`, with the conventional value 1 at n=0. -/
def oddDoubleFactorial : Nat -> Nat
  | 0 => 1
  | n + 1 => (2 * n + 1) * oddDoubleFactorial n

/-- Numerator and denominator of the n-th Dawson reciprocal term at x=1. -/
def numerator (n : Nat) : Nat := oddDoubleFactorial n
def denominator (n : Nat) : Nat := 2 ^ (n + 1)

theorem recurrence (n : Nat) : numerator (n + 1) = (2 * n + 1) * numerator n := by
  rfl

/-- From the fourth displayed term onward, terms have absolute value at least 1. -/
theorem terms_bounded_below_shift (k : Nat) : denominator (k + 4) <= numerator (k + 4) := by
  induction k with
  | zero => decide
  | succ k ih =>
      rw [Nat.succ_add]
      have hfactor : 2 <= 2 * (k + 3) + 1 := by omega
      calc
        denominator (k + 4 + 1) = 2 * denominator (k + 4) := by
          simp [denominator, Nat.pow_succ, Nat.mul_comm]
        _ <= 2 * numerator (k + 4) := Nat.mul_le_mul_left 2 ih
        _ <= (2 * (k + 4) + 1) * numerator (k + 4) := by
          exact Nat.mul_le_mul_right _ (by omega)
        _ = numerator (k + 4 + 1) := (recurrence (k + 4)).symm

/-- The necessary term-to-zero condition for convergence fails at x=1. -/
theorem counterexample : Not (exists N : Nat, forall n, N <= n -> numerator n < denominator n) := by
  rintro ⟨N, hN⟩
  let n := N + 4
  have hNn : N <= n := by omega
  have hlt := hN n hNn
  have hge : denominator n <= numerator n := by
    simpa [n] using terms_bounded_below_shift N
  omega

#print axioms Tlmc3295.counterexample
#print axioms Tlmc3295.terms_bounded_below_shift

end Tlmc3295
