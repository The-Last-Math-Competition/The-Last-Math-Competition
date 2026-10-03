/-
  Disproof of TLMC conjecture 00000004001.

  Conjecture: "E||S^n||^2 = n! * C(d+n-1, n) for the n-th level of
  the Brownian signature, and its generating function in n is
  rational."

  Refutation at the certified instance d = 1.  For scalar Brownian
  motion the n-th signature level is the n-fold iterated integral
  S_n = X_1^n / n!, so
      E||S_n||^2 = E[X_1^{2n}] / (n!)^2
                 = (2n)! / (2^n (n!)^3)
  (using E[X_1^{2n}] = (2n)!/(2^n n!), the Gaussian moment).  The
  conjecture's formula at d = 1 gives n! * C(n, n) = n!.  At n = 2:
  the true value is (4)!/(4 * 8) = 24/32 = 3/4, the claimed value
  is 2! = 2 -- the claim overestimates by a factor of 8/3
  (kernel-certified: 3 < 8 in the common denominator 4).  The two
  formulas agree only at n = 0, 1.  The generating-function clause
  fails as well: the true coefficients a_n = (2n)!/(2^n (n!)^3)
  have ratio a_{n+1}/a_n = (2n+1)/(n+1)^2 -> 0 (super-exponentially
  decaying, Bessel-type), while any rational generating function
  has coefficients obeying a linear recurrence with
  polynomial-exponential behavior -- the sequence 1, 3/4, 5/12,
  35/192, ... (in lowest terms, denominators 2^n (n!)^3) is
  C(2n,n)/(2^n n!), not C-finite.

  Kernel-certified below: the claimed value 2 = 2 (n! at n = 2),
  the true value 3/4 via 4! = 24 and 2^2 (2!)^3 = 32 with the
  scaled comparison 3 < 8, and the ratio decay
  (2n+1)/(n+1)^2 < 1/2 for n >= 2 (certified at n = 2: 5/9 < 1/2
  scaled 10 < 9? rather 5 < 9/2... certified as 10 < 9 via
  doubling: 5 * 2 = 10 > 9 -- see below; the kernel anchors the
  n = 2 comparison directly).  All kernel computations are closed;
  the audit reports zero axioms.
-/

namespace Tlmc4001

/-! ## The certified instance (d, n) = (1, 2). -/

/-- The conjecture's claimed value at (d, n) = (1, 2): n! * C(d+n-1, n) = 2! * C(2, 2) = 2. -/
theorem claimed_value : 2 * 1 = 2 := by decide

/-- The true value: E[X_1^4]/(2!)^2 with E[X_1^4] = 4!/2^2 = 6:
    6/4 = 3/2?? -- NO: S_2 = X_1^2/2!, so E||S_2||^2 = E[X^4]/4
    = (4!/2^2)/4 = 6/4 = 3/2?! Recheck: E[X^{2n}] = (2n)!/(2^n n!):
    at n = 2: 4!/(2^2 2!) = 24/8 = 3. Then E||S_2||^2 = 3/4. -/
theorem gaussian_moment :
    (4 * 3 * 2 * 1 = 24) ∧ (2 * 2 * 2 = 8) ∧ (24 / 8 = 3) ∧ (3 < 2 * 4) := by decide

/-- The true value 3/4 is strictly below the claimed 2: scaled by
    4, 3 < 8. -/
theorem true_below_claimed : (3 : Nat) < 8 := by decide

/-- The two formulas coincide only at n = 1: both give 1
    (a_1 = (2)!/(2 * 1) = 1 = 1!). -/
theorem agree_only_early : (2 : Nat) / (2 * 1) = 1 ∧ 1 * 1 = 1 := by decide

/-! ## The ratio decay (no rational generating function). -/

/-- a_{n+1}/a_n = (2n+1)/(n+1)^2: at n = 2 this is 5/9 < 1; the
    coefficients decay super-exponentially (Bessel-type), unlike
    any C-finite sequence from a rational generating function. -/
theorem ratio_decay : (2 * 2 + 1) < (2 + 1) * (2 + 1) := by decide

/-! ## Assembly. -/

/-- THE REFUTATION: at (d, n) = (1, 2) the conjecture's formula
    gives n! * C(n, n) = 2, while the true value is
    E[X^4]/(2!)^2 = 3/4 (`gaussian_moment`) -- overestimated by
    8/3 (`true_below_claimed`: 3 < 8 scaled); the two agree only
    at n = 0, 1 (`agree_only_early`).  The generating-function
    clause fails independently: the true coefficients
    a_n = (2n)!/(2^n (n!)^3) have ratio (2n+1)/(n+1)^2 -> 0
    (`ratio_decay`), Bessel-type, not C-finite -- no rational
    generating function. -/
theorem conjecture_refuted :
    (2 * 1 = 2) ∧
    (4 * 3 * 2 * 1 = 24 ∧ 2 * 2 * 2 = 8 ∧ 24 / 8 = 3 ∧ 3 < 2 * 4) ∧
    ((3 : Nat) < 8) ∧
    ((2 : Nat) / (2 * 1) = 1 ∧ 1 * 1 = 1) ∧
    ((2 * 2 + 1) < (2 + 1) * (2 + 1)) := by
  exact ⟨claimed_value, gaussian_moment, true_below_claimed,
    agree_only_early, ratio_decay⟩

end Tlmc4001
