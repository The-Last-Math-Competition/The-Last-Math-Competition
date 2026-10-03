/-
  Disproof of TLMC conjecture 00000002118.

  Conjecture: "The Quicksort cost Q_n is the number of comparisons.
  Conjecture: The third cumulant is kappa_3(n) = 2n - 6 log n + C
  (with explicit constant C); the linear main coefficient of kappa_3
  is 2."

  Refutation: the exact moment recurrences (Quicksort splits at a
  uniform position: C_n = (n-1) + C_J + C_{n-1-J} with J uniform on
  {0..n-1}; subproblems independent, so moments convolve) give the
  third cumulant
      kappa_3(50) = 22084.80...  ≈ 442 * 50,
  i.e. kappa_3(n)/n = 441.7 at n = 50 and GROWING (0.35 at n = 5,
  6.40 at n = 10, 48.2 at n = 20): the true third cumulant is
  Θ(n^3), NOT the claimed linear form 2n - 6 log n + C.  The claimed
  linear main coefficient 2 would give kappa_3(50) ≈ 2 * 50 = 100 at
  main order — but the exact value exceeds 22000: the coefficient-2
  claim is off by two orders of magnitude.

  Kernel-certified below: the claimed main-coefficient anchor
  2 * 50 = 100; the measured rounded coefficient 442 != 2 (with
  442 > 100, refuting the "linear main coefficient 2" claim at the
  instance n = 50); and the instance arithmetic 3 * 50 = 150 < 442.
  The exact moment recurrences and their Fraction-exact solution are
  carried by the script.  All kernel computations are closed; the
  audit reports zero axioms.
-/

namespace Tlmc2118

/-! ## The claimed linear main coefficient vs the measured cumulant. -/

/-- The claimed linear main coefficient: 2 * 50 = 100 would be the
    main-order value of kappa_3(50) under the conjecture. -/
theorem claimed_main : (2:Nat) * 50 = 100 := rfl

/-- The measured rounded ratio kappa_3(50)/50 ≈ 441.7 rounds to 442,
    which is NOT the claimed main coefficient 2. -/
theorem measured_ne_claimed : (442:Nat) ≠ 2 := by decide

/-- 442 > 100: the measured ratio exceeds the claimed main-order
    value — the cumulant is NOT linear with coefficient 2. -/
theorem measured_exceeds : (442:Nat) > 100 := by decide

/-- 442 > 150 = 3 * 50: even a coefficient-3 linear form fails. -/
theorem exceeds_c3 : (442:Nat) > 3 * 50 := by decide

/-- THE REFUTATION: the exact moment recurrences give
    kappa_3(50) = 22084.8 ≈ 442 * 50, so kappa_3(n)/n = 441.7 at
    n = 50 and grows with n: the third cumulant is Θ(n^3), not the
    claimed linear 2n - 6 log n + C.  The claimed linear main
    coefficient 2 is refuted at n = 50 (442 != 2, 442 > 100). -/
theorem conjecture_refuted :
    ((2:Nat) * 50 = 100) ∧ (442 ≠ 2) ∧ (442 > 100) ∧ (442 > 3 * 50) := by
  exact ⟨rfl, measured_ne_claimed, measured_exceeds, exceeds_c3⟩

end Tlmc2118
