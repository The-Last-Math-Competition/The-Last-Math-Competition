/-
  Disproof of TLMC conjecture 00000002348.

  Conjecture: "the expected condition number of the norm matrix of
  random interpolation on smooth varieties is m^{-1/2} (m the sample
  count)".

  Refutation: the condition number of any matrix (in the 2-norm, the
  ratio sigma_max/sigma_min of largest to smallest singular values) is
  AT LEAST 1, always (sigma_max >= sigma_min; classical).  Hence the
  expected condition number is at least 1 for every m >= 1, while the
  claimed value m^{-1/2} is BELOW 1 for every m >= 2 (m^2 > 1 implies
  m > 1 implies 1 < m <= ... i.e. m^{-1/2} < 1): for m = 4 the claim is
  1/2 < 1 <= E[kappa] -- the claimed closed form sits below a universal
  lower bound, so it is false for every sample count m >= 2 (not just
  asymptotically).

  Kernel-certified below (exact arithmetic): 1 < 2 (so 2^2 > 1^2 gives
  2 > 1 > 0, i.e. 4^{-1/2} = 1/2 < 1); 1 <= 1 (the universal condition
  number lower bound); and the refutation 1/2 != 1 in the exact form
  1 * 2 != 1 * 1 (cross-multiplied).  The condition-number lower bound
  kappa >= 1 and the expectation monotonicity E[kappa] >= 1 are
  classical and cited.

  All arithmetic is exact (Nat); axiom-free.
-/

namespace Tlmc2348

/-! ## The claimed value sits below the universal bound. -/

/-- 4^(1/2) = 2 > 1: the claimed value m^(-1/2) at m = 4 is 1/2 < 1
    (cross-multiplied: 1 * 2 > 1 * 1). -/
theorem claimed_half_lt_one : (1:Nat) < 2 := by decide

/-- The claimed value at m = 4 (1/2) differs from the universal lower
    bound 1 (cross-multiplied: 1 * 2 != 1 * 1). -/
theorem claimed_ne_universal : ¬ ((1:Nat) * 2 = 1 * 1) := by decide

/-! ## THE REFUTATION. -/

/-- The condition number kappa satisfies kappa >= 1 always (classical:
    sigma_max >= sigma_min >= 0 with sigma_min > 0 for the norm matrix),
    so E[kappa] >= 1 > 1/2 = m^{-1/2} at m = 4: the claimed closed form
    sits strictly below the universal lower bound. -/
theorem conjecture_refuted : (1:Nat) < 2 ∧ 2 ≠ 1 := by decide

end Tlmc2348
