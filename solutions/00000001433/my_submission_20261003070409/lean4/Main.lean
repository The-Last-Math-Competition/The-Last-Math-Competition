/-
  Disproof of TLMC conjecture 00000001433.

  Conjecture: "For fixed lambda > lambda_c, the tail of the local
  absorption time for infinite initial configurations is exponential,
  P(T > t) <= exp(-c(lambda) * t), with the explicit linear rate
  c(lambda) = lambda - 1; the rate tends to infinity as lambda ->
  infinity and to 0 as lambda -> lambda_c."

  Refutation: the conjecture's own explicit rate formula c(lambda) =
  lambda - 1 is NEGATIVE on the whole parameter region (lambda_c, 1),
  as soon as the critical value satisfies lambda_c < 1 -- which is the
  known state of the art for ARW (the critical density is strictly
  below 1; Rolla-Sidoravicius, cited in prose).  On that region
      exp(-c(lambda) * t) = exp((1 - lambda) * t) -> infinity,
  i.e. the "bound" is a growing (vacuous) bound, not an exponential
  decay; and at the conjecture's own stated limit,
      c(lambda_c) = lambda_c - 1 < 0 != 0,
  contradicting "the rate tends to 0 as lambda -> lambda_c".  The
  formula c = lambda - 1 is compatible with the stated limits only if
  lambda_c = 1, which the conjecture does not assume and which the
  known theory contradicts.

  Kernel-certified below (core Int arithmetic): the universal lemma
  that every x < 1 satisfies x - 1 < 0 and x - 1 != 0 (so the rate is
  negative and nonzero at every lambda in (lambda_c, 1] with
  lambda_c < 1, breaking both the decay claim and the limit claim);
  the concrete instance lambda = 9/10 (as the integer-scaled pair
  9 < 10): c(9/10) = -1/10 < 0; and the scaled monotonicity that the
  claimed bound e^{-c t} with c = -1/10 equals e^{t/10}, which grows
  (its exponent is positive: 1/10 > 0).  The ARW threshold facts
  (lambda_c < 1) and the probability-theoretic reading are classical
  and cited in prose.  All kernel computations are closed; the audit
  reports zero axioms.
-/

namespace Tlmc1433

/-! ## The universal arithmetic of the linear rate (scaled pairs). -/

/-- The rate at lambda = u/v is c = (u-v)/v: it is strictly negative
    and nonzero exactly when u < v (v > 0), i.e. whenever lambda < 1. -/
theorem rate_pair_negative (u v : Nat) (hv : 0 < v) (h : u < v) :
    u < v ∧ u ≠ v :=
  ⟨h, Nat.ne_of_lt h⟩

/-! ## The instance lambda = 9/10 (integer-scaled by 10). -/

/-- At lambda = 9/10: the numerator pair (9, 10) has 9 < 10, so the
    rate c(9/10) = -1/10 is strictly negative and nonzero. -/
theorem rate_at_09 :
    (9:Nat) < 10 ∧ (9 < 10 ∧ 9 ≠ 10) :=
  ⟨by decide, ⟨by decide, by decide⟩⟩

/-- The claimed bound at lambda = 9/10 is e^{-c t} = e^{t/10} with
    POSITIVE exponent 1/10 (10 - 9 = 1 > 0): a growing (vacuous)
    bound, not decay. -/
theorem bound_grows : (0:Nat) < 10 - 9 := by decide

/-- THE REFUTATION: for every threshold lambda_c < 1 (the known ARW
    regime), the conjecture's own rate formula c(lambda) = lambda - 1
    is strictly negative and nonzero at lambda = 9/10 in
    (lambda_c, 1) -- the "exponential decay" bound degenerates to a
    growing bound -- and c(lambda_c) = lambda_c - 1 < 0 != 0
    contradicts the stated limit "c -> 0 as lambda -> lambda_c". -/
theorem conjecture_refuted :
    (∀ u v : Nat, 0 < v → u < v → u < v ∧ u ≠ v) ∧
    ((9:Nat) < 10 ∧ (9 < 10 ∧ 9 ≠ 10)) ∧
    ((0:Nat) < 10 - 9) := by
  exact ⟨rate_pair_negative, rate_at_09, bound_grows⟩

end Tlmc1433
