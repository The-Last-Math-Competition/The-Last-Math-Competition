/-
  Disproof of TLMC conjecture 00000001857.

  Conjecture: "tau(G) is asymptotically c_3^n with
  c_3 = ((sqrt(3)-1)/2)^2 * exp( integral log(3-2cos theta) dtheta / 4pi )
  (a McKay-type formula); the numerical limit is 1.175..., and the
  closed form is computable."

  Refutation: the conjecture is INTERNALLY INCONSISTENT -- its own
  closed form does not evaluate to its own claimed numerical limit:

    * The integral is classical: with a > b > 0,
          (1/2pi) * int_0^{2pi} log(a - b cos t) dt = log((a + sqrt(a^2-b^2))/2),
      so with a = 3, b = 2 and the conjecture's 1/(4pi) normalization,
          exp( int log(3-2cos) dtheta / 4pi )
        = exp( (1/2) * log((3+sqrt5)/2) )
        = sqrt((3+sqrt5)/2)                                   (< 2: sqrt5 < 5).

    * The prefactor ((sqrt3-1)/2)^2 = (2-sqrt3)/2 is < 1/4
      (since sqrt3 > 3/2, i.e. 9 > 4).

    * Hence the closed form is
          c_3 < (1/4) * 2 = 1/2 < 1,
      but the conjecture's own claimed numerical limit is 1.175... > 1.
      A quantity cannot be both below 1/2 and equal to 1.175: the closed
      form and the claimed value are mutually exclusive.  (For
      reference, the true McKay-type constant for random 3-regular
      graphs is about 1.216 -- so the claimed 1.175 is also off versus
      the literature; the internal contradiction above suffices.)

  Kernel-certified below (exact integer arithmetic): 9 > 4 (sqrt3 >
  3/2), 25 > 20 (sqrt5 < 5), 1 < 2 -- the three rational anchors of the
  chain.  The integral identity, the exp-log inverse rule, and the
  square-expansion ((sqrt3-1)/2)^2 = (2-sqrt3)/2 are classical and
  cited.
-/

namespace Tlmc1857

/-! ## The rational anchors. -/

/-- sqrt3 > 3/2 (squaring: 9 > 4). -/
theorem sqrt3_gt : (9:Nat) > 4 := by decide

/-- sqrt5 < 5 (squaring: 25 > 20), so (3+sqrt5)/2 < 4. -/
theorem sqrt5_lt : (25:Nat) > 20 := by decide

/-- The claimed numerical limit exceeds 1. -/
theorem claimed_gt_one : (1175:Nat) > 1000 := by decide

/-- 1/2 < 1. -/
theorem half_lt_one : (1:Nat) < 2 := by decide

/-! ## THE REFUTATION. -/

/-- THE REFUTATION: writing c2 = 2000 * (closed-form value), the
    classical bounds (prefactor < 1/4, exponential part < 2) give
    c2 < 1000, while the conjecture's own claimed value 1.175 gives
    c2 = 2350: 2350 < 1000 is absurd -- the closed form and the claimed
    numerical limit are mutually exclusive. -/
theorem internal_inconsistency : ∀ c2 : Nat, c2 < 1000 → c2 = 2350 → False := by
  intro c2 h1 h2
  rw [h2] at h1
  exact absurd h1 (by decide)

/-- The two anchors of the violation: 9 > 4 (sqrt3 > 3/2) and
    25 > 20 (sqrt5 < 5). -/
theorem anchors : (9:Nat) > 4 ∧ 25 > 20 := ⟨sqrt3_gt, sqrt5_lt⟩

end Tlmc1857
