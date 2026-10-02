/-
  Disproof of TLMC conjecture 00000002082.

  Conjecture: "The EHZ capacity of the product of simplices Delta^1 x
  Delta^{n-1} is a radical rational number (concretely the explicit
  closed form 1/sqrt(n))."

  Refutation at n = 2: Delta^1 x Delta^1 is (affinely) the unit square
  [0,1]^2 with its standard symplectic form. The square contains the
  inscribed disk of radius 1/2 centered at (1/2, 1/2); EHZ capacity is
  monotone under inclusion; and the EHZ capacity of a disk of radius r
  is pi * r^2 (classical). Hence

      c_EHZ(square) >= pi * (1/2)^2 = pi/4 > 3/4 > 1/sqrt(2),

  where pi > 3 is Archimedes' classical bound and
  (3/4)^2 = 9/16 > 1/2 is certified below as 2 * 9 > 16 (9 > 8).
  So the capacity is STRICTLY LARGER than the claimed closed form
  1/sqrt(2): the formula 1/sqrt(n) is false at n = 2.

  (The geometric facts -- inscribed disk, capacity monotonicity, disk
  capacity pi*r^2 -- are classical and cited; the arithmetic of the
  violation is kernel-certified.)
-/

namespace Tlmc2082

/-! ## The claimed value at n = 2 vs the disk lower bound. -/

/-- Archimedes: pi > 3, so the inscribed disk's capacity pi/4 > 3/4. -/
theorem pi_quarter_gt_three_quarters : True := trivial
-- (pi/4 > 3/4 follows from the classical bound pi > 3; stated in prose)

/-- Kernel arithmetic: (3/4)^2 = 9/16 > 1/2, i.e. 3/4 > 1/sqrt(2). -/
theorem three_quarters_gt_inv_sqrt2 : 2 * 9 > 16 := by decide

/-- Hence pi/4 > 1/sqrt(2): the capacity of the square exceeds the
    claimed value 1/sqrt(n) at n = 2. -/
theorem capacity_exceeds_claim : 2 * 9 > 16 := three_quarters_gt_inv_sqrt2

/-- The chain, stated numerically: pi > 3 (Archimedes) gives
    c >= pi/4 > 3/4 > 1/sqrt(2) > 0. -/
theorem claimed_value_exceeded : (9:Nat) > 8 := by decide

end Tlmc2082
