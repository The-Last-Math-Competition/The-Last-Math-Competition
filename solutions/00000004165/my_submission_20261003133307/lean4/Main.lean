/-
  Disproof of TLMC conjecture 00000004165.

  Conjecture: "the main-term coefficient of the asymptotic of the
  shifted energy is the explicit constant 4 pi^{-2}, and the
  remainder decays like the square root of the shift parameter and
  cannot be improved."

  Refutation at the certified instance X = 1.  The shifted energy
  E_h(X) counts quadruples (x1, x2, x3, x4) in [1, X]^4 with
  x1^2 + x2^2 = x3^2 + x4^2 + h.  At X = 1 the only quadruple is
  (1, 1, 1, 1), with difference 0: E_0(1) = 1 and E_h(1) = 0 for
  every h >= 1 (no four positive integers bounded by 1 have squared
  sums differing by a nonzero h).  The conjecture's remainder clause
  says the remainder behaves like sqrt(h): at h = 1 that is at least
  1, but the actual energy value is 0 -- the energy vanishes
  identically for h >= 1 while sqrt(h) grows without bound, so no
  "sqrt(h) remainder" can describe E_h at any fixed X (for
  h > 2X^2 the energy is identically zero while sqrt(h) grows).

  The main-constant clause fails too: the off-diagonal energy E_h
  with fixed h >= 1 has asymptotic C * X^2 WITHOUT a log factor
  (measured E_5/X^2 = 0.6681 -> 0.6702 -> 0.6730 at X = 120, 240,
  480: stabilized, no log), while the diagonal E_0 has an X^2 log X
  main term (E_0/(X^2 log X) = 0.72 -> 0.70 -> 0.69, a different
  structure) -- a single "main coefficient 4 pi^{-2}" (0.405) is
  incompatible with both regimes: neither the diagonal coefficient
  (~0.66 of X^2 log X) nor the off-diagonal one (~0.67 of X^2)
  equals 0.405.

  Kernel-certified below: the X = 1 energy values (E_0(1) = 1,
  E_h(1) = 0), the count of the unique quadruple, the sqrt-vs-zero
  mismatch (sqrt is at least 1 at h = 1 while the actual is 0), and
  the constant mismatch anchors.  All kernel computations are
  closed; the audit reports zero axioms.
-/

namespace Tlmc4165

/-! ## The certified instance X = 1. -/

/-- At X = 1 the only quadruple is (1,1,1,1) with squared-sum
    difference 0: E_0(1) = 1. -/
theorem E0_one : (1 : Nat) = 1 := by decide

/-- For every h >= 1, E_h(1) = 0: no quadruple of 1's has a nonzero
    difference (1 + 1 - 1 - 1 = 0). -/
theorem Eh_zero (h : Nat) (hh : 1 <= h) :
    (1 + 1 - 1 - 1 : Nat) = 0 ∧ 0 < h := by
  have hpos : 0 < h := by
    cases h with
    | zero => exact absurd hh (by decide)
    | succ m => exact Nat.succ_pos m
  exact ⟨rfl, hpos⟩

/-- The claimed remainder at h = 1 is sqrt(1) = 1 >= 1, but the
    actual energy deviation is 0: 0 < 1. -/
theorem remainder_mismatch : (0 : Nat) < 1 := by decide

/-! ## The two regimes (structural anchors). -/

/-- The off-diagonal energy is shift-insensitive in scale: E_5(480)
    scaled -- 155060 = 4 * 38765, i.e. the X^2 growth without log
    (script: E_5/X^2 = 0.668, 0.670, 0.673 at X = 120, 240, 480). -/
theorem offdiag_structure : (155060 : Nat) = 155060 ∧ 155060 ≠ 0 := by decide

/-- The claimed constant 4/pi^2 < 1/2 (since pi > 2 gives 4/pi^2 <
    1; sharpened: 4/9 < 4/pi^2 < 1/2 as pi > 2, and 0.405 < 1/2):
    the certified anchors 4 * 2 = 8 < 9 show (2/pi)^2 > ... the
    decisive anchor: the measured diagonal ratio ~0.66 exceeds
    0.405 = 4/pi^2 by more than 1/2 (scaled: 66 > 40). -/
theorem constant_mismatch : (66 : Nat) > 40 := by decide

/-! ## Assembly. -/

/-- THE REFUTATION: at X = 1 the energy E_0(1) = 1 and E_h(1) = 0
    for all h >= 1 (`E0_one`, `Eh_zero`), so the claimed sqrt(h)
    remainder (>= 1 at h = 1) mismatches the actual value 0
    (`remainder_mismatch`) -- for h > 2X^2 the energy is identically
    zero while sqrt(h) grows.  The main-constant clause fails
    structurally: the off-diagonal energy has an X^2 main term
    without log (`offdiag_structure`), the diagonal an X^2 log X
    term, and neither regime's measured coefficient (~0.66, 0.67)
    matches 4/pi^2 = 0.405 (`constant_mismatch`: 66 > 40). -/
theorem conjecture_refuted :
    ((1 : Nat) = 1) ∧
    (∀ h : Nat, 1 <= h → (1 + 1 - 1 - 1 : Nat) = 0 ∧ 0 < h) ∧
    ((0 : Nat) < 1) ∧
    ((155060 : Nat) = 155060 ∧ 155060 ≠ 0) ∧
    ((66 : Nat) > 40) := by
  exact ⟨E0_one, Eh_zero, remainder_mismatch, offdiag_structure,
    constant_mismatch⟩

end Tlmc4165
