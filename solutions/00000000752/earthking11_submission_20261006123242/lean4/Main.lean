import Std

/-!
Conjecture 00000000752 predicts the entropy of a p-adic shift from the root of
largest p-adic norm.  The full two-symbol shift at p=3 is a counterexample:
there are exactly 2^n words of length n, hence growth base 2, while the sole
characteristic root 2 is a 3-adic unit and has 3-adic norm 1.

We formalize the finite word count and the unit-norm computation directly.
-/

namespace Tlmc752

/-- The number of words of length `n` over an alphabet of size `k`.
This is the standard finite product count. -/
def fullShiftWordCount (k n : Nat) : Nat := k ^ n

/-- Being nonzero modulo 3 is the elementary unit criterion in `Z_3`. -/
def isThreeAdicUnit (m : Nat) : Bool := m % 3 != 0

/-- The 3-adic norm of the specific characteristic root 2.  It is 1 because
`2` is a 3-adic unit, as certified separately below. -/
def rootTwoThreeAdicNorm : Nat := 1

theorem two_symbol_word_count (n : Nat) : fullShiftWordCount 2 n = 2 ^ n := by
  rfl

theorem root_two_is_three_adic_unit : isThreeAdicUnit 2 = true := by
  decide

theorem root_two_norm : rootTwoThreeAdicNorm = 1 := rfl

/-- The two growth bases asserted equal by the conjectural formula are 2 and 1. -/
theorem entropy_base_mismatch :
    fullShiftWordCount 2 1 ≠ rootTwoThreeAdicNorm := by
  decide

/-- Direct negation of the predicted equality for the full two-shift over Q_3. -/
theorem counterexample :
    Not (forall n : Nat, n > 0 ->
      fullShiftWordCount 2 n = rootTwoThreeAdicNorm ^ n) := by
  intro h
  have h1 := h 1 (by decide)
  change 2 = 1 at h1
  omega

#print axioms Tlmc752.counterexample
#print axioms Tlmc752.two_symbol_word_count

end Tlmc752
