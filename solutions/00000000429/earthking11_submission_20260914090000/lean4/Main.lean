/-
  Disproof of conjecture `00000000429`.

  Conjecture (as filed):
    Definition: the q-binomial [n choose k]_q at q = 1 counts binomial
    coefficients.
    Conjecture: its value at q = -1 is of the explicit form 2^{v(n,k)}
    (v a 2-adic valuation formula, giving a complete signed version).

  The conjecture is FALSE.  Reading the filed text literally, it predicates the
  form of the VALUE itself: the value of [n choose k]_q at q = -1 should be a
  power of two 2^{v(n,k)}.  The parenthetical phrase "giving a complete signed
  version" only invites the weaker reading value = ± 2^{v(n,k)}.

  Decisive witness:  [6 choose 2]_{q=-1} = 3, and 3 is neither 2^t nor -2^t for
  any integer t.  Further witnesses: [7 choose 3]_{q=-1} = 3,
  [8 choose 4]_{q=-1} = 6, [10 choose 2]_{q=-1} = 5.  The smallest interior
  entry that is not a signed power of two is 3 = [6 choose 2]_{-1}.

  The correct description is the q-Lucas rule at d = 2:
      [n choose k]_{q=-1} = C(floor(n/2), floor(k/2))   if NOT (n even, k odd),
      [n choose k]_{q=-1} = 0                            if n even and k odd.
  The common claim "equals C(floor(n/2), floor(k/2)) when C(n,k) is odd, else 0"
  is FALSE.

  `qb n k` below is the q-binomial coefficient at q = -1, computed by the
  integer Pascal recursion (structural, so `decide` can evaluate it; there is no
  division and no `Rat`).

  Core Lean only (`import Std`), no Mathlib, no `sorry`.
-/

import Std

namespace Tlmc429

/-- The q-binomial coefficient `[n choose k]_q` evaluated at `q = -1`, by the
integer Pascal recursion
```
[n choose k]_{-1} = [n-1 choose k-1]_{-1} + (-1)^k [n-1 choose k]_{-1}
```
with `[n choose 0] = 1` and `[0 choose k+1] = 0`.  No division, no `Rat`: this
is the exact integer value, computed by structural recursion on `n`. -/
def qb : Nat → Nat → Int
  | _, 0 => 1
  | 0, _+1 => 0
  | n+1, k+1 => qb n k + (-1 : Int)^(k+1) * qb n (k+1)

/-! ## Concrete values -/

/-- `[6 choose 2]_{-1} = 3`.  This is the decisive witness: `3` is not `2^t`
for any integer `t`. -/
theorem qb_6_2 : qb 6 2 = 3 := by decide

/-- `[8 choose 4]_{-1} = 6`.  A further witness (and a counterexample to the
incorrect "parity of `C(n,k)`" rule, which would predict `0`). -/
theorem qb_8_4 : qb 8 4 = 6 := by decide

/-- `[7 choose 3]_{-1} = 3`. -/
theorem qb_7_3 : qb 7 3 = 3 := by decide

/-- `[10 choose 2]_{-1} = 5`. -/
theorem qb_10_2 : qb 10 2 = 5 := by decide

/-- `[2 choose 1]_{-1} = 0`, the smallest interior zero. -/
theorem qb_2_1 : qb 2 1 = 0 := by decide

/-! ## `3` is not a signed power of two -/

/-- `2^t ≠ 3` for every natural `t`. -/
theorem pow2_ne_three : ∀ t : Nat, (2 : Int)^t ≠ 3 := by
  intro t
  induction t with
  | zero => decide
  | succ t ih =>
      rw [Int.pow_succ]
      omega

/-- `-2^t ≠ 3` for every natural `t`, since `2^t > 0`. -/
theorem negpow2_ne_three : ∀ t : Nat, -((2 : Int)^t) ≠ 3 := by
  intro t
  have h : (0 : Int) < (2 : Int)^t := Int.pow_pos (by decide)
  omega

/-- `6` is a signed power of two, unlike `3`.  Recorded so that the witness
`[8 choose 4] = 6` is not misused as a signed-power-of-two counterexample. -/
theorem six_eq_two_mul_three : (6 : Int) = 3 * 2 := by decide

/-! ## The conjecture fails -/

/-- **Unsigned failure.**  It is not the case that every value `[n choose k]_{-1}`
is a power of two `2^t`: the witness `[6 choose 2]_{-1} = 3` is not. -/
theorem not_pow2_unsigned :
    ¬ (∀ n k : Nat, ∃ t : Nat, qb n k = (2 : Int)^t) := by
  intro h
  obtain ⟨t, ht⟩ := h 6 2
  rw [qb_6_2] at ht
  exact pow2_ne_three t ht.symm

/-- **Signed failure.**  Even the weaker reading `value = ± 2^{v(n,k)}` fails:
`[6 choose 2]_{-1} = 3` is neither `2^t` nor `-2^t`. -/
theorem not_pow2_signed :
    ¬ (∀ n k : Nat, ∃ t : Nat,
        qb n k = (2 : Int)^t ∨ qb n k = -((2 : Int)^t)) := by
  intro h
  obtain ⟨t, ht⟩ := h 6 2
  rw [qb_6_2] at ht
  rcases ht with h1 | h2
  · exact pow2_ne_three t h1.symm
  · exact negpow2_ne_three t h2.symm

/-- The conjecture, stated for a generic candidate "valuation formula"
`v : Nat → Nat → Nat` (its values are interpreted as exponents, so the
conjectured value is `2^(v n k)`): there is a `v` making every value a power of
two.  This is exactly the unsigned reading, and it is false. -/
theorem conjecture_00000000429_false :
    ¬ (∃ v : Nat → Nat → Nat, ∀ n k : Nat, qb n k = (2 : Int)^(v n k)) := by
  intro h
  obtain ⟨v, hv⟩ := h
  exact not_pow2_unsigned fun n k => ⟨v n k, hv n k⟩

/-- Signed variant of the conjecture: there is a `v` and a sign choice making
every value `±2^(v n k)`.  Also false. -/
theorem conjecture_00000000429_false_signed :
    ¬ (∃ v : Nat → Nat → Nat, ∀ n k : Nat,
        qb n k = (2 : Int)^(v n k) ∨ qb n k = -((2 : Int)^(v n k))) := by
  intro h
  obtain ⟨v, hv⟩ := h
  exact not_pow2_signed fun n k => ⟨v n k, hv n k⟩

end Tlmc429
