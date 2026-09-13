import Mathlib

/-!
# A counterexample to conjecture 00000000013

Conjecture 00000000013 asserts that for every `n ≥ 3` the interval
`[2 ^ n, 2 ^ (n + 1))` contains a prime whose binary expansion has exactly
three `1`s. It fails at `n = 8`.

The `28` integers of `[2 ^ 8, 2 ^ 9)` with three binary ones are
`2 ^ 8 + 2 ^ a + 2 ^ b` for `0 ≤ b < a < 8`, and every one of them is
composite.

The conjecture is stated here in full, as `ConjectureHolds`, and
`conjecture_00000000013_false` refutes it; the digit condition is the honest
one, `(Nat.bits p).count true = 3`, rather than a parametrization assumed to
describe it, and primality is Mathlib's `Nat.Prime`.
-/

namespace Counterexample13

/-- Conjecture 00000000013. -/
def ConjectureHolds : Prop :=
  ∀ n, 3 ≤ n → ∃ p, 2 ^ n ≤ p ∧ p < 2 ^ (n + 1) ∧
    (Nat.bits p).count true = 3 ∧ Nat.Prime p

/-- There are exactly `28` candidates in the interval, as `Nat.choose 8 2 = 28`
predicts. -/
theorem card_candidates :
    ((Finset.Ico (2 ^ 8) (2 ^ 9)).filter
      (fun p => (Nat.bits p).count true = 3)).card = 28 := by
  decide

set_option maxRecDepth 10000 in
/-- No integer of `[2 ^ 8, 2 ^ 9)` with exactly three binary ones is prime.
Decided by exhausting the `256` integers of the interval. -/
theorem no_three_one_prime_at_eight :
    ∀ p < 2 ^ 9, 2 ^ 8 ≤ p → (Nat.bits p).count true = 3 → ¬ Nat.Prime p := by
  decide

/-- Conjecture 00000000013 is false. -/
theorem conjecture_00000000013_false : ¬ ConjectureHolds := by
  intro h
  obtain ⟨p, hlo, hhi, hbits, hp⟩ := h 8 (by norm_num)
  exact no_three_one_prime_at_eight p hhi hlo hbits hp

end Counterexample13
