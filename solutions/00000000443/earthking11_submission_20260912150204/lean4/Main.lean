/-
  Disproof of conjecture `00000000443`: formalisation of the arithmetic core.

  Conjecture (as filed), for the degree-`n` part `L_n` of the free Lie algebra on
  two generators:

      (I)  for all n ≥ 2,   dim L_n ≥ 2^(n-1) - 2^ceil(n/2);
      (II) for prime n, the gap between this bound and the exact value is exactly
           half of 2^((n-1)/2).

  The exact dimension is given by Witt's formula

      dim L_n = (1/n) * Σ_{d | n} μ(d) * 2^(n/d).

  We formalise two independent failures:

    (A) the inequality (I) fails at n = 4 and for every n in [4, 12]
        (`dim L_4 = 3 < 4 = 2^3 - 2^2`);
    (B) the gap identity (II) fails at n = 3, 7, 11.

  Here `mobius` is a hand-written Moebius function and `wittDim` implements the
  divisor sum above by a bounded loop over `List.range`. The file uses CORE LEAN
  ONLY (`import Std`); it does not use Mathlib, `Finset`, `Nat.Prime`,
  `Nat.factorization`, `norm_num`, `linarith`, `omega`, or `sorry`. All numerical
  facts are closed computations discharged by `decide` against the computable
  definitions below.
-/

import Std

namespace Tlmc443

/-! ### Computable number theory: primality, ω, square-freeness, μ -/

/-- `primeB n` is `true` exactly when `n` is prime, decided by bounded trial
division over the candidates `0, …, n-1` in `List.range n`. -/
def primeB (n : Nat) : Bool :=
  decide (2 ≤ n) && (List.range n).all (fun d => decide (d < 2) || decide (n % d ≠ 0))

/-- The number of distinct prime divisors of `n`, computed by a bounded loop over
`List.range (n + 1)`. This is `ω(n)` in the usual notation. -/
def distinctPrimeCount (n : Nat) : Nat :=
  ((List.range (n + 1)).filter (fun p => primeB p && decide (n % p = 0))).length

/-- `squarefreeB n` is `true` exactly when `n` is square-free, decided by checking
that no `d ≥ 2` up to `n` has `d * d` dividing `n`. -/
def squarefreeB (n : Nat) : Bool :=
  (List.range (n + 1)).all (fun d => decide (d < 2) || decide (n % (d * d) ≠ 0))

/-- The Moebius function `μ : Nat → Int`, implemented by hand:
`μ(n) = 0` if `n` is not square-free, and `(-1)^k` if `n` is a product of `k`
distinct primes (`μ(1) = 1`). -/
def mobius (n : Nat) : Int :=
  if squarefreeB n then
    (if distinctPrimeCount n % 2 = 0 then 1 else -1)
  else
    0

/-- The positive divisors of `n`, as a list, by a bounded loop over
`List.range (n + 1)`. -/
def divisors (n : Nat) : List Nat :=
  (List.range (n + 1)).filter (fun d => decide (1 ≤ d) && decide (n % d = 0))

/-- The Witt sum `Σ_{d | n} μ(d) * 2^(n/d)`, over the positive divisors `d` of `n`. -/
def wittSum (n : Nat) : Int :=
  (divisors n).foldl (fun acc d => acc + mobius d * (2 : Int) ^ (n / d)) 0

/-- Witt's formula for `k = 2`: `dim L_n = (1/n) * Σ_{d | n} μ(d) * 2^(n/d)`.
The sum is always divisible by `n`, so integer division is exact. -/
def wittDim (n : Nat) : Int :=
  wittSum n / (n : Int)

/-! ### The claimed bound and the claimed gap -/

/-- The conjectured bound `2^(n-1) - 2^ceil(n/2)`. Since `ceil(n/2) = (n+1)/2`
in `Nat` division, the bound is `2^(n-1) - 2^((n+1)/2)`. -/
def claimedBound (n : Nat) : Int :=
  (2 : Int) ^ (n - 1) - (2 : Int) ^ ((n + 1) / 2)

/-- The conjectured prime gap `(1/2) * 2^((n-1)/2)`. This is integral for odd `n`;
for even `n` the exponent `(n-1)/2` is truncated, so the definition is only used
below for odd arguments. -/
def claimedGap (n : Nat) : Int :=
  (2 : Int) ^ ((n - 1) / 2) / 2

/-- The actual magnitude of the gap between the claimed bound and the exact value. -/
def actualGap (n : Nat) : Int :=
  if wittDim n ≤ claimedBound n then claimedBound n - wittDim n
  else wittDim n - claimedBound n

/-! ### Moebius values -/

theorem mobius_one : mobius 1 = 1 := by decide
theorem mobius_two : mobius 2 = -1 := by decide
theorem mobius_three : mobius 3 = -1 := by decide
theorem mobius_four : mobius 4 = 0 := by decide
theorem mobius_six : mobius 6 = 1 := by decide
theorem mobius_twelve : mobius 12 = 0 := by decide

/-! ### Exact dimensions (Witt's formula) for `n = 1, …, 12` -/

theorem wittDim_one : wittDim 1 = 2 := by decide
theorem wittDim_two : wittDim 2 = 1 := by decide
theorem wittDim_three : wittDim 3 = 2 := by decide
theorem wittDim_four : wittDim 4 = 3 := by decide
theorem wittDim_five : wittDim 5 = 6 := by decide
theorem wittDim_six : wittDim 6 = 9 := by decide
theorem wittDim_seven : wittDim 7 = 18 := by decide
theorem wittDim_eight : wittDim 8 = 30 := by decide
theorem wittDim_nine : wittDim 9 = 56 := by decide
theorem wittDim_ten : wittDim 10 = 99 := by decide
theorem wittDim_eleven : wittDim 11 = 186 := by decide
theorem wittDim_twelve : wittDim 12 = 335 := by decide

/-! ### Failure (A): the inequality fails at `n = 4` and on `[4, 12]` -/

/-- `2^3 - 2^2 = 4`, which is the claimed bound at `n = 4`. -/
theorem bound_four : (2 ^ 3 : Int) - 2 ^ 2 = 4 := by decide

/-- `claimedBound 4 = 4`. -/
theorem claimedBound_four : claimedBound 4 = 4 := by decide

/-- The inequality fails at `n = 4`: `dim L_4 = 3 < 4 = 2^3 - 2^2`. -/
theorem inequality_fails_at_four : wittDim 4 < (2 ^ 3 : Int) - 2 ^ 2 := by decide

/-- The inequality fails at every `n` in `[4, 12]` (checked as a finite,
decidable conjunction of closed strict inequalities). -/
theorem inequality_fails_4_to_12 :
    wittDim 4 < claimedBound 4 ∧
    wittDim 5 < claimedBound 5 ∧
    wittDim 6 < claimedBound 6 ∧
    wittDim 7 < claimedBound 7 ∧
    wittDim 8 < claimedBound 8 ∧
    wittDim 9 < claimedBound 9 ∧
    wittDim 10 < claimedBound 10 ∧
    wittDim 11 < claimedBound 11 ∧
    wittDim 12 < claimedBound 12 := by
  decide

/-! ### Failure (B): the prime-gap identity fails -/

/-- Direct form of the failure at `n = 3`: `dim L_3 = 2`, the bound is
`2^2 - 2^2 = 0`, so the actual gap is `2`, whereas half of `2^((3-1)/2) = 2` is
`1`. Hence `2 ≠ 1`. -/
theorem gap_fails_at_three :
    wittDim 3 = 2 ∧ (2 ^ 2 : Int) - 2 ^ 2 = 0 ∧
      (2 : Int) ≠ (2 ^ ((3 - 1) / 2)) / 2 := by
  decide

/-- The actual gap at `n = 3` is `2`, not the claimed `1`. -/
theorem actualGap_three_ne : actualGap 3 ≠ claimedGap 3 := by decide

/-- The actual gap at `n = 7` is `30`, not the claimed `4`. -/
theorem gap_fails_at_seven : actualGap 7 ≠ claimedGap 7 := by decide

/-- The actual gap at `n = 11` is `774`, not the claimed `16`. -/
theorem gap_fails_at_eleven : actualGap 11 ≠ claimedGap 11 := by decide

/-- At `n = 5` the claimed formula happens to coincide with the actual gap:
`8 - 6 = 2 = (1/2) * 2^2`. This is recorded to stress that the claim, quantified
over all primes, is refuted by `3, 7, 11` despite this coincidence. -/
theorem gap_holds_at_five : actualGap 5 = claimedGap 5 := by decide

/-! ### The disproof -/

/-- Combining the two independent failures, conjecture `00000000443` is false as
stated:

* (A) `wittDim 4 < 2^3 - 2^2` (the universal inequality fails at `n = 4`);
* (B) the actual prime gaps at `3`, `7`, `11` differ from the claimed
  `(1/2) * 2^((p-1)/2)`.

Either failure alone falsifies the conjecture. -/
theorem conjecture_00000000443_false :
    wittDim 4 < (2 ^ 3 : Int) - 2 ^ 2 ∧
    wittDim 3 = 2 ∧
    actualGap 3 ≠ claimedGap 3 ∧
    actualGap 7 ≠ claimedGap 7 ∧
    actualGap 11 ≠ claimedGap 11 := by
  decide

end Tlmc443
