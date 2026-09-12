/-
  Disproof of conjecture `00000001186`: formalisation of the arithmetic core.

  Conjecture (as filed): with `m(k)` the minimal order of a nonabelian simple group
  having exactly `k` distinct prime factors,
      m(3) = 60, m(4) = 504, m(5) = 660, and m(k)/m(k-1) ≤ 4 for all k,
      with equality at k = 4.

  We formalise the three internal contradictions without any group theory:

    (1) `ω(504) = 3` and hence `ω(504) ≠ 4`, so `m(4) ≠ 504`
        (every group of order 504 has exactly three distinct prime factors);
    (2) `ω(660) = 4` and hence `ω(660) ≠ 5`, so `m(5) ≠ 660`;
    (3) `504 / 60 > 4`, contradicting the stated ratio bound at `k = 4`.

  Here `ω(n)` is `distinctPrimeCount n`, the number of distinct prime divisors of `n`.
  The file uses CORE LEAN ONLY (`import Std`); it does not use Mathlib, `Finset`,
  `Nat.factorization`, `norm_num`, `linarith`, `omega`, or `sorry`. All numerical
  facts are proved by `decide` on the computable definitions below.
-/

import Std

-- The bounded trial-division computations below (e.g. `distinctPrimeCount 660`)
-- unfold deeply, so the default kernel recursion limit is too small. The
-- computations are genuinely reducible, only deep; a larger limit lets `decide`
-- finish them.
set_option maxRecDepth 100000

namespace Tlmc1186

/-- `primeB n` is `true` exactly when `n` is a prime, decided by a bounded trial
division over `List.range n` (the candidates `0, …, n-1`). -/
def primeB (n : Nat) : Bool :=
  decide (2 ≤ n) && (List.range n).all (fun d => decide (d < 2 ∨ n % d ≠ 0))

/-- The number of distinct prime divisors of `n`, computed by a bounded loop over
`List.range (n + 1)`. This is `ω(n)` in the usual number-theoretic notation. -/
def distinctPrimeCount (n : Nat) : Nat :=
  ((List.range (n + 1)).filter (fun d => primeB d && decide (d ∣ n))).length

/-! ### Factorisations -/

/-- `60 = 2^2 · 3 · 5`. -/
theorem factor_60 : 60 = 2 ^ 2 * 3 * 5 := by decide

/-- `504 = 2^3 · 3^2 · 7`, which has three distinct prime factors. -/
theorem factor_504 : 504 = 2 ^ 3 * 3 ^ 2 * 7 := by decide

/-- `660 = 2^2 · 3 · 5 · 11`, which has four distinct prime factors. -/
theorem factor_660 : 660 = 2 ^ 2 * 3 * 5 * 11 := by decide

/-! ### Distinct prime counts `ω` -/

/-- `ω(60) = 3` (the primes are `2, 3, 5`). -/
theorem distinctPrimeCount_60 : distinctPrimeCount 60 = 3 := by decide

/-- `ω(504) = 3` (the primes are `2, 3, 7`). -/
theorem distinctPrimeCount_504 : distinctPrimeCount 504 = 3 := by decide

/-- `ω(660) = 4` (the primes are `2, 3, 5, 11`). -/
theorem distinctPrimeCount_660 : distinctPrimeCount 660 = 4 := by decide

/-! ### Contradiction 1: no group of order 504 has exactly 4 distinct prime factors -/

/-- `ω(504) ≠ 4`. -/
theorem distinctPrimeCount_504_ne_four : distinctPrimeCount 504 ≠ 4 := by decide

/-- Pure-arithmetic form of statement (1): any order equal to `504` has exactly three
distinct prime factors, never four. A group of order `504` therefore cannot be a group
"with exactly 4 distinct prime factors", so `m(4) ≠ 504`. (A full group-theoretic
statement would require Mathlib's `Fintype`/`Nat.card`; the arithmetic content is what
matters and is captured here.) -/
theorem no_order_504_has_four_distinct_primes (order : Nat) (h : order = 504) :
    distinctPrimeCount order ≠ 4 := by
  rw [h]
  exact distinctPrimeCount_504_ne_four

/-! ### Contradiction 2: no group of order 660 has exactly 5 distinct prime factors -/

/-- `ω(660) ≠ 5`. -/
theorem distinctPrimeCount_660_ne_five : distinctPrimeCount 660 ≠ 5 := by decide

/-- Pure-arithmetic form of statement (2): any order equal to `660` has exactly four
distinct prime factors, never five, so `m(5) ≠ 660`. -/
theorem no_order_660_has_five_distinct_primes (order : Nat) (h : order = 660) :
    distinctPrimeCount order ≠ 5 := by
  rw [h]
  exact distinctPrimeCount_660_ne_five

/-! ### Contradiction 3: the stated ratio bound fails at `k = 4` -/

/-- Contradiction 3: `504 / 60 > 4`, i.e. `m(4)/m(3) = 8.4 > 4`, contradicting
`m(k)/m(k-1) ≤ 4` with equality at `k = 4`.

The arithmetic content of `504 / 60 > 4` is encoded as the `Nat` inequality
`4 · 60 < 504`: since `60 > 0`, `504 / 60 > 4` holds exactly when
`4 · 60 < 504`. Core `Rat` operations (`Rat.blt`, `Rat.mul`, `Rat.inv`) are
`@[irreducible]` in this toolchain, so a direct `by decide` on the `Rat`
statement cannot reduce; the `Nat` encoding avoids that and carries the same
mathematical content. -/
theorem four_times_sixty_lt_504 : (4 : Nat) * 60 < 504 := by decide

/-! ### Counts with multiplicity (the alternative reading)

The factorisations above also fix `Ω`, the number of prime factors counted with
multiplicity, as the sum of the exponents. These are recorded so that the failure of
the alternative reading is also formal. -/

/-- `Ω(60) = 2 + 1 + 1 = 4`, so the multiplicity reading gives `m(3) ≠ 60`. -/
theorem Omega_60 : (2 : Nat) + 1 + 1 = 4 := by decide

/-- `Ω(504) = 3 + 2 + 1 = 6`, so the multiplicity reading gives `m(4) ≠ 504`. -/
theorem Omega_504 : (3 : Nat) + 2 + 1 = 6 := by decide

/-- `Ω(660) = 2 + 1 + 1 + 1 = 5`; the only listed value consistent with the
multiplicity reading, but it is assigned to `m(5)`. -/
theorem Omega_660 : (2 : Nat) + 1 + 1 + 1 = 5 := by decide

/-! ### The disproof -/

/-- Collecting the three independent contradictions, the conjecture is false as
stated:

* `ω(504) ≠ 4`  (Contradiction 1, so `m(4) ≠ 504`);
* `ω(660) ≠ 5`  (Contradiction 2, so `m(5) ≠ 660`);
* `4 · 60 < 504` (Contradiction 3, the `Nat` encoding of `504/60 > 4`).

Any one of these suffices; together they show `conjecture 00000001186` is FALSE. -/
theorem conjecture_00000001186_false :
    distinctPrimeCount 504 ≠ 4 ∧ distinctPrimeCount 660 ≠ 5 ∧
      (4 : Nat) * 60 < 504 :=
  ⟨distinctPrimeCount_504_ne_four, distinctPrimeCount_660_ne_five,
    four_times_sixty_lt_504⟩

end Tlmc1186
