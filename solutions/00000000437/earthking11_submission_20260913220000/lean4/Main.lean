/-
  Disproof of conjecture `00000000437`: formalisation.

  Conjecture (as filed):

    The n-th graded dimension of the Lie-primitive space of the shuffle algebra
    Sh(V) for dim V = 2 is

        L_n = (1/n) * Σ_{d | n} μ(d) * 2^(n/d)            (Witt's formula),

    and its parity is determined explicitly by whether n is a power of 2.

  The Witt formula is a true classical theorem (L_n counts the binary Lyndon
  words / the aperiodic binary necklaces of length n, equivalently the monic
  irreducible polynomials of degree n over F_2).  Its first values are

    n        :  1  2  3  4  5  6   7   8   9  10   11   12
    L_n      :  2  1  2  3  6  9  18  30  56  99  186  335

  The PARITY CLAUSE is what is false.  The refutation is unconditional and is
  witnessed by two powers of two with different parities:

    * n = 1 and n = 2 are BOTH powers of two, yet
          L_1 = 2 is even  and  L_2 = 1 is odd.
      So parity is not a function of "n is a power of 2".

    * If one refuses to call 1 a power of two, the same conclusion follows from
      n = 2 and n = 8: both are powers of two, yet L_2 = 1 is odd while
      L_8 = 30 is even.

    * The "iff" reading also fails at n = 6: L_6 = 9 is odd, while 6 is not a
      power of two.

  The true repaired characterisation is

      write n = 2^a * m with m odd;
      L_n is odd  <=>  a ∈ {1, 2} and m is squarefree.

  This file is CORE LEAN ONLY (`import Std`): no Mathlib, no `Finset`, no
  `Nat.Prime` (which lives in Mathlib), and no `sorry`.  The Möbius function is
  computed from an ASCENDING smallest-prime-factor search; the finite closed
  facts are discharged by `decide` (never `native_decide`, which would add
  `Lean.ofReduceBool` to the axiom footprint).
-/

import Std

set_option maxRecDepth 1000000

namespace Tlmc437

/-! ## The smallest prime factor (ascending trial division)

`minFac N` returns the SMALLEST `p ≥ 2` that divides `N` (and satisfies
`p * p ≤ N`); if no such `p` exists it returns `N`, so `N` is `1` or prime.
The search is ASCENDING (p = 2, 3, 4, …).  This matters: a "largest divisor
`≤ √N`" search returns a composite (4 ∣ 20 and 4 ∣ 24, with 4 ≤ √20, √24),
which silently corrupts μ.  With the ascending routine, `minFac 20 = 2` and
`minFac 24 = 2` (see the theorems below), and `witt 24 = 698870`. -/

/-- Ascending trial division with fuel `k` and current candidate `p`. -/
def minFacAux (N : Nat) : Nat → Nat → Nat
  | 0, _ => N
  | k + 1, p =>
    if p * p > N then N
    else if N % p = 0 then p
    else minFacAux N k (p + 1)

/-- The smallest prime factor of `N` (or `N` itself if `N` is `1` or prime). -/
def minFac (N : Nat) : Nat := minFacAux N N 2

/-! ## The Möbius function -/

/-- Fuel-based Möbius function.  For `n ≥ 2` with smallest prime factor `p` and
cofactor `m = n / p`: if `p ∣ m` then `n` is not squarefree and `μ n = 0`,
otherwise `μ n = - μ m`. -/
def muF : Nat → Nat → Int
  | 0, _ => 0
  | _, 0 => 0
  | _, 1 => 1
  | fuel + 1, n + 2 =>
    let p := minFac (n + 2)
    let m := (n + 2) / p
    if 2 ≤ p ∧ m % p = 0 then 0 else -muF fuel m

/-- The Möbius function `μ : Nat → Int`. -/
def mu (n : Nat) : Int := muF n n

/-! ## Witt's formula -/

/-- The positive divisors of `n`, as a list. -/
def divisors (n : Nat) : List Nat :=
  (List.range (n + 1)).filter (fun d => decide (d ∣ n))

/-- The numerator `Σ_{d | n} μ(d) · 2^(n/d)` of Witt's formula. -/
def wittNum (n : Nat) : Int :=
  (divisors n).foldl (fun acc d => acc + mu d * (2 : Int) ^ (n / d)) 0

/-- Witt's formula `L_n = (1/n) · Σ_{d | n} μ(d) · 2^(n/d)`. -/
def witt (n : Nat) : Int := wittNum n / (n : Int)

/-- `isPow2 n` is true exactly when `n = 2^k` for some `k` (so `isPow2 1 = true`,
since `2^0 = 1`). -/
def isPow2 (n : Nat) : Bool :=
  (List.range (n + 1)).any (fun k => 2 ^ k == n)

/-! ## Sanity checks on the ascending smallest-prime-factor search

These four facts would be FALSE for a "largest divisor `≤ √N`" routine, which
returns `4` for both `20` and `24`. -/

theorem minFac_20 : minFac 20 = 2 := by decide

theorem minFac_24 : minFac 24 = 2 := by decide

theorem mu_12 : mu 12 = 0 := by decide

theorem mu_30 : mu 30 = -1 := by decide

/-! ## Values of `L_n` (Witt's formula) -/

theorem witt_1 : witt 1 = 2 := by decide

theorem witt_2 : witt 2 = 1 := by decide

theorem witt_6 : witt 6 = 9 := by decide

theorem witt_8 : witt 8 = 30 := by decide

/-- `L_24 = 698870`.  The corrupted `minFac` of the pitfall note would give
`698869`, so this theorem also certifies that the ascending search is in use. -/
theorem witt_24 : witt 24 = 698870 := by decide

/-! ## The parity facts

All four are closed terms and are discharged by `decide`; no `native_decide`,
hence no `Lean.ofReduceBool` in the axiom footprint. -/

theorem witt_1_even : witt 1 % 2 = 0 := by decide

theorem witt_2_odd : witt 2 % 2 = 1 := by decide

theorem witt_6_odd : witt 6 % 2 = 1 := by decide

theorem witt_8_even : witt 8 % 2 = 0 := by decide

/-! ## The power-of-two flags -/

theorem isPow2_1 : isPow2 1 = true := by decide

theorem isPow2_2 : isPow2 2 = true := by decide

theorem isPow2_6 : isPow2 6 = false := by decide

theorem isPow2_8 : isPow2 8 = true := by decide

/-! ## The refutation -/

/-- The sharpest witness: `1` and `2` are both powers of two, but the parities
of `L_1 = 2` and `L_2 = 1` differ.  Hence parity is NOT determined by "n is a
power of 2". -/
theorem witness_1_2_parity : witt 1 % 2 ≠ witt 2 % 2 := by decide

/-- The fallback witness, valid even if one declines to call `1` a power of two:
`2` and `8` are both powers of two, yet `L_2 = 1` is odd and `L_8 = 30` is
even. -/
theorem fallback_2_8_parity : witt 2 % 2 ≠ witt 8 % 2 := by decide

/-- The "iff" reading is violated at `n = 6`: `6` is not a power of two, yet
`L_6 = 9` is odd. -/
theorem iff_reading_fails : isPow2 6 = false ∧ witt 6 % 2 = 1 :=
  ⟨isPow2_6, witt_6_odd⟩

/-- The parity clause, read as "parity is a function of whether `n` is a power
of two", is false.  This is the precise negation of the functional reading of
the conjecture's parity clause. -/
theorem parity_not_determined_by_pow2 :
    ¬ (∀ n m : Nat, isPow2 n = isPow2 m → witt n % 2 = witt m % 2) := by
  intro h
  exact witness_1_2_parity (h 1 2 (by decide))

/-- Collected refutation of conjecture `00000000437`:

* `1` and `2` are both powers of two, but `L_1 = 2` is even and `L_2 = 1` is
  odd, so parity is not a function of "n is a power of 2";
* `2` and `8` are both powers of two with different parities (the fallback);
* `6` is not a power of two, yet `L_6 = 9` is odd (the "iff" reading fails).

Every conjunct is a closed computation, proved by `decide`. -/
theorem conjecture_00000000437_false :
    isPow2 1 = true ∧ isPow2 2 = true ∧
    witt 1 % 2 = 0 ∧ witt 2 % 2 = 1 ∧
    witt 1 % 2 ≠ witt 2 % 2 ∧
    isPow2 6 = false ∧ witt 6 % 2 = 1 ∧
    isPow2 8 = true ∧ witt 2 % 2 ≠ witt 8 % 2 :=
  ⟨isPow2_1, isPow2_2, witt_1_even, witt_2_odd, witness_1_2_parity,
   isPow2_6, witt_6_odd, isPow2_8, fallback_2_8_parity⟩

end Tlmc437
