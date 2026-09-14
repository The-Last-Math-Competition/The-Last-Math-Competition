/-
  Disproof of conjecture `00000001110`.

  Conjecture (as filed, verbatim):
    "The prime factorization of the number of reduced words of the longest
     element w0 involves only primes <= h (smoothness of reduced-word
     counting)."

  The file names no `h` and no type scope.  Under the standard reading,
  `h` is the Coxeter number and the scope is all finite Coxeter groups.
  For the symmetric group S_n (type A_{n-1}) one has h = n.  We exhibit
  n = 6, i.e. type A_5 with h = 6, where the number of reduced words of
  the longest element w0 is

        292864 = 2^11 * 11 * 13,

  and the primes 11 and 13 both exceed h = 6.  This refutes the
  conjecture.

  The count is computed here through the classical hook-length formula:
  reduced words of w0 in S_n correspond to standard Young tableaux of the
  staircase shape (n-1, n-2, ..., 1), and for n = 6 (shape (5,4,3,2,1),
  15 boxes) the hook-length product is

        prod of hooks = 9 * 7^2 * 5^3 * 3^4 = 4465125,

  so the count is 15! / 4465125 = 1307674368000 / 4465125 = 292864.

  Core Lean only (`import Std`), no Mathlib, no `sorry`, and crucially no
  `native_decide`: every numeral equality below is closed by the kernel
  `decide`, so the axiom footprint contains no `Lean.ofReduceBool`.
-/

import Std

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

namespace Tlmc1110

/-! ## A self-contained factorial

`Nat.factorial` is not available under `import Std`, so we define our own by
structural recursion on `Nat`.  Being structurally recursive, it is unfolded
by the kernel, which is what lets plain `decide` close the computations
below (imperative loops would not be unfolded). -/

/-- Factorial, defined by structural recursion so that the kernel can reduce
concrete instances during `decide`. -/
def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

/-- Cross-check of the custom factorial against an explicit small literal. -/
theorem fact_five : fact 5 = 120 := by decide

theorem fact_fifteen : fact 15 = 1307674368000 := by decide

/-! ## The staircase shape (5,4,3,2,1) and its hook lengths

The staircase shape of type A_5 is the partition (5,4,3,2,1) of 15 = 10 + 5.
Its cells have hook lengths, read row by row,

    row 1: 9 7 5 3 1
    row 2: 7 5 3 1
    row 3: 5 3 1
    row 4: 3 1
    row 5: 1

We record them as an explicit list and take the product.  `List.prod` is
structurally recursive, so the kernel reduces it. -/

/-- The 15 hook lengths of the staircase shape (5,4,3,2,1), row by row. -/
def hooks5 : List Nat :=
  [9, 7, 5, 3, 1,   -- row 1, length 5
   7, 5, 3, 1,      -- row 2, length 4
   5, 3, 1,         -- row 3, length 3
   3, 1,            -- row 4, length 2
   1]               -- row 5, length 1

/-- The hook-length product `∏ h(i,j)` of the staircase shape (5,4,3,2,1). -/
def hookProd5 : Nat := hooks5.prod

/-- The hook product is a `Nat` of length 15, as it must be (one factor per
cell). -/
theorem hooks5_length : hooks5.length = 15 := by decide

/-- The hook-length product, computed by the kernel, equals the bookkeeping
form `9 · 7² · 5³ · 3⁴`. -/
theorem hookProd5_closed : hookProd5 = 9 * 7 ^ 2 * 5 ^ 3 * 3 ^ 4 := by decide

/-- Numerical value of the hook product. -/
theorem hookProd5_value : hookProd5 = 4465125 := by decide

/-! ## The number of reduced words of `w0` in S_6 -/

/-- The number of reduced words of the longest element `w0` of S_6, computed
by the hook-length formula for the staircase shape (5,4,3,2,1):

      `#Red(w0) = 15! / ∏ h(i,j)`.

The bijection `reduced words of w0 in S_n ↔ SYT of shape (n-1,…,1)` and the
hook-length formula are cited, not formalised: core Lean has no Coxeter
groups.  What is formalised is the arithmetic evaluation. -/
def reducedWordsW0S6 : Nat := fact 15 / hookProd5

/-- The hook-length evaluation: `15! / (9·7²·5³·3⁴) = 292864`.  This numeral
equality is closed by the kernel `decide` (no `native_decide`). -/
theorem reducedWordsW0S6_eq : reducedWordsW0S6 = 292864 := by decide

/-- The full prime factorisation of the count, again by kernel `decide`. -/
theorem reducedWordsW0S6_factorisation :
    reducedWordsW0S6 = 2 ^ 11 * 11 * 13 := by decide

/-! ## The two large primes divide the count -/

/-- `11` divides `2^11 · 11 · 13 = 292864`.  Stated with an explicit
cofactor `26624` so that only a `Nat` equality is decided (there is no
`Decidable` instance for `∣` on `Nat` in core Lean). -/
theorem eleven_dvd : 11 ∣ reducedWordsW0S6 := ⟨26624, by decide⟩

/-- `13` divides `292864`, with cofactor `22528`. -/
theorem thirteen_dvd : 13 ∣ reducedWordsW0S6 := ⟨22528, by decide⟩

theorem six_lt_eleven : 6 < 11 := by decide

theorem six_lt_thirteen : 6 < 13 := by decide

/-! ## Smoothness, and the refutation -/

/-- `Bsmooth B c` says every prime factor of `c` is at most `B`; equivalently
`c` is `B`-smooth.  Phrased over all divisors (not over primes) so that no
primality predicate is needed: this is the exact content when `B` is the
Coxeter number and `c` the reduced-word count. -/
def Bsmooth (B c : Nat) : Prop := ∀ p : Nat, p ∣ c → p ≤ B

/-- For type A_5 (S_6) the Coxeter number is `h = 6`.  The number of reduced
words of `w0` is *not* `6`-smooth: its divisor `11 > 6`. -/
theorem not_six_smooth : ¬ Bsmooth 6 reducedWordsW0S6 := by
  intro h
  exact (by decide : ¬ (11 ≤ 6)) (h 11 eleven_dvd)

/-- Same conclusion, exhibiting both offending prime factors `11` and `13`,
both strictly greater than `h = 6`. -/
theorem two_primes_above_h :
    6 < 11 ∧ 11 ∣ reducedWordsW0S6 ∧ 6 < 13 ∧ 13 ∣ reducedWordsW0S6 :=
  ⟨six_lt_eleven, eleven_dvd, six_lt_thirteen, thirteen_dvd⟩

/-- **The counterexample, packaged.**  In type A_5, with Coxeter number
`h = 6`, the number of reduced words of `w0` has a prime factor strictly
greater than `h`.  Hence the conjecture, read as "for every finite Coxeter
group the reduced-word count of `w0` is `h`-smooth", is FALSE. -/
theorem conjecture_00000001110_false :
    ¬ Bsmooth 6 reducedWordsW0S6 ∧
      (∃ p : Nat, p ∣ reducedWordsW0S6 ∧ 6 < p) :=
  ⟨not_six_smooth, ⟨11, eleven_dvd, six_lt_eleven⟩⟩

end Tlmc1110
