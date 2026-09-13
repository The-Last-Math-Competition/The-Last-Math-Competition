# Lean 4 formalisation — disproof of conjecture `00000001192`

Core Lean only (`import Std`), no Mathlib, no `sorry`, no `axiom`, no
`native_decide`. The project pins `lean-toolchain` to
`leanprover/lean4:v4.33.1` and defines the library `Main` in `lakefile.toml`.

## Build and audit

```sh
lake build
lake env lean Check.lean
```

`Check.lean` prints `#print axioms` for every theorem so a reviewer can confirm
the absence of `sorryAx` and of `ofReduceBool` (the axiom introduced by
`native_decide`), and the absence of Mathlib.

## What is formalised

The conjecture is about `c(n,q)`, a subgroup count for `GL_n(F_q)`, plus the
claim that `c(n,q)` is an integer-coefficient polynomial of degree `n² − n`
with leading coefficient `LC(n) = (∏_{p|n} p)/(n! · n^n)`. The formalisation
captures the **arithmetic obstruction**: `LC(n)` is a non-integer rational, so
no integer-coefficient polynomial (whose leading coefficient is an integer) of
the stated degree can have it. It also rules out the weaker integer-valued
reading via the `d! · LC(n) ∉ ℤ` test at `n = 2, 3`.

Rationals are represented by the reduced pair `(lcNum n, lcDen n)`, so the whole
development stays over `Nat`/`Int` (core `Rat` operations are irreducible to
`decide`). Non-integrality is stated as the equivalent non-existence of an
integer solution, e.g. `¬ ∃ a : Int, 4 * a = 1` for `LC(2) = 1/4`.

## Definitions

| Definition | Meaning |
|:-----------|:--------|
| `isPrimeB n` | `Bool` primality test by bounded trial division over `List.range n`. |
| `prodPrimeDiv n` | `∏_{p|n} p`, filtering primes in `0..n` that divide `n`. |
| `factN n` | `n!` by structural recursion (core Lean has no `Nat.factorial`). |
| `gcdN a b` | computable gcd as the max common divisor in `0..min a b` (`Nat.gcd` is opaque to `decide`). |
| `lcGcd n` | `gcdN (prodPrimeDiv n) (factN n * n^n)`. |
| `lcNum n`, `lcDen n` | reduced numerator and denominator of `LC(n)`. |

## Theorems

| Theorem | Statement | Role |
|:--------|:----------|:-----|
| `prodPrimeDiv_two/three/four/six` | `2`, `3`, `2`, `6` | `∏_{p|n} p` at `n = 2,3,4,6` |
| `factN_two`, `factN_six` | `2! = 2`, `6! = 720` | factorial values used below |
| `lc_two` | `lcNum 2 = 1 ∧ lcDen 2 = 4` | `LC(2) = 1/4` |
| `lc_three` | `lcNum 3 = 1 ∧ lcDen 3 = 54` | `LC(3) = 1/54` |
| `lc_four` | `lcNum 4 = 1 ∧ lcDen 4 = 3072` | `LC(4) = 1/3072` |
| `lc_six` | `lcNum 6 = 1 ∧ lcDen 6 = 5598720` | `LC(6) = 1/5598720` |
| `lc_raw_two` | `∏_{p|2} p = 2 ∧ 2! · 2^2 = 8` | unreduced form `LC(2) = 2/8` |
| `lc2_not_integer` | `¬ ∃ m : Nat, m * 4 = 1` | `1/4 ∉ ℤ` (divisibility form) |
| `lc3_not_integer` | `¬ ∃ m : Nat, m * 54 = 1` | `1/54 ∉ ℤ` |
| `lc4_not_integer` | `¬ ∃ m : Nat, m * 3072 = 1` | `1/3072 ∉ ℤ` |
| `no_integer_poly_has_lc_two` | `¬ ∃ a : Int, 4 * a = 1` | integer-coefficient obstruction, `Int` form |
| `lc2_times_two_not_integer` | `¬ ∃ m : Nat, m * 2 = 1` | `2! · LC(2) = 1/2 ∉ ℤ` |
| `lc2_degree_factorial_times_lc_not_integer` | `¬ ∃ m : Nat, m * 4 = 2` | same, over the unreduced denominator |
| `lc3_degree_factorial_times_lc_not_integer` | `¬ ∃ m : Nat, m * 54 = 720` | `6! · LC(3) = 40/3 ∉ ℤ` |
| `lc3_degree_factorial_times_lc_not_integer_reduced` | `¬ ∃ m : Nat, m * 3 = 40` | reduced form of the same |
| `conjecture_00000001192_false` | conjunction of `lc_two`, `lc_three`, `lc_four` and the non-integrality facts | the collected disproof |

## Proof strategy

- All numerical facts are closed by `decide` on the computable definitions
  above; `set_option maxRecDepth 100000` is set to be safe.
- Because `Nat.factorial` is not in core and `Nat.gcd` does not reduce under
  `decide`, the development supplies `factN` (structural recursion) and `gcdN`
  (bounded list fold). Likewise `Nat.div`, `Nat.mod`, `List.range`, `List.filter`
  are kernel-reducible on numerals, which is all that is needed.
- The non-integrality facts are proved by converting the equation `m * b = 1`
  into a divisibility `b ∣ 1`, then closing `¬ (b ∣ 1)` by `decide`. For the
  `Int` statement, `Int.natAbs` sends `4 * a = 1` to `a.natAbs * 4 = 1`, which
  the `Nat` theorem `lc2_not_integer` refutes.
- `Rat` is deliberately not used: in this toolchain `Rat.mul`/`Rat.inv`/`Rat.blt`
  are irreducible, so `decide` cannot evaluate `(a : Rat) = 1/4`. The pair
  `(lcNum, lcDen)` together with divisibility statements carries exactly the same
  arithmetic content over `Nat`/`Int`.

## Scope note

The formalisation establishes that the *stated leading coefficient* `LC(n)` is
not an integer for `n = 2, 3, 4` (indeed for all `n ≥ 2`), and that the weaker
integer-valued reading fails at `n = 2` and `n = 3`. It therefore shows the
conjecture's two structural assertions are mutually inconsistent. The actual
subgroup count `c(n,q)` is not analysed; see the top-level `README.md` for the
honest scope discussion and the PORC caveat.

## Environment

Lean 4.33.1, Lake, no Mathlib. `lake build` needs no cache download and
completes in well under a second.
