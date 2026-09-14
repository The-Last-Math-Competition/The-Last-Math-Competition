# Lean 4 formalisation — disproof of conjecture `00000001110`

Core Lean only (`import Std`), no Mathlib, no `sorry`, and **no
`native_decide`**. The project pins `lean-toolchain` to
`leanprover/lean4:v4.33.1` and defines the Lake project `tlmc1110` with library
`Main` in `lakefile.toml`.

## Build and audit

```sh
lake build
lake env lean Check.lean
```

`lake build` exits `0`. `Check.lean` prints `#print axioms` for every theorem.

## What is formalised, and what is not

The conjecture is about the number of reduced words of the longest element
`w_0` of a finite Coxeter group and its `h`-smoothness. Core Lean has no
Coxeter groups, so the development does **not** formalise the classical
bijection

```
reduced words of w_0 in S_n  <->  SYT of shape (n-1, ..., 1)
```

which is cited as a theorem. What *is* formalised is the arithmetic evaluation
of the hook-length formula for the staircase shape `(5,4,3,2,1)` (the type
`A_5` / `S_6` case, `h = 6`), together with the resulting divisibility and
smoothness facts. This is stated as a scope note, not hidden.

```lean
/-- Self-contained factorial: `Nat.factorial` is absent from `import Std`. -/
def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

/-- The 15 hook lengths of the staircase shape (5,4,3,2,1), row by row. -/
def hooks5 : List Nat := [9,7,5,3,1, 7,5,3,1, 5,3,1, 3,1, 1]

def hookProd5 : Nat := hooks5.prod

/-- #Red(w_0) in S_6, via `15! / prod(hooks)`. -/
def reducedWordsW0S6 : Nat := fact 15 / hookProd5

/-- `Bsmooth B c`: every divisor of `c` is at most `B` (B-smoothness). -/
def Bsmooth (B c : Nat) : Prop := ∀ p : Nat, p ∣ c → p ≤ B
```

| Theorem | Statement | Role |
|:--------|:----------|:-----|
| `fact_five`, `fact_fifteen` | `fact 5 = 120`, `fact 15 = 1307674368000` | the custom factorial on concrete inputs |
| `hooks5_length` | `hooks5.length = 15` | one hook per box |
| `hookProd5_closed` | `hookProd5 = 9 * 7^2 * 5^3 * 3^4` | bookkeeping form of the hook product |
| `hookProd5_value` | `hookProd5 = 4465125` | numerical hook product |
| `reducedWordsW0S6_eq` | `reducedWordsW0S6 = 292864` | **the hook-length evaluation** |
| `reducedWordsW0S6_factorisation` | `reducedWordsW0S6 = 2^11 * 11 * 13` | **full prime factorisation** |
| `eleven_dvd` | `11 ∣ reducedWordsW0S6` | the offending prime `11 > h = 6` |
| `thirteen_dvd` | `13 ∣ reducedWordsW0S6` | the offending prime `13 > h = 6` |
| `six_lt_eleven`, `six_lt_thirteen` | `6 < 11`, `6 < 13` | the comparisons against `h = 6` |
| `not_six_smooth` | `¬ Bsmooth 6 reducedWordsW0S6` | **the count is not `6`-smooth** |
| `two_primes_above_h` | `6 < 11 ∧ 11 ∣ c ∧ 6 < 13 ∧ 13 ∣ c` (`c = reducedWordsW0S6`) | both witnesses together |
| `conjecture_00000001110_false` | `¬ Bsmooth 6 reducedWordsW0S6 ∧ ∃ p, p ∣ c ∧ 6 < p` | **the packaged refutation** |

## Proof strategy and the avoidance of `native_decide`

The prior prototype at `/tmp/routeA.lean` computed the count by a bottom-up
order-ideal DP over an `Array` of 32768 masks and closed the numeral equality
with `native_decide`, which trusts the compiler and introduces the axiom
`Lean.ofReduceBool`. This submission avoids that:

- `fact` is defined by **structural recursion** on `Nat` (not by a loop), so
  the kernel unfolds `fact 15` directly.
- `hookProd5 = hooks5.prod` uses `List.prod`, also structurally recursive, so
  the kernel unfolds the product of the explicit 15-element list.
- `reducedWordsW0S6 := fact 15 / hookProd5` is therefore a closed `Nat`
  expression that the kernel reduces, and `reducedWordsW0S6_eq`,
  `reducedWordsW0S6_factorisation`, `hookProd5_closed`, `hookProd5_value` are
  all closed by plain `decide` (`set_option maxRecDepth 1000000` and
  `maxHeartbeats 2000000` are set for head-room; the kernel reductions are
  tiny).
- `11 ∣ reducedWordsW0S6` needs no `Decidable` instance for `∣` on `Nat`
  (there is none in core Lean): it is proved with the **explicit cofactor**,
  `⟨26624, by decide⟩`, i.e. by deciding the `Nat` equality
  `reducedWordsW0S6 = 11 * 26624`. Likewise `13 ∣ reducedWordsW0S6` uses
  cofactor `22528`.
- `not_six_smooth` unfolds `Bsmooth`, applies the hypothesis to `11`, and
  closes the resulting `11 ≤ 6` with a kernel `decide` (`¬ (11 ≤ 6)`), so no
  tactic beyond `decide`/term mode is needed.

No `native_decide` appears anywhere; the compiler is not trusted.

## Axiom audit

`lake env lean Check.lean` reports, verbatim:

```
'Tlmc1110.fact_five' does not depend on any axioms
'Tlmc1110.fact_fifteen' does not depend on any axioms
'Tlmc1110.hooks5_length' does not depend on any axioms
'Tlmc1110.hookProd5_closed' does not depend on any axioms
'Tlmc1110.hookProd5_value' does not depend on any axioms
'Tlmc1110.reducedWordsW0S6_eq' does not depend on any axioms
'Tlmc1110.reducedWordsW0S6_factorisation' does not depend on any axioms
'Tlmc1110.eleven_dvd' does not depend on any axioms
'Tlmc1110.thirteen_dvd' does not depend on any axioms
'Tlmc1110.six_lt_eleven' does not depend on any axioms
'Tlmc1110.six_lt_thirteen' does not depend on any axioms
'Tlmc1110.not_six_smooth' does not depend on any axioms
'Tlmc1110.two_primes_above_h' does not depend on any axioms
'Tlmc1110.conjecture_00000001110_false' does not depend on any axioms
```

Every theorem depends on **no axioms at all**. In particular there is no
`sorryAx`, no `Classical.choice`, and — the point of the exercise — no
`Lean.ofReduceBool`. `native_decide` was not needed.

## Scope note

- The statement refuted is: for type `A_5` (`S_6`, Coxeter number `h = 6`),
  `#Red(w_0)` is `h`-smooth. The formalisation proves
  `¬ Bsmooth 6 reducedWordsW0S6`, i.e. the count has a divisor exceeding `6`.
  The value `292864` is obtained from `15! / (9 * 7^2 * 5^3 * 3^4)`, which is
  the hook-length formula for the staircase shape `(5,4,3,2,1)`.
- The bijection `reduced words of w_0 in S_n <-> SYT of shape
  (n-1,...,1)` and the hook-length formula itself are **cited classical
  theorems, not formalised** (core Lean has no Coxeter groups). Consequently
  the Lean development certifies the arithmetic, while the identification of
  `#Red(w_0)` with `15! / prod(hooks)` is a mathematical input. This is also
  recorded in the top-level `README.md`.
- `11` and `13` are shown to *divide* the count; primality of `11` and `13`
  is not separately formalised (`Nat.Prime` is absent from `import Std`), and
  it is not needed: divisibility by a number greater than `6` alone negates
  `Bsmooth 6`.

## Environment

Lean 4.33.1, Lake, no Mathlib, no cache download required.
