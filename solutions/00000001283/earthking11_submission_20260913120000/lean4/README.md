# Lean formalisation (conjecture 00000001283)

Toolchain: `leanprover/lean4:v4.33.1` (see `lean-toolchain`).
Core Lean only: `import Std`, **no Mathlib**, no `sorry`, no `axiom`,
no `native_decide`.

## Build

```bash
export PATH="/opt/homebrew/bin:$PATH"
cd lean4
lake build                 # exit 0
lake env lean Check.lean   # axiom audit, no sorryAx / ofReduceBool
```

`lakefile.toml` declares a single library `Main` with `defaultTargets =
["Main"]`, so `lake build` checks `Main.lean`.  The audit file `Check.lean`
is deliberately kept out of the library target and is checked with
`lake env lean Check.lean`, which compiles it against the already-built
`Main.olean` (this is the same convention used by the other submissions in
this repository).

`Main.lean` sets `maxRecDepth` high because the two bounded-search proofs
reduce a `List` of length `200 * 200`; the default recursion depth is too
small for the `Decidable` instance of list equality.

## What is formalised

* `two_nim_two` : `(2 : Nat) ^^^ 2 = 0 ∧ (2 : Nat) * 2 = 4`, by `decide`.
* `not_a_solution` : `¬ ((2 : Nat) ^^^ 2 = 2 * 2)`, by `decide`.
  This refutes the first clause at the explicitly listed pair `(2,2)`
  (`^^^` is Lean's infix XOR on `Nat`).
* `pairsUpTo`, `solutionsUpTo`, `solutionsUpToPos` : computable enumeration
  of the pairs `(x, y)` in a box satisfying `x ⊕ y = x * y`.
* `only_zero_solution` : `solutionsUpTo 200 = [(0, 0)]`, by `decide`.
* `no_pos_solutions` : `solutionsUpToPos 200 = []`, by `decide` -- the
  computational counterpart of the mathematical theorem that there is no
  solution with `x, y ≥ 1`.
* `int_two_pow_cast` : `((2 ^ j : Nat) : Int) = (2 : Int) ^ j`
  (from `Int.natCast_pow`).
* `int_two_pow_pos` : `∀ j, (0 : Int) < (2 : Int) ^ j`.
* `int_two_pow_ne_nine` : `∀ j, (2 : Int) ^ j ≠ 9` (induction on `j`, using
  `Int.pow_succ` and `omega`).
* `nine_not_pow` : `¬ ∃ j, ((0 : Int) - 9 = (2 : Int) ^ j)`.
* `nine_not_pow_neg` : `¬ ∃ j, ((0 : Int) - 9 = -((2 : Int) ^ j))`.
* `clause2_fails_at_3_3` : `3 ⊕ 3 = 0`, `3 * 3 = 9`, and `-9` is neither
  `2^j` nor `-2^j`.
* `conjecture_00000001283_false` : the conjunction of the above: `(2,2)` is
  not a solution, the `x, y ≥ 1` solution set is empty, and the second clause
  fails at `(3,3)`.

## Axiom audit

`Check.lean` runs `#print axioms` for every theorem above.  The observed
output is:

```
'Tlmc1283.two_nim_two' depends on axioms: [propext]
'Tlmc1283.not_a_solution' depends on axioms: [propext]
'Tlmc1283.only_zero_solution' depends on axioms: [propext]
'Tlmc1283.no_pos_solutions' depends on axioms: [propext]
'Tlmc1283.int_two_pow_pos' depends on axioms: [propext]
'Tlmc1283.int_two_pow_ne_nine' depends on axioms: [propext, Quot.sound]
'Tlmc1283.nine_not_pow' depends on axioms: [propext, Quot.sound]
'Tlmc1283.nine_not_pow_neg' depends on axioms: [propext, Quot.sound]
'Tlmc1283.clause2_fails_at_3_3' depends on axioms: [propext, Quot.sound]
'Tlmc1283.conjecture_00000001283_false' depends on axioms: [propext, Quot.sound]
```

No `sorryAx`, no `Lean.ofReduceBool`, no custom axioms.

## What is NOT formalised in Lean

The general (unbounded) statement of Theorem 2 of `../main.tex` -- that no
`x, y ≥ 1` solve the equation for *all* sizes -- is proved on paper there
using the inequality `x ⊕ y ≤ x + y ≤ x · y`; in Lean it is witnessed by the
bounded search over `0 ≤ x, y < 200` together with the case analysis on
`x = 1`.  The unbounded universal statement is not encoded as a Lean theorem
here (it would need a general inequality argument that the bounded `decide`
checks do not provide).  The two concrete facts needed for the disproof --
the failure at `(2,2)` and the failure of the second clause at `(3,3)` -- are
fully formalised and are independent of that gap.
