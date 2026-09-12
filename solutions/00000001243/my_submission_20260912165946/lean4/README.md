# Lean 4 formalisation — status: COMPLETE

This project formalises the disproof of conjecture `00000001243` and **builds
with no `sorry`**, using **core Lean 4 only** (no Mathlib).

```bash
lake build          # Build completed successfully, no warnings
lake env lean Check.lean   # prints the axiom dependencies of every theorem
```

## Contents

| file | purpose |
|---|---|
| `Main.lean` | the formalisation |
| `Check.lean` | `#print axioms` for each theorem — the machine-checkable evidence |
| `lakefile.toml` | Lake configuration, no dependencies |
| `lean-toolchain` | pins `leanprover/lean4:v4.33.1` |

## What is formalised

```lean
def HasSquare (w : List Bool) : Prop :=
  ∃ s p : Nat, 0 < p ∧ s + 2 * p ≤ w.length ∧
    (w.drop s).take p = (w.drop (s + p)).take p
```

| theorem | statement |
|---|---|
| `binary_word_has_square` | every `w : List Bool` with `4 ≤ w.length` has a square |
| `no_square_free_binary_prefix` | for any `f : Nat → Bool` and `2 ≤ k`, `(List.range (2^k)).map f` has a square |
| `centralColumn` | the central column of rule 30, from a single `1` at position 0 |
| `central_column_starts_11` | its first two terms are `true, true` |
| `central_column_has_square` | the central column is not square-free |
| `SquareFreeOverPow2Prefixes` | the property the conjecture asserts |
| `conjecture_00000001243_false` | **no** binary sequence has that property |
| `rule30_central_column_refutes_conjecture` | the same, instantiated at the central column |

The main theorem is `conjecture_00000001243_false`, and it is deliberately
stated for an **arbitrary** `f : Nat → Bool` rather than for rule 30. That is
the mathematical content of the paper: the obstruction has nothing to do with
the dynamics of rule 30, because no binary sequence satisfies the property.

## Proof structure

`binary_word_has_square` is the four-case argument of Lemma 3.1 of the paper,
transcribed literally:

1. `w` shorter than 4 → contradiction with the hypothesis.
2. Otherwise `w = a :: b :: c :: d :: t`. Case split on `a = b`, then `b = c`,
   then `c = d`. The first three cases each give a square of period 1 at
   position 0, 1, 2.
3. In the remaining case all three adjacent pairs differ, so `c = a` and
   `d = b` (the alphabet has two letters); the square is `(a b)²` at position 0
   with period 2. The two auxiliary facts `c = a` and `d = b` are discharged by
   `cases` on the three `Bool`s followed by `simp_all`.

`centralColumn` is defined on an explicit row of width `2n+1` with the seed at
the centre. The width is chosen so the light cone (which spreads one cell per
step) never reaches the boundary within `n` steps, so the boundary condition
does not affect the recorded cells. The first two terms are then a closed
computation, discharged by `decide`.

## Axiom dependencies

```
binary_word_has_square                  : [propext]
no_square_free_binary_prefix            : [propext]
central_column_starts_11                : [propext]
central_column_has_square               : [propext]
conjecture_00000001243_false            : [propext]
rule30_central_column_refutes_conjecture: [propext]
```

Every theorem depends only on `propext`. In particular there is **no
`sorryAx`**, no `Classical.choice`, and no Mathlib axiom. `propext` is a
standard Lean axiom and appears here only through `List` and `Bool` library
lemmas.

To re-verify, run `lake env lean Check.lean`; the output is exactly the block
above.

## Notes for a reviewer

- **No Mathlib.** The project has no dependencies, so `lake build` needs no
  cache download and completes in well under a second. This also means there is
  nothing to trust beyond the Lean core library.
- **The `decide` uses are finite and checkable by hand.** The `decide` calls
  discharge only: `0 < 1`; the length bound `0 + 2·p ≤ length` for
  `p ∈ {1,2}`; the concrete word equality in each case; and the two closed
  computations on `centralColumn 32`. None of them hides a search.
- **`central_column_starts_11` is redundant** given `binary_word_has_square` —
  the latter already refutes the conjecture for every binary sequence. It is
  kept because it records the *specific* counterexample `11` at position 0 that
  the paper mentions, and because it independently exercises the `centralColumn`
  definition.

## Environment used

Lean 4.33.1 (arm64-apple-darwin), Lake 5.0.0, no Mathlib.
