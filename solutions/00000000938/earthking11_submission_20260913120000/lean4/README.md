# Lean formalisation (`tlmc938`)

Core Lean 4 formalisation of the `n = 2` counterexample to conjecture
00000000938. Only `import Std` is used; there is no Mathlib dependency and no
`sorry` / `axiom` / `native_decide`. Core Lean has no real numbers, so the
statements live in `Int` / `Nat` and the arithmetic fact `1^2 != 2` stands in
for `1 != sqrt(2)` (as `sqrt(2)` is irrational).

## Toolchain

`lean-toolchain` pins `leanprover/lean4:v4.33.1`.

## What is proved (`Main.lean`, namespace `Tlmc938`)

* `max_abs_eq : ∀ a b : Int, max (|a+b|) (|a-b|) = |a| + |b|` — the key
  isometry identity, where `|·|` is `Int.natAbs` (a local notation is used
  because core Lean has no `Abs` class / `abs` notation for `Int`).
* `T : Int × Int → Int × Int`, `T x = (x.1 + x.2, x.1 - x.2)`.
* `T_isometry : ∀ x, max |(T x).1| |(T x).2| = |x.1| + |x.2|`.
* `maps_diamond_to_square` — the four diamond vertices `(±1,0), (0,±1)` map to
  the four square corners `(±1,±1)`, by `decide`.
* `one_sq_ne_two_nat : (1 : Nat) * 1 ≠ 2` and `one_sq_ne_two_int` — formal
  `1^2 != 2` (no `decide` on `Rat`).
* `conjecture_00000000938_false` — collects the above into one statement.

## Build

```sh
export PATH="/opt/homebrew/bin:$PATH"
lake build                 # must end with "Build completed successfully"
lake env lean Check.lean   # axiom audit
```

`lake build` compiles `Main`. `Check.lean` is a standalone audit script (not a
lake target) and is run with `lake env lean`.

## Expected axiom audit

```
'Tlmc938.max_abs_eq' depends on axioms: [propext, Quot.sound]
'Tlmc938.T_isometry' depends on axioms: [propext, Quot.sound]
'Tlmc938.maps_diamond_to_square' does not depend on any axioms
'Tlmc938.one_sq_ne_two_nat' does not depend on any axioms
'Tlmc938.one_sq_ne_two_int' does not depend on any axioms
'Tlmc938.conjecture_00000000938_false' depends on axioms: [propext, Quot.sound]
```

No `sorryAx`, no `Lean.ofReduceBool`.
