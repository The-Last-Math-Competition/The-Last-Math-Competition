# lean4 — core Lean 4 formalization of the `B₂` refutation

Toolchain: `leanprover/lean4:v4.33.1` (see `lean-toolchain`). Core Lean only:
`import Std`, **no Mathlib**, no `sorry`, no `axiom`, no `native_decide`.

## Build and check

```sh
export PATH="/opt/homebrew/bin:$PATH"
lake build          # builds the Main library
lake env lean Check.lean   # prints #print axioms for every theorem
```

## Encoding

`B₂ = {⊥, a, b, ⊤}` is encoded as `Fin 4` with `0 = ⊥`, `1 = a`, `2 = b`,
`3 = ⊤`. The order (`Main.lean`, `Tlmc2601.le`) is

```lean
def le (x y : Fin 4) : Prop := x = y ∨ x = 0 ∨ y = 3
```

so `0` is bottom, `3` is top, and `1, 2` are incomparable. Monotonicity is

```lean
def Monotone (f : Fin 4 → Fin 4) : Prop := ∀ x y, le x y → le (f x) (f y)
```

## Results

* `identity_monotone : Monotone id`
* `identity_fixes_all : ∀ x : Fin 4, id x = x`
* `identity_fixed_count : fixedCount id = 4`
* `maxFixedPoints_eq_four : maxFixedPoints = 4` — exhaustive search over all
  `4 ^ 4 = 256` self-maps, keeping the monotone ones and maximizing the number
  of fixed points.
* `countMonotone_eq_36 : countMonotone = 36` — `B₂` has `36` monotone
  self-maps.
* `maxChainLen_eq_three : maxChainLen = 3` — longest chain has `3` elements.
* `maxChainEdges_eq_two : maxChainLen - 1 = 2` — `2` edges.
* `conjecture_00000002601_false` — `maxFixedPoints = 4 ∧ maxChainLen = 3 ∧ 4 > 3`.
* `conjecture_00000002601_false_edges` — the same under the edge reading.

## Axioms

`Check.lean` reports that none of the theorems depends on `sorryAx` or
`ofReduceBool`. A few depend on the standard core axioms `propext` and
`Quot.sound`, which is expected from `decide` over `Std` data and is not a
soundness concern.
