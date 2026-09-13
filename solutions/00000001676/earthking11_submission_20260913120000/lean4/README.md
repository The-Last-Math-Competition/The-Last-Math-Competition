# Lean formalisation (`tlmc1676`)

Core Lean 4 only (`import Std`), **no Mathlib**, no `sorry`, no `axiom`, no
`native_decide`. Toolchain: `leanprover/lean4:v4.33.1` (see `lean-toolchain`).

## Build

```sh
lake build            # builds library Main (default target)
lake env lean Check.lean   # prints #print axioms for every theorem
```

## Files

* `Main.lean` — the model and all theorems.
* `Check.lean` — `import Main` plus one `#print axioms` per theorem.

## Model

`C_3 □ C_3` is modelled on nine bits (mask `0..511`) representing the vertices
`Fin 3 × Fin 3`; vertices are adjacent when they differ in exactly one
coordinate, taken mod 3 (the torus wrap). There are 18 edges.

Because core Lean's `Nat.sqrt` (and `Nat.div`/`Nat.mod`) are not reliably
reducible by the kernel, all arithmetic uses structural recursion:

* `parityOf`, `halfOf`, `bitAt` — kernel-reducible bit extraction;
* `rangeFrom n start` — structural replacement for `List.range`;
* `popcountBits`, `edgeBoundary` (`!=` counts crossing edges);
* `minBoundaryOfSize k` — folds `min` over all 512 masks with `k` bits set;
* `ceilSqrt N` — bounded linear search (`find?`) for the least `s` with
  `N ≤ s*s`, replacing the opaque `Nat.sqrt`;
* `formula n m = ceilSqrt (16 * (n*m − m*m))`, i.e. `⌈4√(n·m − m²)⌉`.

`set_option maxRecDepth 100000` is required because the exhaustive `decide`
proofs reduce a 512-element list fold.

## Theorems

| Theorem | Statement |
| --- | --- |
| `minBoundaryOfSize_one` | `minBoundaryOfSize 1 = 4` |
| `minBoundaryOfSize_three` | `minBoundaryOfSize 3 = 6` |
| `formula_3_1` | `formula 3 1 = 6` |
| `formula_3_3` | `formula 3 3 = 0` |
| `mismatch_3_1` | `formula 3 1 ≠ minBoundaryOfSize 1` |
| `mismatch_3_3` | `formula 3 3 ≠ minBoundaryOfSize 3` |
| `radicand_negative_3_4` | `(3 : Int) * 4 − 4 * 4 < 0` |
| `conjecture_00000001676_false` | conjunction of the `(3,3)` mismatch and the `(3,4)` negative-radicand fact |

## Axiom audit

Running `lake env lean Check.lean` prints

```
'Tlmc1676.minBoundaryOfSize_one' does not depend on any axioms
'Tlmc1676.minBoundaryOfSize_three' does not depend on any axioms
'Tlmc1676.formula_3_1' does not depend on any axioms
'Tlmc1676.formula_3_3' does not depend on any axioms
'Tlmc1676.mismatch_3_1' does not depend on any axioms
'Tlmc1676.mismatch_3_3' does not depend on any axioms
'Tlmc1676.radicand_negative_3_4' does not depend on any axioms
'Tlmc1676.conjecture_00000001676_false' does not depend on any axioms
```

In particular there is no `sorryAx` and no `ofReduceBool`.
