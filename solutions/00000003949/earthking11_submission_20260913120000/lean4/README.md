# Lean 4 formalisation (core Lean + Std, no Mathlib)

Package `tlmc3949`, toolchain `leanprover/lean4:v4.33.1`.

## Build & audit

```sh
export PATH="$HOME/.elan/bin:$PATH"
cd lean4
lake build
lake env lean Check.lean
```

`lake build` must complete with exit code 0. `Check.lean` prints `#print axioms`
for each theorem; the expected output depends only on `propext` (a standard
Lean axiom used by `decide`) and contains neither `sorryAx` nor
`Lean.ofReduceBool`.

## Model

* A cell of the `4 × 4` grid is `Fin 4 × Fin 4` (`abbrev Cell`).
* `dist p q = absDiff p.1.val q.1.val + absDiff p.2.val q.2.val` is the
  Manhattan distance, using `Nat` subtraction on `.val`s.
* A set of cells is a 16-bit `Nat` bitmask; cell `(i,j)` is bit `i*4 + j`
  (`def bit`). `ballMask c r` is the bitmask of the closed ball `B(c,r)`
  (`List.foldr` over `allCells`), and `covers centres radii` folds the union of
  the balls and compares it with `full = 2^16 − 1`.
* `countTriples` counts the ordered centre triples with radii `2,1,0` covering
  the grid.

`Nat.sqrt` is opaque to the kernel reducer, so the closed form is computed by a
bounded `List.foldr` (`ceilSqrt`) that does reduce definitionally under
`decide`.

## Theorems

* `no_three_cover : countTriples = 0` — exhaustive `decide` over all 4096
  ordered triples with radii `2,1,0`.
* `four_cover_exists : ∃ c0 c1 c2 c3 : Cell, covers [c0,c1,c2,c3] [3,2,1,0] = true`
  — witness `(0,0)`, `(0,2)`, `(3,2)`, `(2,3)`.
* `conjecture_00000003949_false` — collects `formulaValue 4 = 3`,
  `countTriples = 0`, the existence of the 4-round cover, and `3 ≠ 4`.

## Notes / scope

The Lean development formalises the `n = 4` counterexample. The `n = 6`
statement (`b(P₆ □ P₆) ≥ 5`) is verified computationally in
`reproduce.py`; it is not formalised here because `decide` over the
`36⁴ ≈ 1.68·10⁶` quadruples would be prohibitively expensive for the kernel.
No `sorry`, no `axiom`, no `native_decide` is used anywhere.
