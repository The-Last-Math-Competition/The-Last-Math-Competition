# Core-Lean formalisation for conjecture 00000001671

This directory contains a machine-checked refutation, in **core Lean 4 only**
(`import Std`), of the claim `b(K_n) = ⌈(n+3)/2⌉` for the basis number of the
complete graph. There is no Mathlib dependency, no `sorry`, no `axiom`, and no
`native_decide`.

## Toolchain and build

* `lean-toolchain`: `leanprover/lean4:v4.33.1`
* `lakefile.toml`: library target `Main`

```sh
lake build              # should print "Build completed successfully"
lake env lean Check.lean   # axiom audit
```

## Model

* An edge subset of `K_n` is a `Nat` bitmask over the `C(n,2)` edges listed in
  `edgesOf n` (only `n = 3, 4` are tabulated, which is all that is needed).
* Over `GF(2)` the cycle space of a connected graph is exactly the set of edge
  subsets in which every vertex has even degree; `isCycle n mask` tests this, and
  `cycleMasks n` enumerates all of them (including the empty set).
* `IsKFoldBasis n k basis` holds when `basis` consists of cycles, has exactly
  `cycleDim n = |E| − |V| + 1` elements, has `GF(2)` span equal to the whole
  cycle space (checked by enumerating the XOR-span via `spanContains`), and
  every edge occurs in at most `k` of its cycles.
* `minBasisNumber n` searches `subsetsOfSize (cycleMasks n) (cycleDim n)` for the
  least `k` admitting such a basis, returning the sentinel `cycleDim n + 1` if
  none is found.
* `formula n = (n+4)/2`, an integer rendering of `⌈(n+3)/2⌉`.

Everything is written as structural recursion so that the kernel can reduce
`by decide` proofs. Core `Nat.xor` is opaque to the kernel reducer and drags the
`propext` axiom into proofs, so bitwise XOR is re-implemented as `xorBits`
(a fold over bit positions). `set_option maxRecDepth 100000` accommodates the
nested folds.

## Theorems

| Theorem | Statement |
|---|---|
| `basis_three_is_one` | `minBasisNumber 3 = 1` |
| `basis_four_is_two` | `minBasisNumber 4 = 2` |
| `no_one_fold_four` | `hasKFoldBasis 4 1 = false` |
| `k3_basis_is_one_fold` | `IsKFoldBasis 3 1 [7] = true` (the triangle) |
| `k4_basis_is_two_fold` | `IsKFoldBasis 4 2 [11,21,38] = true` (three triangles) |
| `formula_three`, `formula_four` | `formula 3 = 3`, `formula 4 = 4` |
| `mismatch_three`, `mismatch_four` | `formula n ≠ minBasisNumber n` for `n = 3,4` |
| `conjecture_00000001671_false` | collects `b(K_3)=1`, `b(K_4)=2`, the formula values, and both mismatches |

The bitmasks for `K_4`: edges are indexed
`0:(0,1), 1:(0,2), 2:(0,3), 3:(1,2), 4:(1,3), 5:(2,3)`, so the triangles
`{0,1,2}, {0,1,3}, {0,2,3}` are `11 = 0b001011`, `21 = 0b010101`,
`38 = 0b100110`. For `K_3` the triangle is `7 = 0b111`.

## Axiom audit

`Check.lean` runs `#print axioms` on every theorem above. The expected (and
actual) output is that each one **does not depend on any axioms** — in
particular no `sorryAx` and no `ofReduceBool`.

## Scope

The Lean development verifies `K_3` and `K_4` (the two smallest counterexamples)
by kernel evaluation. `K_5` and `K_6` are verified by the exact `GF(2)` search
in `../reproduce.py`; a full kernel `decide` for those would require enumerating
subsets of a 63- respectively 1023-element cycle space and is not practical.
This is enough to refute the conjecture, which fails already at `n = 3`.
