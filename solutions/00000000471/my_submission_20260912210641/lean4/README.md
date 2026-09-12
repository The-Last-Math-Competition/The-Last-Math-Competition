# Lean 4 formalisation for `00000000471`

**Core Lean only** — no Mathlib, no `sorry`, no axioms beyond `propext` and
`Quot.sound` (inherited from the standard treatment of lists).

Toolchain: `leanprover/lean4:v4.33.1` (see `lean-toolchain`).

## Build

```bash
lake build
lake env lean Check.lean
```

`lake env lean` takes one file at a time, so run `lake build` first; a bare
`lean Check.lean` will not find the `Main` module.

`lake build` takes roughly a minute. The `n = 5` theorem enumerates
`2^10 = 1024` subhypergraphs and runs a closure computation on each, which needs
more than the default heartbeat budget — `set_option maxHeartbeats 0` is set just
before it in `Main.lean`.

## What is in `Main.lean`

| section | contents |
|---|---|
| 1 | `edges n`: the edge set of `K_n^{(3)}` (strictly increasing triples, each 3-subset listed once). `sublists`: the powerset, i.e. all subhypergraphs. `sublists_length`: the powerset of an `m`-set has `2^m` elements. |
| 2 | `connected n es`: closure from vertex `0`, run for `n` rounds, must reach all `n` vertices. `minimalConnected n es`: connected, and deleting any one edge disconnects. `hypertrees n`: the filter of the powerset by `minimalConnected`. |
| 3 | `formula n`: the conjectured `n^{C(n-1,2)-1} * prod_{i=1}^{n-1} (i^2 - i + 1)`. |
| 4 | **Refutation I (counting bound).** `filter_length_le` and `hypertrees_le_subhypergraphs`: `t(K_n^{(3)}) ≤ 2^{C(n,3)}`. `refutation_bound_3`: `formula 3 > (hypertrees 3).length`. `refutation_bound_6`: `formula 6 > 2^{20}`. |
| 5 | **Refutation II (exact enumeration).** `hypertrees3_length = 1`, `hypertrees4_length = 6`, `hypertrees5_length = 25`, each by `rfl`, and `refutation_exact_3/4/5`. |

## Axiom audit

From `lake env lean Check.lean`:

| theorem | axioms |
|---|---|
| `hypertrees3_length`, `hypertrees4_length`, `hypertrees5_length` | **none** |
| `refutation_exact_3`, `refutation_exact_4`, `refutation_exact_5` | **none** |
| `filter_length_le`, `hypertrees_le_subhypergraphs` | `propext` |
| `sublists_length`, `refutation_bound_3`, `refutation_bound_6` | `propext`, `Quot.sound` |

The enumeration theorems are `rfl` proofs, not `native_decide`: the kernel
itself performs the search, so no additional axiom (such as `Lean.ofReduceBool`)
is introduced.

## Note on scope

The formalisation covers the two refutations and the exact values for
`n = 3, 4, 5`. It does **not** attempt to determine `t(K_n^{(3)})` in general,
and it makes no claim about `r ≠ 3`.
