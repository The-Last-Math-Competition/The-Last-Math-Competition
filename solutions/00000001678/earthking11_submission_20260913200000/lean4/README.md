# Lean 4 formalisation — disproof of conjecture `00000001678`

Core Lean only (`import Std`), no Mathlib, no `sorry`. The project pins
`lean-toolchain` to `leanprover/lean4:v4.33.1` and defines the library `Main` in
`lakefile.toml`.

## Build and audit

```sh
lake build
lake env lean Check.lean
```

`Check.lean` prints `#print axioms` for every theorem so a reviewer can confirm
the absence of `sorryAx` and of Mathlib dependencies.

## What is formalised

The witness is the path `P_4` on four vertices, with vertex type `Fin 4` and
edges `i—(i+1)`. Everything about it is computable, so every theorem is closed
by `decide`.

| Theorem | Statement | Role |
|:--------|:----------|:-----|
| `singleton_zero_forces` | `isZFS (single 0) = true` | `{v1}` is a zero forcing set (forces `1`, then `2`, then `3`) |
| `empty_not_zfs` | `isZFS (coloringOf 0) = false` | the empty colouring is not a zero forcing set |
| `zeroForcingNumber_P4` | `zeroForcingNumber = 1` | `Z(P_4) = 1`, minimum over all `16` colourings |
| `whole_path_is_path_cover` | `isPathCover (fun _ => 0) = true` | the whole path is one induced path cover |
| `pathCoverNumber_P4` | `pathCoverNumber = 1` | `P(P_4) = 1`, minimum over all `256` partitions |
| `diameter_P4` | `diameter = 3` | graph diameter, by BFS reachability |
| `diameter_P4_odd` | `isOdd diameter = true` | the diameter is odd |
| `matching_01_23` | `isPerfectMatching 5 = true` | mask `5` selects `{v1v2, v3v4}` |
| `P4_has_perfect_matching` | `hasPerfectMatching = true` | `P_4` has a perfect matching |
| `difference_P4` | `zMinusP = 0` | `Z(P_4) - P(P_4) = 0` |
| `difference_P4_ne_one` | `zMinusP ≠ 1` | the difference is not `1` |
| `P4_satisfies_rhsPredicate` | `rhsPredicate = true` | odd diameter and a perfect matching |
| `exactly_clause_false` | `rhsPredicate = true ∧ zMinusP ≠ 1` | `P_4` is in `R` but not in `D` |
| `conjecture_00000001678_refuted` | conjunction of the above | the collected refutation |

## Proof strategy

- **Zero forcing.** A colouring is a function `Fin 4 → Bool`. One step of the
  colour-change rule is `step c v = c v || V4.any (fun u => forcedBy c u v)`,
  where `forcedBy c u v` says `u` is black, adjacent to `v`, and every other
  neighbour of `u` is black. The closure is `step` iterated `4` times (each
  effective step colours a new vertex, and there are only four). The zero
  forcing number is the minimum `zfCard` over the `16` colourings whose closure
  is all black.
- **Path cover number.** Vertex sets are checked to induce a path via
  `isPathBlock` (nonempty, no repeats, induced degree `≤ 2`, and `|S|-1` induced
  edges — connectedness for an induced forest). Partitions are enumerated
  through all `4^4 = 256` functions `Fin 4 → Fin 4` encoded as base-4 digits;
  idempotent maps encode the partitions (the blocks are the fibres over the
  fixed points), and the path cover number is the least number of blocks of a
  path cover. This is exactly the minimum number of vertex-disjoint induced
  paths covering `V_4`.
- **Diameter.** `frontier s k` is the set of vertices reachable from `s` by a
  walk of exactly `k` steps; `graphDist` finds the first `k` with `t` in the
  frontier, and `diameter` is the maximum over all pairs. For `P_4` this is `3`.
- **Perfect matching.** The three edges are encoded by a bit mask `k : 0..7`;
  `isPerfectMatching k` checks that the selected endpoints number four and that
  each vertex occurs exactly once. Mask `5 = 0b101` gives `{v1v2, v3v4}`.

Because function types have no decidable equality in core Lean, colourings and
partitions are never compared as functions: they are only evaluated pointwise,
or compared through `List` images and Boolean evaluators.

## Scope note

The formalisation covers the concrete witness `P_4`, which suffices to refute
the `exactly` clause of the conjecture: `P_4` is an odd-diameter tree admitting a
perfect matching, yet its difference is `0`, so the asserted classification is
false. The general statement that `Z(T) = P(T)` for all trees (the AIM theorem)
and the infinite family `P_{2k}` are not formalised here; they are stated in
`main.tex` with a literature reference and corroborated by `reproduce.py`,
which checks every path `P_n` for `n ≤ 10` and every tree on up to `10` vertices.

## Environment

Lean 4.33.1, Lake, no Mathlib. `lake build` needs no cache download.
