# Lean 4 formalisation — disproof of conjecture `00000008234`

Core Lean only (`import Std`), no Mathlib, no `sorry`. The project pins
`lean-toolchain` to `leanprover/lean4:v4.33.1` and defines the library `Main` in
`lakefile.toml`.

## Build and audit

```sh
lake build
lake env lean Check.lean
```

`Check.lean` prints `#print axioms` for every theorem so a reviewer can confirm
the absence of `sorryAx` and of Mathlib dependencies. The development uses only
`propext` and `Quot.sound` (the latter through `funext`).

## What is formalised

An allocation of `m` goods to `n` agents is a function `Fin m → Fin n` (each good
maps to its owner). Bundles are counted with `List.finRange`, which avoids
`Finset`. The EF1 predicate is transcribed literally from the definition:

```lean
def ef1 {n m : Nat} (a : Alloc n m) : Prop :=
  ∀ i j : Fin n, ¬ envy a i j ∨ ∃ g : Fin m, a g = j ∧ value a j - 1 ≤ value a i
```

where `value a i` is the unit additive valuation (= bundle cardinality) and
`envy a i j` means `value a i < value a j`. The computable predicate `isEF1`
(size gap `≤ 1`) is proved equivalent to `ef1` on the `2 × 2` instance by
`ef1_iff_bool`.

The swap graph has vertices = EF1 allocations and edges = single-good transfers,
i.e. Hamming distance `1` (`Adj a b := hamming a b = 1`). `ReachN a k b` is a
length-`k` walk that stays on EF1 vertices.

| Theorem | Statement | Role |
|:--------|:----------|:-----|
| `fin2_forall` | `(C 0) → (C 1) → ∀ g : Fin 2, C g` | case analysis on `Fin 2`, built from `Fin.cases` |
| `alloc_cases22` | every allocation is one of `alloc00, alloc01, alloc10, alloc11` | exhaustiveness, via `funext` |
| `value_alloc01`, `value_alloc10` | each agent holds exactly one good | unit valuations on the diagonals |
| `ef1_alloc01`, `ef1_alloc10` | the two diagonal allocations are EF1 | positive half of the classification |
| `not_ef1_alloc00`, `not_ef1_alloc11` | the two non-diagonal allocations are not EF1 | negative half |
| `ef1_classification` | every EF1 allocation is `alloc01` or `alloc10` | exactly two EF1 vertices |
| `ef1_iff_bool` | `ef1 a ↔ isEF1 a = true` | literal predicate agrees with the computable one |
| `exactly_two_ef1` | conjunction of the above plus `(allAllocs22.filter isEF1).length = 2` | exactly two EF1 allocations |
| `no_adj_ef1` | `ef1 a → ef1 b → ¬ Adj a b` | no edge joins two EF1 allocations |
| `reachN_eq` | `ef1 a → ReachN a k b → b = a` | every EF1 walk is trivial |
| `alloc01_ne_alloc10` | the two EF1 allocations differ | they are distinct vertices |
| `no_path_between_diagonals` | `¬ ∃ k, ReachN alloc01 k alloc10` | no path between them |
| `not_ef1_connected` | `¬ EF1Connected` | the swap graph is disconnected |
| `bound_value` | `2 * (2 - 1) = 2` | the conjectured bound at `n = m = 2` |
| `claimed_diameter_bound_fails` | `¬ SwapGraphDiameterAtMost 2` | the diameter bound fails |
| `conjecture_00000008234_refuted` | conjunction of the above | the collected disproof of the first conjunct |

## Proof strategy

- `alloc_cases22` is proved pointwise with `funext` on the values `a 0` and
  `a 1`, using `fin2_val_cases` (`Fin.cases`-based). Function equality is not
  decidable in core Lean, so no `decide` is applied to functions.
- `ef1_alloc01` / `ef1_alloc10`: `value` is `1` for both agents, so `envy` is
  `1 < 1`, which is false for every ordered pair; the first disjunct of `ef1`
  therefore always holds.
- `not_ef1_alloc00` / `not_ef1_alloc11`: the empty-handed agent envies the owner
  of both goods, and removing one good leaves value `1 > 0`, so neither
  disjunct of `ef1` holds.
- `no_adj_ef1`: classify both endpoints as the two diagonals; the remaining four
  cases are closed by `decide` on the concrete Hamming distances (`0` or `2`).
- `reachN_eq` is an induction on the walk length `Nat`; each step would need an
  edge between two EF1 vertices, which `no_adj_ef1` rules out. This is why
  `ReachN` is `Nat`-indexed: the induction on the index avoids dependent
  elimination problems, and the restriction to EF1 vertices is essential (the
  full Hamming graph on all four allocations *does* connect the two diagonals
  through `alloc00` and `alloc11`, which are not EF1).

## Scope note

The formalisation covers the `2 × 2` refutation, which is the smallest
counterexample and is sufficient to refute the first conjunct. The general
`n | m` family and the `3 × 3` instance are proved in the paper (`main.tex`) and
checked by exhaustive enumeration in `reproduce.py`; the Lean development keeps
to the `Fin 2 → Fin 2` case so that no `Fintype` (`Mathlib`) infrastructure is
needed.

## Environment

Lean 4.33.1, Lake, no Mathlib. `lake build` needs no cache download. The
`exploration/` subdirectory holds the minimal development scratch files; it is
not part of the library and is not built by `lake build`.
