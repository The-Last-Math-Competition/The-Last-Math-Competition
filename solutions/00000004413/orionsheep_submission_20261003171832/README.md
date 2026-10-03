# Refutation of Conjecture 00000004413

**Conjecture.** In every bounded-degree graph limit (graphing) of degree
bound `d`, the measure of `l`-cycles is at most `(d-1)^l / (2l)`, and this
bound is attained and optimal for the `d`-regular tree graph limit.

**Verdict: FALSE.**

## Why

Two independent failures:

1. **The upper bound fails.** The triangle `K₃`, viewed as a graphing on the
   uniform probability space `Fin 3`, has degree bound `d = 2` and contains
   exactly one undirected `3`-cycle, so its `3`-cycle measure is `1/3`
   (and its raw cycle count is `1`).  The claimed bound is
   `(2-1)³/(2·3) = 1/6 < 1/3`.  The bound fails on the simplest
   bounded-degree object.

2. **The attainment claim fails.** A `d`-regular tree has *no* cycles, so
   its `l`-cycle measure is `0`, whereas `(d-1)^l/(2l) > 0` for all
   `d ≥ 2`, `l ≥ 1`.  The bound is never attained by the `d`-regular tree;
   the conjecture's optimality clause is inconsistent with its own bound.

**Context.** `(d-1)^l/(2l)` is the mean of the Poisson limit for the number
of `l`-cycles in a uniformly random `d`-regular graph (Bollobás–Wormald) —
a *typical* value for locally-tree-like limits, not a universal upper bound.

## Lean 4 / Mathlib formalization (`lean4/`)

- `lean-toolchain`: `leanprover/lean4:v4.33.1`; `lakefile.toml` requires
  `mathlib4` at rev `v4.33.1`; `defaultTargets = ["Main"]`.
- `Main.lean` (namespace `Submission00000004413`) defines the objects for
  real:
  - `structure Graphing V`: symmetric, irreflexive, decidable edge relation
    `E` on a `Fintype V` (uniform measure);
  - `Graphing.deg`, `Graphing.DegreeBound`;
  - `Graphing.cycStep` (cyclic successor on `Fin n`, defined for all `n`);
  - `Graphing.IsCycleWalk` (oriented closed `n`-walks), `Graphing.cycleWalks`;
  - `Graphing.edgeSetOf` : `Fin n → V ↦ Finset (Sym2 V)` — unordered edge
    set traversed, so a cycle and all of its cyclic rotations/reversal give
    the *same* `Sym2` set; the image counts distinct undirected cycles;
  - `Graphing.cycleCount` (image card / `|V|`), `Graphing.claimedBound`
    `= (d-1)^l/(2l)`;
  - `triangle : Graphing (Fin 3)`.
- Theorems (no `sorry`, no `native_decide`):
  - `conjecture_00000004413_false` — the universal bound is false;
  - `counterexample_exists` — explicit witness `K₃`;
  - `triangle_degreeBound` (`d = 2`), `triangle_cycleCount_ge`
    (`≥ 1/3`), `claimedBound_2_3` (`= 1/6`);
  - `tree_cannot_attain` — `claimedBound > 0` for `d ≥ 2, l ≥ 1`, while a
    tree's cycle measure is `0`.
- `Check.lean` runs `#print axioms` on every theorem; all report only the
  three standard Lean axioms `propext`, `Classical.choice`, `Quot.sound`
  (the ambient mathlib foundation) — no `sorryAx`, no `ofReduceBool`.

## Reproduction

- `python3 reproduce.py` — brute-force check: `K₃` has `1` undirected
  `3`-cycle vs. bound `1/6`; trees have `0` cycles vs. positive bound.
- `cd lean4 && lake build` — exits `0`.
- `lake env lean Check.lean` — axiom audit.
- `tectonic main.tex --outdir build` — produces `build/main.pdf`.

## Files

```
README.md            this file
main.tex             write-up
build/main.pdf       compiled PDF
reproduce.py         numerical verification
lean4/Main.lean      formalization
lean4/Check.lean     #print axioms audit
lean4/lakefile.toml  mathlib v4.33.1 dependency
lean4/lean-toolchain leanprover/lean4:v4.33.1
lean4/.gitignore
```
