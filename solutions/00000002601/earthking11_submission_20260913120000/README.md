# Disproof of conjecture 00000002601

**Verdict: FALSE.** The conjecture claims that the maximum number of fixed
points of a monotone self-map of an `n`-element finite lattice equals the
length of a maximal chain, is attained on distributive lattices, and drops
strictly on non-distributive lattices (the drop being the minimal number of
embedded `N₅` sublattices).

## Why it is false

The identity map is monotone (order-preserving) on every finite lattice and
fixes **all `n` elements**. Hence the maximum number of fixed points of a
monotone self-map is exactly `n`, the trivial upper bound — on every finite
lattice, distributive or not.

* On the 4-element distributive lattice `B₂ = {0, a, b, 1}`, the identity is
  monotone and fixes `4` elements, while a maximal chain `0 < a < 1` has only
  `3` elements (`2` edges). So `4 ≠ 3` (and `4 ≠ 2`), and the failure occurs on
  a **distributive** lattice, so the "attained on distributive lattices" rider
  does not help.
* Brute force: `B₂` has `36` monotone self-maps and maximum fixed-point count
  `4`; `B₃` (Boolean lattice on 3 atoms, `n = 8`) has `8000` monotone
  self-maps and maximum `8`, versus a maximal chain of `4` elements (`3`
  edges).
* Excluding the identity does not rescue it: on `B₃` a non-identity monotone
  map (send one coatom to the top, fix everything else) still fixes `7 > 4`;
  the computed maximum over non-identity monotone maps is `7`.
* On the non-distributive `N₅` the identity fixes all `5` elements, so the
  maximum is `5` — the same trivial value as on any 5-element lattice. The
  claimed strict drop on non-distributive lattices is therefore `0`, not
  positive; the conjectured quantity is blind to distributivity.

The "length of a maximal chain" is ambiguous between counting **elements**
(`k`) and counting **edges** (`k-1`). The refutation holds under **both**
readings.

## Contents

| Path | Description |
| --- | --- |
| `main.tex` | Standalone article with the identity argument, the `B₂`/`B₃` computations, the non-identity case, and the `N₅` remark. |
| `build/main.pdf` | Compiled article (`tectonic --outdir build main.tex`). |
| `reproduce.py` | Stdlib-only brute force: all `256` self-maps of `B₂`, backtracking enumeration of the `8000` monotone maps of `B₃`, all `3125` self-maps of `N₅`; prints max fixed points vs maximal chain length and PASS/FAIL. Exits `0`. |
| `lean4/` | Core Lean 4 formalization of the `B₂` refutation (no Mathlib, no `sorry`, no `axiom`, no `native_decide`). |

## Reproduce

```sh
python3 reproduce.py

export PATH="/opt/homebrew/bin:$PATH"
cd lean4 && lake build
lake env lean Check.lean

cd .. && tectonic --outdir build main.tex
```

## Lean formalization (`lean4/`)

Encodes `B₂ = Fin 4` with the order `x ≤ y ↔ x = y ∨ x = 0 ∨ y = 3`
(`0 = ⊥`, `1 = a`, `2 = b`, `3 = ⊤`; `a`, `b` incomparable). Main results:

* `identity_monotone : Monotone id`
* `identity_fixes_all : ∀ x : Fin 4, id x = x`
* `maxFixedPoints_eq_four : maxFixedPoints = 4` (exhaustive over all `4⁴ = 256` functions)
* `countMonotone_eq_36 : countMonotone = 36`
* `maxChainLen_eq_three : maxChainLen = 3`, `maxChainEdges_eq_two : maxChainLen - 1 = 2`
* `conjecture_00000002601_false : maxFixedPoints = 4 ∧ maxChainLen = 3 ∧ 4 > 3`
* `conjecture_00000002601_false_edges : maxFixedPoints = 4 ∧ maxChainLen - 1 = 2 ∧ 4 > 2`

All proofs use `decide`/`omega` only; `Check.lean` confirms no theorem depends
on `sorryAx` or `ofReduceBool` (only the standard core axioms `propext` and
`Quot.sound` appear).
