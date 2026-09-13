# Refutation of conjecture 00000001676

**Verdict: FALSE.**

Conjecture: the isoperimetric profile of the `n × n` torus grid
`C_n □ C_n` is `ip(m) = ⌈4√(n·m − m²)⌉` for all `m ≤ n²/2`.

Two independent defects:

1. **Ill-posed on part of its stated range.** The radicand is
   `n·m − m² = m(n − m)`, which is negative whenever `m > n`. Such `m` lie in
   the stated range: for `n = 3`, `m = 4` gives `12 − 16 = −4 < 0` although
   `4 ≤ n²/2 = 4.5`. So the formula is not even real there.
2. **Wrong wherever it is defined.** Exhaustive search over all `m`-vertex
   subsets confirms mismatches, e.g. for `n = 3`: `m = 1` true `4` vs formula
   `6`; `m = 3` true `6` vs formula `0`. For `n = 4`: `m = 1` true `4` vs
   formula `7`; `m = 4` true `8` vs formula `0`.

**Cleanest counterexample:** `n = m = 3`. The formula gives
`⌈4√(9 − 9)⌉ = 0`, while the true minimum edge boundary is `6` (a full row of
the torus). The `n = 3, m = 4` case is outside the reals entirely.

## Contents

| Path | Description |
| --- | --- |
| `main.tex` | Standalone article with definitions, brute-force tables, the counterexample, and the ill-posedness argument. Build with `tectonic --outdir build main.tex`. |
| `reproduce.py` | Stdlib-only brute force of the true minimum edge boundary for `n = 3, 4` over the whole stated range; prints true-vs-formula tables, flags negative radicands, prints `PASS`/`FAIL`, exits `0`. |
| `lean4/` | Core-Lean (no Mathlib) machine-checked formalisation. |

## Reproduce

```sh
python3 reproduce.py          # brute force, PASS/FAIL
cd lean4 && lake build        # builds the formalisation
lake env lean Check.lean      # prints the axiom audit
tectonic --outdir build ../main.tex   # or from the submission root
```

## Lean formalisation

`lean4/Main.lean` models `C_3 □ C_3` on the nine bit positions of a 9-bit
`Nat` mask, defines `edgeBoundary` over the 18 torus edges, and computes
`minBoundaryOfSize k` by folding over all `2^9 = 512` masks. It proves, by
kernel `decide` (no `sorry`, no `axiom`, no `native_decide`):

* `minBoundaryOfSize 1 = 4` and `minBoundaryOfSize 3 = 6`;
* `formula 3 3 = 0` and `formula 3 3 ≠ minBoundaryOfSize 3` (the counterexample);
* `(3 : Int) * 4 − 4 * 4 < 0` (the negative-radicand/ill-posedness fact);
* `conjecture_00000001676_false`, collecting the `(3,3)` mismatch and the
  `(3,4)` negative radicand.

`formula (n m)` encodes `⌈4√(n·m − m²)⌉` as `ceilSqrt (16·(n·m − m²))`
(a computable bounded-search `ceilSqrt`, since core `Nat.sqrt` is opaque to the
kernel reducer). See `lean4/README.md`.
