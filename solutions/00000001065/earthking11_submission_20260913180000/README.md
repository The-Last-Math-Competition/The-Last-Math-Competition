# Submission for Conjecture 00000001065 — verdict: FALSE

**Claim (as stated in `/Users/lidazuo/Documents/dev/aimath/repo/conjectures/00000001065.md`).**
In the affine plane over the finite field with `q` elements, the minimal size
of a Nikodym set exceeds the minimal size of a Kakeya set by exactly `q - 1`.

**Verdict.** FALSE. Under the definitions recorded in the conjecture itself the
difference is `-1` at `q = 2`, `-2` at `q = 3`, and `0` at `q = 4`; it is never
`q - 1`.

## Definitions used

* A **Kakeya set** `K ⊆ F_q^2` contains a full line in every one of the `q + 1`
  directions.
* A **Nikodym set** `N ⊆ F_q^2` is a subset such that through every point
  `p ∈ F_q^2` there is a line `L` with `p ∈ L` and `L \ {p} ⊆ N`; that is, all
  *other* points of `L` lie in `N`, while `p` itself may be exceptional. The
  quantifier ranges over **all** points of the plane, including points outside
  `N`.

These are exactly the definitions in the conjecture ("a Nikodym set: through
each point, a line almost all of whose points lie in the set").

## Results (exhaustive search)

| q | min Kakeya | min Nikodym | difference | claimed q-1 | verdict |
|---|-----------|-------------|------------|-------------|---------|
| 2 | 3 | 2 | **-1** | 1 | differs |
| 3 | 7 | 5 | **-2** | 2 | differs |
| 4 | 10 | 10 | **0** | 3 | differs |

For `q = 2` all `16` subsets were checked; for `q = 3` all `512`; for `q = 4`
all `65 536`, using `GF(4)` arithmetic with the irreducible polynomial
`x^2 + x + 1`.

**Sanity check.** The computed Kakeya minima `3, 7, 10` match the known formula
`q(q+1)/2` for even `q` and `q(q+1)/2 + (q-1)/2` for odd `q`. This validates
the search independently of the Nikodym computation.

**Smallest witness (`q = 2`).** The two-point set `{(0,0),(0,1)}` is Nikodym:
for `(0,0)` and `(0,1)` the vertical line through them works; for `(1,0)` the
diagonal line to `(0,1)` works; for `(1,1)` the horizontal line to `(0,1)`
works. Meanwhile every Kakeya set needs at least `3` points, and
`{(0,0),(0,1),(1,0)}` is Kakeya. Hence min Nikodym `= 2`, min Kakeya `= 3`,
difference `= -1`, while `q - 1 = 1`.

## Strongest objection, stated honestly

If "almost all" is strengthened to "a **whole** line through every point",
then any point `p ∉ N` lies on its own required line, forcing `N = F_q^2` and
`min = q^2`. The quantity `q^2 - minKakeya` then coincidentally equals `q - 1`
at `q = 2` (`4 - 3 = 1`) and `q = 3` (`9 - 7 = 2`) — which may be where the
formula came from — but it already fails at `q = 4`
(`16 - 10 = 6 ≠ 3`). Under the stated "almost all" wording the refutation
stands, and it does so already at `q = 2`.

## Contents

* `main.tex` — standalone article with the definitions, the `q = 2` and `q = 3`
  computations, the full results table, the sanity checks, and the
  "whole line" discussion. Builds to `build/main.pdf` with
  `tectonic --outdir build main.tex`.
* `reproduce.py` — stdlib-only exhaustive search for `q = 2, 3, 4`; prints the
  table against `q - 1`, the sanity check, and `PASS`/`FAIL` verdicts; exits 0.
* `lean4/` — core-Lean machine-checked formalisation of the decisive `q = 2`
  case (`import Std` only, no Mathlib, no `sorry`, no `axiom`, no
  `native_decide`).
  * `Main.lean` — definitions and theorems.
  * `Check.lean` — `#print axioms` audit.
  * `lean-toolchain` — `leanprover/lean4:v4.33.1`.
  * `lakefile.toml`, `README.md`.

## Reproduction

```bash
python3 reproduce.py

cd lean4
export PATH="/opt/homebrew/bin:$PATH"
lake build
lake env lean Check.lean

cd ..
tectonic --outdir build main.tex
```
