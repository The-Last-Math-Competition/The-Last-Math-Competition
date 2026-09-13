# Disproof of conjecture 00000001021

**Conjecture (as stated).** "The minimum number of vertices of a
(3,6)-regular Tanner graph of girth 12 is 132 (minimal graph counting,
computationally verifiable)."

**Verdict: FALSE.**

A Tanner graph is bipartite with a degree-3 class (variable nodes) and a
degree-6 class (check nodes). If the girth is at least 12, the radius-5 ball
around any variable node is a tree: two distinct paths of lengths `i, j <= 5`
from the root ending at the same vertex would close a cycle of length
`i + j <= 10 < 12`. Hence the BFS layers are forced:

| depth | children per vertex | layer size |
|-------|---------------------|-----------:|
| 0     | 3                   |          1 |
| 1     | 5                   |          3 |
| 2     | 2                   |         15 |
| 3     | 5                   |         30 |
| 4     | 2                   |        150 |
| 5     | –                   |        300 |

Total: `1 + 3 + 15 + 30 + 150 + 300 = 499`. So every
(3,6)-regular girth-12 Tanner graph has **at least 499 vertices**, and 132 is
impossible.

Imposing the (3,6)-regular balance relation `3V = 6C` (i.e. `V = 2C`)
strengthens the bound: the forced check-side layers number
`3 + 30 + 300 = 333`, so `C >= 333`, hence `V >= 666` and the total is
`N = 3C >= 999`.

Scanning the whole parameter family `(dv, dc) in [2,8]^2`, even girth in
`{4, 6, ..., 16}` yields **no** Moore-type bound equal to 132. For
`(dv, dc) = (3,6)` the rigorous balanced bounds are 24 (girth 6), 99
(girth 8), 249 (girth 10), 999 (girth 12); the raw tree-ball bound for
girth 12 is 499. No reading of "girth 12" produces 132.

## Contents

| Path | Description |
|------|-------------|
| `main.tex` | Standalone article: collision lemma, forced layer table, 499 bound, 999 balanced variant, parameter-family note. |
| `reproduce.py` | Stdlib-only verifier: layer arithmetic, symbolic BFS of the radius-5 ball, parameter-family scan. |
| `lean4/` | Core Lean 4 formalisation (no Mathlib) of the forced layer count and the impossibility statement. |
| `lean4/README.md` | What the Lean development does and does not formalise. |

## Reproduction

```sh
# Python verifier (prints PASS, exits 0)
python3 reproduce.py

# Lean build
export PATH="/opt/homebrew/bin:$PATH"
cd lean4 && lake build && lake env lean Check.lean

# PDF
export PATH="/opt/homebrew/bin:$PATH"
mkdir -p build && tectonic --outdir build main.tex   # -> build/main.pdf
```

`lean4/lean-toolchain` pins `leanprover/lean4:v4.33.1`.

## What is formally checked

* `reproduce.py` computationally confirms the forced layers `[1,3,15,30,150,300]`,
  the sum 499, the symbolic radius-5 ball of 499 distinct vertices, and that
  no parameter-family bound equals 132.
* Lean formalises the layer arithmetic and the concrete alternating tree of
  499 vertices, and states the impossibility of a 132-vertex graph, with a
  clean axiom audit (`lake env lean Check.lean` reports no axioms, in
  particular no `sorryAx` and no `Lean.ofReduceBool`).
* The graph-theoretic collision lemma is proved in `main.tex` and
  computationally evidenced in `reproduce.py`; it is **not** formalised in
  Lean (see `lean4/README.md`).
