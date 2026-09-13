# Disproof of conjecture `00000001682`

**Verdict: FALSE.**

This submission disproves conjecture `00000001682` as stated. The refutation is
unconditional and elementary: the parenthetical claim that the generalized
Petersen graph `G(n, 2)` is pancyclic for every `n >= 11` fails already at
`n = 11`. The graph `G(11, 2)` is **triangle-free**, so it is not pancyclic: it
has `|V| = 22` vertices, and pancyclicity would require a cycle of length `3`.

## The conjecture

Quoted verbatim from `conjectures/00000001682.md`:

> **English.** Conjecture: The pancyclicity threshold of generalized Petersen
> graphs G(n, 2) has a complete classification for n ≥ 11 (G(n,2) pancyclic).
>
> **中文。** 猜想：广义 Petersen 图 G(n, 2) 的满圈泛环性(pancyclic)阈值为 n ≥ 11
> 的完全分类(G(n,2) 泛环)。

## Definitions

**Generalized Petersen graph.** For integers `n >= 3` and
`1 <= k <= (n-1)/2`, the graph `GP(n, k)` has vertex set

```
V = { u_0, u_1, ..., u_{n-1} } ∪ { v_0, v_1, ..., v_{n-1} },   |V| = 2n,
```

and edge set

```
E = { u_i u_{i+1} }  ∪  { u_i v_i }  ∪  { v_i v_{i+k} },
```

with all subscripts read modulo `n`. The `u_i u_{i+1}` are the *outer* edges,
the `u_i v_i` the *spokes*, and the `v_i v_{i+k}` the *inner* edges. Here and
below we use the standard convention `G(n, k) = GP(n, k)`; the conjecture
concerns `k = 2`.

**Pancyclic.** A graph is *pancyclic* if it contains a simple cycle of every
length `L` with `3 <= L <= |V|`. Thus `GP(n, 2)` is pancyclic exactly when it
has a cycle of each length `3, 4, ..., 2n`.

The conjecture therefore claims: *`GP(n, 2)` is pancyclic for every `n >= 11`.*
That claim is false.

## The witness `G(11, 2)` is triangle-free

For `k = 2` the neighbourhoods are (indices mod `n`)

```
N(u_i) = { u_{i-1}, u_{i+1}, v_i },        N(v_i) = { v_{i-2}, v_{i+2}, u_i }.
```

For `n = 11`:

* **No outer triangle.** On the outer layer the graph is the 11-cycle
  `u_0 u_1 ... u_10 u_0`, which is triangle-free.
* **No inner triangle.** On the inner layer `v_i` is joined to `v_{i±2}`; since
  `gcd(11, 2) = 1`, this is a single 11-cycle, also triangle-free.
* **No mixed triangle.** Every `v_i` has exactly one neighbour in the outer
  layer, namely `u_i`; every `u_i` has exactly one neighbour in the inner layer,
  namely `v_i`. So a triangle cannot have both an outer and an inner vertex.
  (A triangle has three vertices in two classes, so one class would contain two
  vertices; that class's vertex would need two neighbours in the other class.)

Every triangle would therefore be monochromatic, and neither monochromatic
triangle exists. Hence **`GP(11, 2)` is triangle-free**.

Exhaustive confirmation: testing all `C(22, 3) = 1540` vertex triples gives
`0` triangles. This is done by `reproduce.py` and certified in Lean by the
kernel-reduction theorem `gp11_triangle_count : triangleCount 11 2 = 0`.

### Not pancyclic

Since `G(11, 2)` has no 3-cycle, it is not pancyclic. Exhaustive search shows
that the lengths it is missing are exactly

```
3, 4, 6, 7, 22,
```

while it does have cycles of every other length in `3..22`. (The absence of a
22-cycle reflects the fact that `G(11, 2)` is hypohamiltonian, consistent with
`11 ≡ 5 (mod 6)`.) The missing lengths `3` and `4` alone suffice.

## The claim fails for all `n = 5, ..., 16`

Exact missing cycle lengths for `GP(n, 2)`, computed exhaustively:

| `n` | `|V| = 2n` | triangles | missing cycle lengths |
|----:|-----------:|----------:|:----------------------|
| 5  | 10 | 0 | 3, 4, 7, 10 |
| 6  | 12 | 2 | 4 |
| 7  | 14 | 0 | 3, 4 |
| 8  | 16 | 0 | 3, 6 |
| 9  | 18 | 0 | 3, 4, 6 |
| 10 | 20 | 0 | 3, 4, 6, 7, 19 |
| 11 | 22 | 0 | 3, 4, 6, 7, 22 |
| 12 | 24 | 0 | 3, 4, 7 |
| 13 | 26 | 0 | 3, 4, 6, 7 |
| 14 | 28 | 0 | 3, 4, 6 |
| 15 | 30 | 0 | 3, 4, 6, 7 |
| 16 | 32 | 0 | 3, 4, 6, 7, 31 |

Every row has a non-empty "missing" set, so **no `GP(n, 2)` with
`5 <= n <= 16` is pancyclic**. In particular `n = 11 >= 11` is non-pancyclic,
refuting the conjecture's parenthetical claim and its asserted threshold.

## Structural remark: `GP(n, 2)` has a triangle iff `n | 6`

No triangle can be mixed (as above: each vertex has exactly one neighbour in the
other layer). So triangles are monochromatic:

* the outer layer is the `n`-cycle `C_n`, which has a triangle iff `n = 3`;
* the inner layer is a single `C_n` when `n` is odd (`gcd(n,2) = 1`) and two
  `C_{n/2}` when `n` is even, so it has a triangle iff `n = 3` or `n/2 = 3`.

Hence for `n >= 4` the graph `GP(n, 2)` contains a triangle **iff `n = 6`**
(equivalently, among `n` dividing `6`, only the non-degenerate case `n = 6`).
This is why every `n >= 7` is automatically non-pancyclic, and it is
corroborated by the table: the only nonzero triangle count is `2` at `n = 6`.
The true classification for these graphs concerns **Hamiltonicity**
(`GP(n, 2)` is hypohamiltonian for `n ≡ 5 (mod 6)`, e.g. `n = 5, 11`), not
pancyclicity; the conjecture appears to garble that statement.

## Files

| File | Description |
|:-----|:------------|
| `README.md` | This document: verdict, quoted conjecture, definitions, witness, table, reproduction, status. |
| `main.tex` | LaTeX source of the disproof. Standalone `article`, compiles with `tectonic main.tex`. |
| `build/main.pdf` | PDF produced by `tectonic main.tex --outdir build` (the artifact is placed in `build/`). |
| `reproduce.py` | Python 3 (standard library only) brute force over `n = 5..16`: triangle counts and exhaustive cycle-existence checks; prints `PASS`/`FAIL`, non-zero exit on failure. |
| `lean4/lean-toolchain` | Pins `leanprover/lean4:v4.33.1`. |
| `lean4/lakefile.toml` | Lake configuration; project `tlmc1682`, library `Main`, no dependencies. |
| `lean4/Main.lean` | Lean 4 formalisation, core Lean only (`import Std`, no Mathlib, no `sorry`). |
| `lean4/Check.lean` | `#print axioms` audit for every theorem. |
| `lean4/README.md` | Statement table, proof strategy, and scope note for the formalisation. |

## Reproducing

Python (dependency-free; runs in a few seconds):

```sh
python3 reproduce.py
```

It builds `GP(n, 2)` for `n = 5..16`, counts the triangles among all
`C(2n, 3)` triples, and decides cycle existence for every length `L = 3..2n` by
two exhaustive methods (subset enumeration of all `C(2n, L)` vertex sets for
small `L`, and a pruned DFS cycle search for larger `L`). It asserts that
`G(11, 2)` has no triangle, prints the per-`n` table of missing lengths, and
exits non-zero on any failure.

LaTeX document:

```sh
tectonic main.tex --outdir build
```

Lean 4 project:

```sh
cd lean4
lake build
lake env lean Check.lean
```

## Status against the submission rules

Rule 3 requires each submission to contain the LaTeX source code, a PDF
document, and a Lean 4 project.

* **LaTeX source** — present (`main.tex`), a standalone `article` using
  `geometry`, `amsmath`, `amssymb`, `amsthm`, `array`, `parskip`, `booktabs`
  and `xeCJK` (the latter only to typeset the Chinese quote of the conjecture).
  It compiles with `tectonic main.tex`.
* **PDF document** — present at `build/main.pdf`, produced by
  `tectonic main.tex --outdir build`.
* **Lean 4 project** — present under `lean4/`, with `lean-toolchain`,
  `lakefile.toml`, `Main.lean`, `Check.lean`, and a `README.md`. It models
  `GP(11, 2)` on `Fin 2 × Fin 11`, defines the adjacency predicate and a
  triangle, and proves by kernel reduction that no triangle exists
  (`gp11_triangle_free`, `gp11_triangle_count = 0`). It then defines
  `HasCycleOfLength G L` (an injective closed walk with `L` vertices) and
  `Pancyclic G`, shows that pancyclicity of `G(11, 2)` would yield a 3-cycle,
  and concludes `gp11_not_pancyclic : ¬ Pancyclic (gp 11 2)`. It uses core Lean
  only (no Mathlib) and contains no `sorry`; `lake env lean Check.lean` reports
  no `sorryAx` and only the core axioms `propext` and `Quot.sound`.

A caveat on reproducibility of the PDF: the CJK font (`PingFang SC`) is taken
from the local system font collection, so rebuilds on machines without that font
may need a different `\setCJKmainfont`.
