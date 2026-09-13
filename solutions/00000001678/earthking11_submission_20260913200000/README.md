# Disproof of conjecture `00000001678`

**Verdict: FALSE.**

This submission disproves conjecture `00000001678` as stated. The failure is not
the claim that the difference lies in `{0, 1}` but the **“exactly”** clause of the
classification: the trees with difference one are *not* exactly the odd-diameter
trees admitting a perfect matching. In fact, by the AIM theorem, the zero forcing
number equals the path cover number on every tree, so the difference is always
`0` and the difference-one class is empty; on the other hand the odd-diameter
trees admitting a perfect matching are abundant. The path `P_4` is a concrete
witness, and `P_2, P_6, P_8, …` give an infinite family.

## The conjecture

Original statement (English and Chinese) as filed in
`conjectures/00000001678.md`:

> **English.** Conjecture: The difference between the zero forcing number and the
> path cover number on trees takes values in {0, 1}, with an explicit tree
> classification (zero-forcing versus path-cover tree classification); and the
> trees with difference one are exactly the odd-diameter trees admitting a
> perfect matching.
>
> **中文。** 猜想：零力数(zero forcing number)与路径覆盖数之差在树上取值 {0, 1} 且
> 树分类显式(Z−路径覆盖树分类)；且差为一的树恰为含完美匹配的奇直径树。

## Definitions

**Zero forcing number (colour-change rule).** Colour every vertex of a graph
`G = (V, E)` either black or white. The *colour-change rule* is: if a black
vertex `u` has *exactly one* white neighbour `v`, then `v` is turned black, and
we say `u` *forces* `v`. A *zero forcing set* is a set `S ⊆ V` such that, starting
with exactly the vertices of `S` black, repeated application of the rule turns
every vertex black. The *zero forcing number* `Z(G)` is the minimum size of a
zero forcing set.

**Path cover number.** A *path cover* of `G` is a set of pairwise vertex-disjoint
paths whose vertex sets cover `V`; it is *induced* if each path is an induced
subgraph. The *path cover number* `P(G)` is the minimum number of paths in a path
cover. For a tree the two conventions coincide, because a path subgraph of a tree
is automatically induced (a tree has no chords).

**Diameter and perfect matching.** `diam(G)` is the maximum graph distance between
two vertices. A *perfect matching* is a set of pairwise disjoint edges covering
every vertex.

The conjecture compares the two classes

```
D = { T a tree : Z(T) − P(T) = 1 }
R = { T a tree : diam(T) odd and T admits a perfect matching }
```

and asserts `D = R`.

## Why it is false

### The AIM theorem: the difference is always zero

> **Theorem (AIM; Barioli–Fallat–Hogben et al., 2008).** For every tree `T`,
> `Z(T) = P(T)`.

Reference: F. Barioli, S. Fallat, L. Hogben, et al., *Zero forcing sets and the
minimum rank of graphs*, Linear Algebra and its Applications **428** (2008)
1628–1648. Consequently `Z(T) − P(T) = 0` for every tree, so `D = ∅`; but `R` is
non-empty (all paths `P_{2k}` lie in it). Hence `D = R` is impossible, and the
“exactly” clause fails.

### The witness `P_4`

Let `T = P_4`, the path on four vertices `v1—v2—v3—v4`.

- **`Z(P_4) = 1`.** Take `S = {v1}`. Vertex `v1` is black with the unique white
  neighbour `v2`, so `v1` forces `v2`. Then `v2` is black with neighbours `v1`
  (black) and `v3` (white), so `v2` forces `v3`. Then `v3` forces `v4`. All four
  vertices are black, so `Z(P_4) ≤ 1`. The empty set forces nothing (there is no
  black vertex to apply the rule with), so `Z(P_4) ≥ 1`. Hence `Z(P_4) = 1`. The
  explicit forcing sequence is
  `{v1} → {v1,v2} → {v1,v2,v3} → {v1,v2,v3,v4}`.
- **`P(P_4) = 1`.** The single path `v1—v2—v3—v4` covers all four vertices and is
  an induced path (a tree has no chords). Every path cover has at least one path,
  so `P(P_4) = 1`.
- **Difference.** `Z(P_4) − P(P_4) = 1 − 1 = 0 ≠ 1`, so `P_4 ∉ D`.
- **Diameter.** `dist(v1, v4) = 3` and all other distances are smaller, so
  `diam(P_4) = 3`, which is **odd**.
- **Perfect matching.** `{v1v2, v3v4}` is a perfect matching of `P_4`, so
  `P_4 ∈ R`.

Therefore `P_4 ∈ R` but `P_4 ∉ D`: an odd-diameter tree with a perfect matching
whose difference is not one. The “exactly” clause is false.

### The family `P_2`, `P_4`, `P_6`, … 

`P_2` is an even smaller witness: `Z(P_2) = P(P_2) = 1`, its diameter is `1`
(odd), and its unique edge is a perfect matching, yet the difference is `0`.
More generally, for every `k ≥ 1` the path `P_{2k}` has `Z = P = 1`, diameter
`2k − 1` (odd) and the perfect matching
`{v1v2, v3v4, …, v_{2k−1}v_{2k}}`, hence
`P_{2k} ∈ R \ D`. The counterexamples are therefore infinite in number.

### Computational corroboration

`reproduce.py` brute-forces `Z` over all subsets using the colour-change closure
and `P` by exhaustive path-cover search. For `P_n`, `n = 1, …, 10`:

| `n` | `Z(P_n)` | `P(P_n)` | `Z−P` | `diam` | odd? | perfect matching? |
|----:|---------:|---------:|------:|-------:|:----:|:-----------------:|
| 1  | 1 | 1 | 0 | 0 | no  | no  |
| 2  | 1 | 1 | 0 | 1 | yes | yes |
| 3  | 1 | 1 | 0 | 2 | no  | no  |
| 4  | 1 | 1 | 0 | 3 | yes | yes |
| 5  | 1 | 1 | 0 | 4 | no  | no  |
| 6  | 1 | 1 | 0 | 5 | yes | yes |
| 7  | 1 | 1 | 0 | 6 | no  | no  |
| 8  | 1 | 1 | 0 | 7 | yes | yes |
| 9  | 1 | 1 | 0 | 8 | no  | no  |
| 10 | 1 | 1 | 0 | 9 | yes | yes |

Every odd-diameter `P_n` admitting a perfect matching (`n = 2, 4, 6, 8, 10`) has
`Z − P = 0`. Exhaustively enumerating all trees on `1, …, 10` vertices — the
`201` isomorphism classes, generated from Prüfer sequences for `n ≤ 8` and by
canonical rooted trees for `n = 9, 10`, cross-validated — gives:

```
trees with Z − P = 1                            : 0
trees with odd diameter and a perfect matching  : 14
trees with Z = P (AIM theorem)                  : 201
```

The difference-one class is empty, while odd-diameter trees with a perfect
matching exist (for example `P_2, P_4, P_6, P_8, P_10` and others). The
classification is refuted.

## Files

| File | Description |
|:-----|:------------|
| `README.md` | This document: verdict, conjecture quote, definitions, the `P_4` computation, the `P_{2k}` family, the AIM context, reproduction commands, submission status. |
| `main.tex` | LaTeX source of the disproof. Standalone `article`, compiles with `tectonic main.tex`. |
| `build/main.pdf` | PDF produced by `tectonic`; non-empty. |
| `reproduce.py` | Python 3 (standard library only): `Z` by colour-change closure, `P` by exhaustive path-cover search, the `P_n` table for `n = 1..10`, and all trees on `1..10` vertices. Asserts the refutation and prints `PASS`/`FAIL`. |
| `lean4/lean-toolchain` | Pins `leanprover/lean4:v4.33.1`. |
| `lean4/lakefile.toml` | Lake configuration; library `Main`, no dependencies. |
| `lean4/Main.lean` | Lean 4 formalisation of the `P_4` witness, core Lean only (`import Std`, no Mathlib, no `sorry`). |
| `lean4/Check.lean` | `#print axioms` audit for every theorem. |
| `lean4/README.md` | Statement table, proof strategy, and scope note for the formalisation. |

## Reproducing

The numerical checks are dependency-free and run in a few seconds:

```sh
python3 reproduce.py
```

It prints the `P_n` table, asserts that every odd-diameter `P_n` admitting a
perfect matching has `Z − P = 0`, enumerates all trees on up to `10` vertices,
asserts that no tree has `Z − P = 1` while `14` have odd diameter and a perfect
matching, and ends with a `PASS`/`FAIL` summary. A `FAIL` (non-zero exit status)
means a claimed refutation check did not verify.

The LaTeX document is built with:

```sh
tectonic main.tex
```

(`build/main.pdf` is the compiled document; the plain command writes `main.pdf`
next to the source, which was moved to `build/`.)

The Lean 4 project is built and audited with:

```sh
cd lean4
lake build
lake env lean Check.lean
```

The project uses the toolchain pinned in `lean4/lean-toolchain`
(`leanprover/lean4:v4.33.1`) and imports only `Std`; it does not depend on
Mathlib.

## Status against the submission rules

Rule 3 requires each submission to contain the LaTeX source code, a PDF
document, and a Lean 4 project.

- **LaTeX source** — present (`main.tex`), a standalone `article` using
  `geometry`, `amsmath`, `amssymb`, `amsthm`, `array`, `parskip`, and `xeCJK`
  (for the bilingual Chinese quotation). It compiles with `tectonic main.tex`
  without external figures, and the compiled PDF exists at `build/main.pdf`.
- **PDF document** — `build/main.pdf` (≈ 86 KB, 3 pages) is produced by
  `tectonic main.tex` in this environment and is non-empty. Note: rendering the
  Chinese quote uses the macOS font `Songti SC` via `xeCJK`; on a machine
  without that font, `tectonic` still produces the PDF but may not render the
  Chinese characters.
- **Lean 4 project** — present under `lean4/` with `lean-toolchain`,
  `lakefile.toml`, `Main.lean`, and `Check.lean`. In this environment
  `lake build` exits `0`, and `lake env lean Check.lean` reports that every
  theorem depends only on the standard-library axiom `propext` — no `sorryAx`
  and no Mathlib. The formalisation proves, by computation, that
  `Z(P_4) = 1`, `P(P_4) = 1`, `diam(P_4) = 3` is odd, `P_4` has a perfect
  matching, and `Z(P_4) − P(P_4) = 0 ≠ 1`.
