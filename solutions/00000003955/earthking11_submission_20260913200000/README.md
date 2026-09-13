# Disproof of conjecture `00000003955`

**Verdict: FALSE.**

This submission disproves conjecture `00000003955` as stated. The conjecture is
built on the assertion that rank-width `r` and treewidth `t` always satisfy the
"classical inequality" `t ≤ 3r − 1`. **That inequality is already false**, and it
fails at the smallest non-trivial complete graph: `K₄` has rank-width `1` and
treewidth `3`, so

```
t = 3  >  2 = 3·1 − 1 = 3r − 1.
```

Because the claimed inequality is false, nothing can be built on it: the
follow-up claims (that the constant `3` is optimal and that there is a family of
rank-width `r` and treewidth exactly `3r − 1`) have no valid basis. Worse, there
is not merely a wrong constant but no valid inequality of the form `t ≤ f(r)`
at all: for every `n ≥ 2`,

```
rank-width(K_n) = 1,     treewidth(K_n) = n − 1,
```

so treewidth grows without bound while rank-width stays `1`. The smallest
counterexample is `K₄`; the inequality `t ≤ 3r − 1` holds for `K₂` (`1 ≤ 2`) and
is saturated at `K₃` (`2 = 3·1 − 1`), but fails for every `K_n` with `n ≥ 4`.

## The conjecture

Quoted verbatim from `conjectures/00000003955.md`:

> **English.** Definition: The rank-width is a width parameter satisfying, with
> treewidth t, the classical inequality t <= 3r - 1. Conjecture: The constant 3
> in the inequality t <= 3r - 1 is optimal, with an explicit family of graphs of
> rank-width r and treewidth exactly 3r - 1; moreover the kernelization kernel
> size for distance-hereditary graphs is constant. (optimal
> rank-width-treewidth constant)

> **中文。** 定义：rank-width 指宽度参数，与树宽满足 t ≤ 3r − 1 的经典不等式。
> 猜想：不等式 t ≤ 3r − 1 中的常数 3 最优，存在秩宽 r 树宽恰 3r − 1 的显式图族；
> 且距离遗传图的核化核尺寸为常数。（秩宽-树宽常数最优）

The conjecture contains a definitional premise (the inequality `t ≤ 3r − 1`) and
two claims resting on it. A conjecture whose stated definition is false cannot
be correct, so it suffices to refute the premise. We do not need to (and do not)
make any claim about the distance-hereditary kernelization clause.

## Definitions

**Cut-rank over `GF(2)`.** Let `G = (V, E)` be a finite simple graph and let
`(X, Y)` be a bipartition of `V` (`X ∩ Y = ∅`, `X ∪ Y = V`). The **cut matrix**
`A(G, X, Y)` is the `|X| × |Y|` matrix over `GF(2)` with `A_{xy} = 1` if
`xy ∈ E` and `A_{xy} = 0` otherwise. The **cut-rank** of `(X, Y)` is
`cutrk_G(X, Y) = rank_{GF(2)} A(G, X, Y)`.

**Rank-width.** A **rank-decomposition** of `G` is a pair `(T, τ)` where `T` is
a binary tree with `|V|` leaves and `τ : V → L(T)` is a bijection. Each edge `e`
of `T` splits the leaves, hence `V`, into a bipartition `(X_e, Y_e)`. The
**width** of `(T, τ)` is `max_e cutrk_G(X_e, Y_e)`, and the **rank-width** is

```
rw(G) = min over rank-decompositions (T, τ) of  max over edges e of  cutrk_G(X_e, Y_e).
```

**Treewidth.** A **tree decomposition** of `G = (V, E)` is a pair
`(T, {B_t}_{t ∈ V(T)})`, where `T` is a tree and each **bag** `B_t ⊆ V`, such
that (i) every vertex lies in some bag; (ii) every edge `uv ∈ E` lies inside some
bag; (iii) for every `v ∈ V`, the bags containing `v` induce a connected subtree
of `T`. The **width** is `max_t |B_t| − 1`, and the **treewidth** `tw(G)` is the
minimum width over all tree decompositions.

## The counterexample: `K₄`

Let `K₄` have vertex set `V = {0, 1, 2, 3}` with `ij ∈ E` for all distinct
`i, j`.

### Rank-width of `K₄` is `1`

Every nontrivial bipartition of `K₄` has cut-rank `1`. Indeed, for `x ∈ X` and
`y ∈ Y` we have `x ≠ y` (the sides are disjoint), hence `xy ∈ E(K₄)` and
`A_{xy} = 1`: the cut matrix is the all-ones `|X| × |Y|` matrix. Writing
`𝟙_X`, `𝟙_Y` for the all-ones column vectors, `A = 𝟙_X 𝟙_Yᵀ` is an outer
product, so `rank A ≤ 1`; and `A ≠ 0` because both sides are nonempty, so
`rank A ≥ 1`. Hence `rank A = 1` over `GF(2)` (and over any field).

The seven bipartitions of a four-element set, up to swapping the sides, and
their cut-ranks are:

| bipartition | cut matrix shape | GF(2) rank |
|:--|:--|:--:|
| `{0} \| {1,2,3}` | `1 × 3` all-ones | `1` |
| `{1} \| {0,2,3}` | `1 × 3` all-ones | `1` |
| `{2} \| {0,1,3}` | `1 × 3` all-ones | `1` |
| `{3} \| {0,1,2}` | `1 × 3` all-ones | `1` |
| `{0,1} \| {2,3}` | `2 × 2` all-ones | `1` |
| `{0,2} \| {1,3}` | `2 × 2` all-ones | `1` |
| `{0,3} \| {1,2}` | `2 × 2` all-ones | `1` |

*Upper bound `rw(K₄) ≤ 1`:* the **caterpillar** rank-decomposition that splits
off one vertex at a time has internal cuts `{0}|{1,2,3}`, `{1}|{2,3}`,
`{2}|{3}`, all of cut-rank `1`; so its width is `1`.

*Lower bound `rw(K₄) ≥ 1`:* every rank-decomposition has a root edge, which
splits `V` into two nonempty parts (a binary tree with `≥ 2` leaves has a
nontrivial root split); that bipartition is one of the seven above and has
cut-rank `1`, so every decomposition has width at least `1`.

Therefore `rw(K₄) = 1`. (More generally `rw(K_n) = 1` for all `n ≥ 2`: the same
caterpillar gives `≤ 1`, and `rw(G) = 0` holds exactly for edgeless `G`, so an
edge forces `≥ 1`.)

### Treewidth of `K₄` is `3`

*Upper bound `tw(K₄) ≤ 3`:* the tree with a single node `t` and the single bag
`B_t = {0,1,2,3}` is a tree decomposition (every vertex and every edge lies in
the bag; connectedness is trivial), of width `|B_t| − 1 = 3`.

*Lower bound `tw(K₄) ≥ 3` via the minimum-degree lemma.* The relevant lemma is:

> **Lemma (minimum-degree bound).** If a graph `G` with at least one vertex has
> `tw(G) ≤ w`, then `G` has a vertex of degree at most `w`.

*Proof.* Take a tree decomposition of width `≤ w` and reduce it so that no leaf
bag is contained in its neighbour's bag (delete such a leaf; conditions (i)–(iii)
are preserved, the width does not increase, and the process terminates). If one
node remains then its bag is all of `V`, and any vertex has all its neighbours in
it, so `deg ≤ |B| − 1 ≤ w`. Otherwise pick a leaf `t` with neighbour `t'` and
`v ∈ B_t \ B_{t'}`. The bags containing `v` form a connected subtree containing
the leaf `t`; since `v ∉ B_{t'}`, that subtree is `{t}`, so `B_t` is the only bag
containing `v`. Every neighbour `u` of `v` shares some bag with `v` (condition
(ii)), which must be `B_t`, so `u ∈ B_t`. Hence every neighbour of `v` lies in
`B_t` and `deg(v) ≤ |B_t| − 1 ≤ w`. `∎`

Since every vertex of `K₄` is adjacent to the other three, `δ(K₄) = 3`. Applying
the lemma with `w = 2` is impossible, so `tw(K₄) ≥ 3`. (Equivalently
`tw(G) ≥ δ(G)` for every nonempty graph `G`.)

Hence `tw(K₄) = 3`.

### The inequality fails

```
rank-width(K₄) = 1,   treewidth(K₄) = 3,   3r − 1 = 2,   t = 3 > 2 = 3r − 1.
```

So the "classical inequality" `t ≤ 3r − 1` is false, and conjecture
`00000003955` is FALSE.

## The sharpening: no function of `r` bounds `t`

For every `n ≥ 2`:

```
rank-width(K_n) = 1,     treewidth(K_n) = n − 1.
```

The treewidth statement follows from the single bag `{0, …, n−1}` (width
`n − 1`) and the minimum-degree bound (every vertex has degree `n − 1`, so
`tw(K_n) ≥ n − 1`). Hence for any function `f` and any `n > f(1) + 1`,

```
tw(K_n) = n − 1 > f(1) = f(rw(K_n)),
```

so **no function `f` satisfies `tw(G) ≤ f(rw(G))` for all graphs `G`**. The
constant `3` is therefore not merely non-optimal; the whole shape
`t ≤ 3r − 1` is invalid. The boundary cases: `K₂` gives `1 ≤ 2`, `K₃` saturates
`2 = 3·1 − 1`, and `K₄` is the smallest counterexample.

## Files

| File | Description |
|:-----|:------------|
| `README.md` | This document: verdict, the conjecture, definitions, the `K₄`/`K_n` disproof, reproduction, file list, rule status. |
| `main.tex` | LaTeX source of the disproof. Standalone `article`, compiles with `tectonic main.tex`. |
| `build/main.pdf` | PDF produced by `tectonic --outdir build main.tex` (a copy of `main.pdf` is also written in the submission root by `tectonic main.tex`). |
| `reproduce.py` | Python 3 (standard library only) verification: GF(2) cut-ranks of all bipartitions of `K_n`, exact treewidth by elimination orders, the minimum-degree bound, the `t` vs `3r − 1` table, assertions, `PASS`/`FAIL`. |
| `lean4/lean-toolchain` | Pins `leanprover/lean4:v4.33.1`. |
| `lean4/lakefile.toml` | Lake configuration; library `Main`, no dependencies. |
| `lean4/Main.lean` | Lean 4 formalisation, core Lean only (`import Std`, no Mathlib, no `sorry`). |
| `lean4/Check.lean` | `#print axioms` audit for every theorem. |
| `lean4/README.md` | Statement table, proof strategy, and an explicit statement of what is formalised vs. argued in prose. |

## Reproducing

The numerical checks are dependency-free and run in well under a second:

```sh
python3 reproduce.py
```

It enumerates all bipartitions of `K_n` for `n = 2, …, 7`, forms each cut matrix
over `GF(2)`, computes its rank by Gaussian elimination, computes the exact
treewidth as the minimum elimination width over all `n!` orders, checks the
minimum-degree bound, prints the table of `t` against `3r − 1`, asserts the
inequality fails for every `n ≥ 4`, and prints `PASS` (exit `0`) or `FAIL`
(exit non-zero). Observed tail of the output:

```
[3] Tabulated inequality t <= 3r - 1 (r = rank-width, t = treewidth)
      n |  r |  t | 3r - 1 | holds?
      --+----+----+--------+-------
      2 |  1 |  1 |   2    | yes
      3 |  1 |  2 |   2    | yes
      4 |  1 |  3 |   2    | NO    <-- counterexample
      5 |  1 |  4 |   2    | NO    <-- counterexample
      6 |  1 |  5 |   2    | NO    <-- counterexample
      7 |  1 |  6 |   2    | NO    <-- counterexample
...
PASS: for every n in 2..7, rank-width(K_n) = 1, treewidth(K_n) = n - 1,
      and every bipartition of K_n has GF(2) cut-rank 1.
      The inequality t <= 3r - 1 fails for every n >= 4; the smallest
      counterexample is K_4 with t = 3 > 2 = 3*1 - 1.  Conjecture
      00000003955 is FALSE as stated.
```

The LaTeX document is built with:

```sh
tectonic main.tex              # writes main.pdf
tectonic --outdir build main.tex   # writes build/main.pdf
```

The Lean 4 project is built with:

```sh
cd lean4
lake build
lake env lean Check.lean
```

The project uses the toolchain pinned in `lean4/lean-toolchain`
(`leanprover/lean4:v4.33.1`) and imports only `Std`; it does not depend on
Mathlib.

### Acceptance gate (actually run)

| Command | Result |
|:--|:--|
| `cd lean4 && lake build` | exit `0`, `Build completed successfully (3 jobs).` |
| `cd lean4 && lake env lean Check.lean` | exit `0`; every theorem reports only `propext` (a few also `Quot.sound`); **no `sorryAx`**; two theorems depend on no axioms |
| `tectonic main.tex` | exit `0`, `Writing 'main.pdf' (87.3 KiB)`; `build/main.pdf` present and non-empty (`89396` bytes) |
| `python3 reproduce.py` | prints `PASS`, exit `0` |

## Status against the submission rules

Rule 3 of The Last Math Competition requires each submission to contain the
LaTeX source code, a PDF document, and a Lean 4 project.

- **LaTeX source** — present (`main.tex`), a standalone `article` using only
  `geometry`, `amsmath`, `amssymb`, `amsthm`, `array`, `parskip`, and `xeCJK`
  (for the bilingual Chinese quotation), designed to compile with
  `tectonic main.tex`. It contains the full proof: cut-rank and rank-width of
  `K₄`, the treewidth upper bound and the minimum-degree lower bound, and the
  conclusion `t > 3r − 1`, together with the `K_n` sharpening.
- **PDF document** — present at `build/main.pdf` (and as `main.pdf`), produced
  by `tectonic` (version 0.17.0) and non-empty (`89396` bytes). Tectonic emits a
  warning that the CJK font (`PingFang SC`) resolves to an absolute system path,
  so the PDF build is not byte-reproducible on machines without that font;
  `main.tex` falls back through `FandolSong-Regular`, `Noto Serif CJK SC`,
  `Songti SC`, `STSong`, and finally still compiles (with missing-glyph warnings
  for the Chinese quotation only) if no CJK font is installed.
- **Lean 4 project** — present under `lean4/`, with `lean-toolchain`
  (`leanprover/lean4:v4.33.1`), `lakefile.toml`, `Main.lean`, and `Check.lean`.
  It is written in core Lean only (no Mathlib) and contains no `sorry`. It
  formalises a computable `GF(2)` rank of bit-mask matrices, the cut matrix of a
  bipartition of `K₄`, the fact that all seven bipartitions of `K₄` have
  cut-rank `1`, a lightweight treewidth model on `Fin 4` (the exact
  elimination-order characterisation), the minimum-degree lemma, the explicit
  width-`3` decomposition, the computed value `tw(K₄) = 3`, and the conclusion
  `tw(K₄) > 3·rw(K₄) − 1`.
- **Scope of the formalisation** — stated explicitly in `lean4/README.md`. What
  is argued in prose rather than formalised: (1) the classical identification of
  the elimination-order model with the standard tree-decomposition definition of
  treewidth (the model *is* the exact elimination characterisation); (2) the
  identification `rankWidthK4 = 1` (the cut-rank facts for all seven
  bipartitions are formalised, but the min over all rank-decompositions is not);
  (3) `K_n` for `n ≥ 5` and the no-function theorem (proved in `main.tex`,
  verified numerically in `reproduce.py`); (4) the distance-hereditary
  kernelization clause. No `sorry` and no unproved assumption is used anywhere
  in the Lean file.
