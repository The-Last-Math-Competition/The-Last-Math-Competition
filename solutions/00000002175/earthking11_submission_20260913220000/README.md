# Disproof of conjecture `00000002175`

**Verdict: FALSE.**

This submission disproves conjecture `00000002175` as stated. The refutation is
unconditional, elementary, and already complete at the smallest interesting
ground size: for `n = 4` there is a 3-wise odd-intersecting family of size 4,
whereas the conjecture predicts the maximum `2^{n−3} = 2`. Exhaustive and
branch-and-bound computations give the true maxima `M(0),…,M(7)`, which are
inconsistent with the claimed formula in both directions. A separate check shows
that no affine coset is an extremal family, so the conjecture's characterisation
clause is false too.

## The conjecture

> **Definition:** A 3-wise odd-intersecting family is one where the intersection
> of any three members is odd.
> **Conjecture:** The maximal size is always `2^{n−3}`; and the extremal
> families consist of indicator functions of 3-dimensional affine subspaces.
> (3-wise odd-intersection affine extremal)

Original statement as filed in `conjectures/00000002175.md` (bilingual):

> **English.** Definition: A 3-wise odd-intersecting family is one where the
> intersection of any three members is odd. Conjecture: The maximal size is
> always 2^{n−3}; and the extremal families consist of indicator functions of
> 3-dimensional affine subspaces. (3-wise odd-intersection affine extremal)
>
> **中文。** 定义：3-wise 奇交族指任意三成员之交为奇数的族。猜想：最大尺寸恒为二的
> n 减三次幂；且极值族由三维仿射子空间的指示函数构成。（3-wise 奇交仿射极值）

Throughout, members are subsets of an `n`-element ground set `[n] = {1,…,n}`.

## The counterexample at `n = 4`

Take the ground set `{1,2,3,4}` and the four-member family

```
F = { {1,2}, {1,3}, {1,4}, {1,2,3,4} }.
```

There are `C(4,3) = 4` triples of distinct members. Each triple is checked
explicitly:

| triple | pairwise intersection of the three members | size | odd? |
|:-------|:------------------------------------------:|:----:|:----:|
| `{1,2}`, `{1,3}`, `{1,4}` | `{1,2} ∩ {1,3} ∩ {1,4} = {1}` | 1 | yes |
| `{1,2}`, `{1,3}`, `{1,2,3,4}` | `{1,2} ∩ {1,3} ∩ {1,2,3,4} = {1}` | 1 | yes |
| `{1,2}`, `{1,4}`, `{1,2,3,4}` | `{1,2} ∩ {1,4} ∩ {1,2,3,4} = {1}` | 1 | yes |
| `{1,3}`, `{1,4}`, `{1,2,3,4}` | `{1,3} ∩ {1,4} ∩ {1,2,3,4} = {1}` | 1 | yes |

So `F` is 3-wise odd-intersecting. But

```
|F| = 4  >  2 = 2^{4−3},
```

so the conjecture's size claim is false at `n = 4`. The true maximum at `n = 4`
is in fact `5` (a 5-element witness is `{1}, {1,2}, {1,3}, {1,4}, {1,2,3}`), so
the conjecture is broken even harder than the four-member witness shows.

## True maxima versus the claim

The exact maxima were computed in two independent ways (both implemented in
`reproduce.py`):

- **exhaustive** depth-first search over all `2^{2^n}` subfamilies for
  `n ≤ 4` (with a cardinality prune);
- **branch and bound** for the maximum independent set in the 3-uniform
  hypergraph whose hyperedges are the triples with even intersection, for
  `n = 5, 6, 7`. The bound packs vertex-disjoint forbidden triples (each
  permits at most 2 of its 3 vertices); vertices are ordered by conflict degree
  and precomputed bitmasks make the search run in about ten seconds for `n = 7`.

| `n` | true max `M(n)` | claim `2^{n−3}` | comparison |
|----:|:---------------:|:---------------:|:-----------|
| 0 | 1 | — (undefined) | — |
| 1 | 2 | — (undefined) | — |
| 2 | 2 | — (undefined) | — |
| 3 | 4 | 1 | claim too **small** by 3 |
| 4 | 5 | 2 | claim too **small** by 3 |
| 5 | 7 | 4 | claim too **small** by 3 |
| 6 | 8 | 8 | equal (coincidence only) |
| 7 | 10 | 16 | claim too **large** by 6 |

```
M(n) = 1, 2, 2, 4, 5, 7, 8, 10     (n = 0, …, 7)
```

The claim is too small at `n = 3, 4, 5`, too large at `n = 7` (there is no
family of size 16 — the maximum is 10), and agrees at `n = 6` only by
coincidence. The single formula `2^{n−3}` is therefore not the truth, and no
adjustment of a constant can fix the observed sequence.

## The construction

Exact optimal families for `n = 3,…,7` have the following shape. Fix a point
`x` and let `Y = [n] \ {x}`. Put

```
G = { ∅ } ∪ { all singletons {y}, y ∈ Y } ∪ { the edges of a matching on Y },
F = { {x} ∪ g : g ∈ G }.
```

Any three distinct members meet in `{x} ∪ (g₁ ∩ g₂ ∩ g₃)`. For the three `gᵢ`
chosen from `∅`, singletons, and matching edges, the intersection `g₁ ∩ g₂ ∩ g₃`
is always empty: if any `gᵢ = ∅` this is clear; at most one singleton can equal a
given `{y}` and at most one matching edge contains `y`, so a singleton cannot
appear in two distinct `gᵢ`; and two distinct matching edges are disjoint. Hence
every such triple meets in `{x}`, of odd size 1, and `F` is valid. Its size is

```
|F| = 1 + (n−1) + ⌊(n−1)/2⌋ = n + ⌊(n−1)/2⌋,
```

which equals the computed maximum `M(n) = 4, 5, 7, 8, 10` for `n = 3, 4, 5, 6, 7`.
In particular the extremal families have a "fixed point plus an
even-intersecting family on the rest" shape, not the affine-subspace shape the
conjecture proposes.

**Asymptotic lower bound.** Partitioning `Y` into pairs and taking `G =` *all
unions of pairs* gives triple intersections `{x} ∪ (union of pairs)`, again
always odd, of size

```
|F| = 2^{⌊(n−1)/2⌋} ≈ 2^{n/2}.
```

This is an explicit infinite family, so `M(n) ≥ 2^{⌊(n−1)/2⌋}`: the maximum
grows at least like `2^{n/2}`, an exponential of rate `n/2` rather than `n−3`.
(The values `M(6) = 8 = 2^3` and `M(7) = 10` are consistent with growth of that
order. The lower bound alone does not settle the value of `M(n)` for large `n`;
what is rigorous, and decisive, is the computed table above — the claim fails in
both directions within `n ≤ 7`.)

## The affine-subspace characterisation is false

The phrase "indicator functions of 3-dimensional affine subspaces" is
ambiguous, so both readings were tested by enumerating **all** affine cosets of
**all** dimensions in `F₂ⁿ` (a subset of `[n]` is encoded as its indicator
vector in `F₂ⁿ`; a family of indicator vectors is a set of points of `F₂ⁿ`).

- **Literal reading — a 3-dimensional affine subspace** (so `2³ = 8` family
  members). Enumerating all `3`-dimensional subspaces and their cosets:
  `n = 4`: 30 cosets, `0` are 3-wise odd-intersecting; `n = 5`: 620 cosets, `0`;
  `n = 6`: 11160 cosets, `0`; `n = 7`: 188976 cosets, of which `105` are
  3-wise odd, but every one has size `8 < M(7) = 10` and so none is extremal.
- **Codimension-3 reading — a coset of size `2^{n−3}`.** `n = 4`: cosets of size
  `2`, all vacuously 3-wise odd, but `2 < M(4) = 5`; `n = 5`: cosets of size `4`,
  `460` of them 3-wise odd, but `4 < M(5) = 7`; `n = 6`: cosets of size `8`, and
  **none** is 3-wise odd; `n = 7`: such a coset would have size `16 > M(7) = 10`,
  impossible.

Consequently: **no affine coset of any dimension is an extremal family** for
`n = 4, 5, 6, 7`. Since every affine coset has power-of-two size while
`M(4) = 5`, `M(5) = 7`, `M(7) = 10` are not powers of two, no coset can even
have the right size there; and at `n = 6` (where `M(6) = 8 = 2³`) the only
cosets of size 8 are 3-dimensional, and none of them is 3-wise
odd-intersecting. The characterisation clause is therefore false.

**Ambiguity note.** "Indicator functions of 3-dimensional affine subspaces" is
garbled: a 3-dimensional affine subspace has `2³ = 8` points, whereas
`2^{n−3}` is the size of a codimension-3 coset. Each indicator function of a
3-dimensional affine subspace is a *member* of the extremal family, while the
`2^{n−3}` refers to a *number of members*; the two readings are not the same
statement and neither yields valid extremal families. (A curious aside: the
`n = 4` witness `F = {{1,2},{1,3},{1,4},{1,2,3,4}}` *is* an affine coset — of
dimension 2, size 4, not the claimed dimension 3 and not extremal since
`M(4) = 5`. Being an affine coset is thus neither sufficient nor, at the claimed
dimension, possible.)

## Files

| File | Description |
|:-----|:------------|
| `README.md` | This document: verdict, bilingual conjecture quote, the `n = 4` witness with the explicit 4-triple check, the true-maxima table, the affine-counterexample analysis, the construction, the ambiguity note, reproduction, status. |
| `main.tex` | LaTeX source of the disproof. Standalone `article`, compiles with `tectonic main.tex`. |
| `build/main.pdf` | PDF produced by `tectonic --outdir build main.tex`. |
| `reproduce.py` | Python 3 (standard library only): exhaustive search for `n ≤ 4`, branch-and-bound for `n = 5, 6, 7`, the witness and construction checks, and the affine-coset analysis. Prints `PASS`/`FAIL`; non-zero exit on failure. |
| `lean4/lean-toolchain` | Pins `leanprover/lean4:v4.33.1`. |
| `lean4/lakefile.toml` | Lake configuration; library `tlmc2175`, no dependencies. |
| `lean4/Main.lean` | Lean 4 formalisation of the `n = 4` witness (core Lean only: `import Std`, no Mathlib, no `sorry`). |
| `lean4/Check.lean` | `#print axioms` audit for every theorem. |
| `lean4/README.md` | Statement table, proof strategy, and scope note for the formalisation. |

## Reproducing

Python (dependency-free; about 13 seconds, dominated by the `n = 7` search):

```sh
python3 reproduce.py
```

It checks the witness's four triple intersections (each `= {1}`), computes the
maxima `M(0..4)` exhaustively and `M(5..7)` by branch and bound, cross-checks the
two methods at `n = 4`, verifies the constructions, and tests every affine coset
for `n = 4,…,7`. It prints `PASS` and exits `0` exactly when every check holds.

LaTeX document:

```sh
tectonic --outdir build main.tex
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

- **LaTeX source** — present (`main.tex`), a standalone `article` using only
  `geometry`, `amsmath`, `amssymb`, `amsthm`, `array`, `parskip`, and
  `booktabs`, and compiling with `tectonic main.tex`.
- **PDF document** — present at `build/main.pdf`, produced by
  `tectonic --outdir build main.tex`.
- **Lean 4 project** — present under `lean4/`, with `lean-toolchain`,
  `lakefile.toml`, `Main.lean`, `Check.lean`, and a `README.md`. It formalises
  the concrete `n = 4` witness: `TripleOdd F`, the four explicit triple
  intersections (`interSize … = 1`), `F.length = 4`,
  `F.length > 2 ^ (4 - 3 : Nat)`, and a 5-element family `G5` with
  `G5.length = 5`. It uses core Lean only (no Mathlib) and contains no `sorry`;
  `lake env lean Check.lean` reports no `sorryAx` for any theorem.

**No files were deleted and no git operations were performed.**
