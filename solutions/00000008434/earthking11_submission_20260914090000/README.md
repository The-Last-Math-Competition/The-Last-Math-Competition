# Disproof of conjecture `00000008434`

**Verdict: FALSE.**

This submission disproves conjecture `00000008434` as stated. Both clauses are
refuted, by completely explicit finite objects:

* **Clause 1** ("the intersection spectrum is exactly the set of all integer
  values in the interval `[s_0, s_1]`") fails for `AG(3,2)`, the unique
  `3-(8,4,1)` Steiner quadruple system. Its intersection spectrum is `{0, 2}`,
  but the interval `[s_0, s_1] = [0, 2]` also contains `1`, which never occurs.
* **Clause 2** ("`s_0 = s_1` if and only if the design is symmetric") fails for
  the Pasch configuration, a `1-(6,3,2)` design in which every pair of blocks
  meets in exactly one point (`s_0 = s_1 = 1`), yet `b = 4 ≠ 6 = v` is not
  symmetric.

The first clause is refuted by a genuine `3`-design, the strongest possible
structural setting, so no strengthening of the wording can rescue it.

## The conjecture, quoted verbatim

From `conjectures/00000008434.md`:

> **English.** Definition: The intersection structure of a combinatorial
> geometry: the intersection spectrum of its blocks. Conjecture: The
> intersection spectrum is exactly the set of all integer values in the
> interval [s_0,s_1]; and s_0 = s_1 if and only if the design is symmetric.
> (interval characterization of intersection spectra)
>
> **中文。** 定义：组合几何的交集结构指其区组的相交谱。猜想：交谱为区间
> [s₀,s₁] 中一切整数值；s₀ = s₁ 当且仅当设计为对称型。（交谱区间特征）

The two versions are identical in content.

## The statement defines nothing, so a reading must be pinned

The file is a prose sentence. It introduces the names "combinatorial geometry",
"blocks", "intersection spectrum" and "symmetric" **without defining any of
them**, and it never says what `s_0` and `s_1` are. A disproof therefore has to
fix a reading. We adopted the only standard reading consistent with the
wording:

| Term in the file | Pinned reading |
|:-----------------|:---------------|
| combinatorial geometry | a block design: a finite point set `P` with a family `ℬ` of blocks (a set system) |
| blocks | the elements of `ℬ` |
| intersection spectrum | the set `S = { \|B ∩ B'\| : B, B' ∈ ℬ, B ≠ B' }` |
| `s_0`, `s_1` | `s_0 = min S`, `s_1 = max S` |
| symmetric | `b = \|ℬ\| = \|P\| = v` (equivalently `r = k` for 2-designs) |

Two remarks on why this reading is the right one and why the refutation is
robust:

1. Taking `s_0, s_1` to be the **minimum and maximum of the spectrum** is forced
   by the phrasing. The conjecture describes an "interval characterization"
   whose endpoints are `s_0, s_1`, and the second clause "`s_0 = s_1` iff
   symmetric" only has content if `s_0, s_1` are the two ends of `S`. Under
   this reading the second clause is in fact a genuine theorem for 2-designs
   (see below); it is its extension to 1-designs in the wording that is false.
2. The refutation of clause 1 does **not** depend on any looseness in the
   reading. The witness is a full `3-(8,4,1)` design — the strongest design
   hypothesis available here — so no "intended" strengthening of
   "combinatorial geometry" can rescue the claim.

## The witness: `AG(3,2)` and its 14 affine planes

Let `P = F_2^3` be the 8 points. For a nonzero normal vector `a` and
`b ∈ {0,1}` put

```
B_{a,b} = { x ∈ F_2^3 : a·x = b },   a·x = a_1 x_1 + a_2 x_2 + a_3 x_3  (mod 2).
```

There are `7 · 2 = 14` such affine planes. Encoding the point `(x_1,x_2,x_3)`
by the 8-bit mask with bit `x_1 + 2x_2 + 4x_3` set (so that bitwise `AND`
computes intersections), they are, sorted:

```
[15, 51, 60, 85, 90, 102, 105, 150, 153, 165, 170, 195, 204, 240]
```

Each has exactly 4 points. Since a line of `AG(3,2)` has only 2 points, no
three distinct points are collinear; hence any 3 points are affinely
independent and span a unique affine plane. Therefore:

* **`AG(3,2)` is a genuine `3-(8,4,1)` design**: all `C(8,3) = 56` triples lie
  in exactly one block (verified exhaustively).
* Parameter consistency: `v = 8`, `b = 14`, `k = 4`, `λ_3 = 1`,
  `λ_2 = (v-2)/(k-2) = 3`, `λ_1 = ((v-1)/(k-1))·λ_2 = 7`. So each point lies in
  7 blocks and each pair in 3 blocks (both verified exhaustively).

## The intersection spectrum of `AG(3,2)`: the 91-pair table

For two distinct blocks:

* if `a = a'` then the two planes are parallel and disjoint (`b ≠ b'`), so the
  intersection has size **0**; there are exactly 7 such pairs, one for each
  nonzero normal (the 7 parallel classes);
* if `a ≠ a'` then the planes meet in an affine line, which in `F_2^3` has
  exactly **2** points.

Hence over all `C(14,2) = 91` unordered pairs of distinct blocks:

| intersection size `m` | number of pairs with `\|B ∩ B'\| = m` | `m ∈ [s_0,s_1] = [0,2]`? |
|:---------------------:|:------------------------------------:|:------------------------:|
| 0 | 7  | yes |
| 1 | 0  | yes |
| 2 | 84 | yes |
| **total** | **91** | |

So the spectrum is

```
S = {0, 2},   s_0 = min S = 0,   s_1 = max S = 2,
```

while the integer interval is

```
[s_0, s_1] ∩ ℤ = {0, 1, 2}.
```

The value `1` lies in the conjectured interval and **never occurs**: `S` is a
strict subset of `[s_0,s_1]`, with `|S| = 2 < 3 = |[s_0,s_1] ∩ ℤ|`. The seven
disjoint pairs are exactly the seven parallel classes, in masks:

```
(15,240), (51,204), (60,195), (85,170), (90,165), (102,153), (105,150).
```

The full 14×14 intersection matrix (upper triangle; diagonal blank) has entry 2
everywhere except those seven positions, which are 0. In particular no two
planes of `AG(3,2)` meet in exactly one point.

**Clause 1 of the conjecture is therefore false.**

## Bonus: clause 2 also fails, for 1-designs

The Pasch configuration is the set system on `P = {1,…,6}` with blocks

```
{1,2,3},  {1,4,5},  {2,4,6},  {3,5,6}.
```

* It has `b = 4` blocks of size `k = 3` on `v = 6` points.
* Every point lies in exactly `r = 2` blocks: a `1-(6,3,2)` design.
* Every two distinct blocks meet in exactly one point, so `s_0 = s_1 = 1`.
* But `b = 4 ≠ 6 = v`, so it is **not symmetric**.

Hence the second clause ("`s_0 = s_1` if and only if the design is symmetric")
fails in the generality stated.

**To be fair:** for genuine **2-designs** the second clause *is* a theorem. If
a `2-(v,k,λ)` design has all pairwise block intersections equal to a constant
`μ`, then its incidence matrix satisfies `N Nᵀ = (k-μ)I + μJ`, whose
eigenvalues are `k-μ` (multiplicity `b-1`) and `k + μ(b-1) > 0`. If `b > v`
then `N Nᵀ` is singular (rank `= v < b`), forcing `k = μ`, i.e. any two
distinct blocks share all `k` points and are equal — impossible for `b > 1`.
So `b = v` (Fisher's inequality gives `b ≥ v`): the design is symmetric. Thus
clause 2 only fails because the wording says "design" rather than "2-design".
(We record this rather than overstate the refutation.)

## Files

| File | Description |
|:-----|:------------|
| `README.md` | This document: verdict, bilingual quote, pinned reading, `AG(3,2)` construction, 91-pair table, Pasch bonus, file list, reproduction, rule-3 status. |
| `main.tex` | LaTeX source of the disproof, standalone `article`; compiles with `tectonic --outdir build main.tex`. |
| `build/main.pdf` | PDF produced by that command. |
| `reproduce.py` | Python 3, standard library only: builds the 14 affine planes of `F_2^3`, verifies the `3-(8,4,1)` property, computes all 91 pairwise intersections and their size multiplicities, asserts the spectrum is `{0,2}` and that `1 ∈ [0,2]` is absent, and verifies the Pasch failure; prints `PASS`/`FAIL`, non-zero exit on failure. |
| `lean4/lean-toolchain` | Pins `leanprover/lean4:v4.33.1`. |
| `lean4/lakefile.toml` | Lake configuration: name `tlmc8434`, library `Main`, no dependencies. |
| `lean4/Main.lean` | Lean 4 formalisation, core Lean only (`import Std`, no Mathlib, no `sorry`). |
| `lean4/Check.lean` | `#print axioms` audit for every theorem. |
| `lean4/README.md` | Statement table, proof strategy, axiom audit, scope note. |

## Reproducing

Python (dependency-free, runs in well under a second):

```sh
python3 reproduce.py
```

It builds the planes from the affine equations (not from the hard-coded mask
list), asserts the generated masks equal the pinned list, verifies that all 56
triples have containment count 1, tabulates the 91-pair spectrum, asserts
`S = {0,2}` and `1 ∈ [0,2] \ S`, verifies the Pasch failure, prints `PASS`, and
exits `0`. A buggy check (the point `0` was tested as a mask rather than
`1 << 0`) was caught and fixed by this script during preparation.

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

`lake build` exits `0`; `Check.lean` prints `#print axioms` for every theorem
and reports no `sorryAx` (only `propext` for the structural results, and no
axioms at all for the pure `Nat` equalities). The Lean numbers agree with the
write-up exactly: block count 14, spectrum length 91, multiplicities 0:7, 1:0,
2:84.

## Status against the submission rules

Rule 3 requires each submission to contain the LaTeX source, a PDF document,
and a Lean 4 project.

* **LaTeX source** — present (`main.tex`), a standalone `article` using only
  `geometry`, `amsmath`, `amssymb`, `amsthm`, `array`, `parskip`, `booktabs`;
  compiles with `tectonic --outdir build main.tex`.
* **PDF document** — present at `build/main.pdf` (non-empty, produced by the
  command above; no CJK is used in the PDF, the Chinese quote lives in this
  README, so no `xeCJK`/`ctex` is needed).
* **Lean 4 project** — present under `lean4/`, with `lean-toolchain`
  (`leanprover/lean4:v4.33.1`), `lakefile.toml` (name `tlmc8434`, library
  `Main`), `Main.lean`, `Check.lean`, and a `README.md`. It encodes the 14
  blocks as 8-bit `Nat` masks, defines `pc` by a structural bit fold (there is
  no `Nat.popcount` in `import Std`), the spectrum by a structurally recursive
  function, and proves by kernel `decide` (with
  `set_option maxRecDepth 1000000`) that the block list has length 14, all
  blocks have popcount 4, every 3-subset lies in exactly one block, the
  spectrum has 91 entries with values only in `{0,2}`, the multiplicities are
  0:7 / 1:0 / 2:84, `s_0 = 0`, `s_1 = 2`, and the negation of the interval
  statement (`intervalFull = false`, `¬ IntervalSpectrum`). It also formalises
  the Pasch 1-design and its second-clause failure. It uses core Lean only and
  contains no `sorry`; the audit reports no `sorryAx`.

## Caveats

* **The file defines nothing** (no definition of "combinatorial geometry",
  "blocks", "intersection spectrum", "symmetric", `s_0`, `s_1`). We pinned the
  standard reading above. The clause-1 refutation is insensitive to this
  because the witness is a genuine 3-design.
* **Clause 2 is only false for 1-designs**; for 2-designs it is a theorem, as
  shown above. We state this explicitly rather than overstate the result.
* **Lean scope.** The Lean development certifies the finite combinatorial facts
  (design property, spectrum, absence of 1, negation of clause 1, Pasch
  failure). The general 2-design theorem is proved on paper in `main.tex` and
  is not formalised; it is not needed for the disproof.
* `AG(3,2)` is the unique `3-(8,4,1)` design; uniqueness is classical and is
  not needed — everything used is established directly by the finite checks.
