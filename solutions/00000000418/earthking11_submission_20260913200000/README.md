# Disproof of conjecture `00000000418`

**Verdict: FALSE.**

This submission disproves conjecture `00000000418` as stated. The refutation is
already complete at weight `λ = (2,1)`, `n = 3`, and it is fatal under *each* of
the two readings of "lattice word" that the conjecture itself supplies. The two
readings are mutually inconsistent, and they fail the conjectured value in
opposite directions: `1` under the synonym reading, `0` under the strict
reading, against the claimed `1/3`.

## The conjecture

Quoted verbatim from `conjectures/00000000418.md`:

> **English.** Definition: A Yamanouchi (lattice) word of weight λ is a word in
> which, in every prefix, the occurrence counts of each letter form a partition;
> a lattice word is one appearing as the reading word of a standard tableau.
> Conjecture: The proportion of lattice words of weight λ among Yamanouchi words
> is exactly f^λ/n! · K^{-1}_{λ,λ}, and this ratio attains its maximum 1/2^{n−1}
> when λ is a rectangle.

> **中文。** 定义：权 λ 的 Yamanouchi(格子)词指每个前缀中字母 i 的出现次数构成分拆的词;格子词指出现在某标准表读词中的词。猜想：权 λ 的格子词在 Yamanouchi 词中的比例恰为 f^λ/n!·K^{-1}_{λ,λ},且该比值在 λ 取方框形状时达到最大值 1/2^{n−1}。

## Setup

A word `w = w₁w₂…wₙ` over the positive integers has **content** `μ` if letter
`i` occurs `μᵢ` times. A **Yamanouchi word of weight λ** is a word of content `λ`
such that in every prefix the counts `(c₁, c₂, …)` form a partition, i.e.
`c₁ ≥ c₂ ≥ …`. Here `n = |λ|`, `f^λ` is the number of standard Young tableaux
(SYT) of shape `λ`, and `K_{λ,μ}` is the Kostka number, the number of
semistandard Young tableaux (SSYT) of shape `λ` and content `μ`.

The classical bijection is

```
{SYT of shape λ}  <-->  {Yamanouchi words of weight λ},
```

sending an SYT `T` to the word `w(T)` whose `i`-th letter is the row index of
the cell containing the entry `i`. Hence the number of Yamanouchi words of
weight `λ` equals `f^λ`. For `λ = (2,1)` the two SYT are

```
1 2        1 3
3          2
```

with row-index words `112` and `121`.

## Refutation (A): "Yamanouchi (lattice)" is a synonym

The parenthetical in "Yamanouchi (lattice) word" identifies the two terms.
Under that identification the set of lattice words of weight `λ` **is** the set
of Yamanouchi words of weight `λ`, so the proportion is `1` for every `λ`,
while the conjectured value is `f^λ/(n!·K_{λ,λ})`.

At `λ = (2,1)` the words of content `(2,1)` over `{1,2}` are `112`, `121`, and
`211`. The prefix counts are:

| word | prefix 1 | prefix 2 | prefix 3 | Yamanouchi? |
|:----:|:--------:|:--------:|:--------:|:------------|
| `112` | (1,0) | (2,0) | (2,1) | **yes** |
| `121` | (1,0) | (1,1) | (2,1) | **yes** |
| `211` | (0,1) | (1,1) | (2,1) | **no** — `(0,1)` is not a partition |

So there are exactly **2** Yamanouchi words of weight `(2,1)`, namely `112` and
`121`, and both are lattice words under reading (A):

```
proportion(A) = 2/2 = 1.
```

Now compute the conjectured value.

* **`K_{λ,λ} = 1` for every λ.** The unique SSYT of shape and content `λ` is the
  superstandard one (every cell of row `i` contains `i`). Proof sketch: an SSYT
  of content `λ` has exactly `λ₁` letters `1`; no cell in a row `≥ 2` can
  contain a `1` (the cell above it would have to be `< 1`), so all `λ₁` of them
  fill the `λ₁` cells of row 1; delete row 1 and induct. Hence
  `K_{(2,1),(2,1)} = 1`, confirmed by brute force in `reproduce.py`.
* **`f^{(2,1)} = 2`.** The hook lengths of the three cells of `(2,1)` are
  `3, 1, 1`, so the hook-length formula gives
  `f^{(2,1)} = 3!/(3·1·1) = 6/3 = 2`. Equivalently there are exactly the two SYT
  above.
* **`n! = 3! = 6`.**

Therefore the conjectured value is

```
f^{(2,1)} / (3! · K_{(2,1),(2,1)}) = 2 / (6·1) = 1/3,
```

and

```
proportion(A) = 1  ≠  1/3 = 2/6.
```

Cross-multiplying `2/2` and `2/6`:

```
2·6 = 12  ≠  4 = 2·2.
```

**The maximum clause also fails under reading (A).** At `n = 3` the asserted
maximum is `1/2^{n−1} = 1/4`, but the proportion is `1 > 1/4`, so the asserted
"maximum" is exceeded.

## Refutation (B): a lattice word is the reading word of a standard tableau

Read the definition literally: a lattice word is a word that appears as the
reading word of a standard tableau. In a standard tableau the entries
`1, 2, …, n` each occur exactly once, so every reading word is a permutation of
`{1, …, n}` and has content `(1, 1, …, 1) = (1ⁿ)`. It can have weight `(2,1)`
only if `(2,1) = (1,1,1)`, which is false. Concretely, the two SYT of shape
`(2,1)` have entry reading words (rows bottom to top, left to right)

```
1 2        1 3
3     ->  312        2     ->  213
```

both of weight `(1,1,1) ≠ (2,1)`. Hence under reading (B) there is **no**
lattice word of weight `(2,1)`, and

```
proportion(B) = 0/2 = 0  ≠  1/3.
```

The two readings are therefore mutually inconsistent (Yamanouchi words may
repeat letters, reading words never do), and each is separately fatal to the
conjecture.

## The general failure

Because `K_{λ,λ} = 1` for every partition `λ`, the conjectured value
`f^λ/(n!·K_{λ,λ})` collapses to `f^λ/n!` for every `λ`. Meanwhile the proportion
of lattice words among Yamanouchi words is identically `1` under reading (A),
and the number of Yamanouchi words of weight `λ` equals `f^λ`. Since
`Σ_{λ⊢n} f^λ = n!` with `f^λ ≥ 1` and at least two shapes for `n ≥ 2`, one has
`f^λ < n!` for `n ≥ 2`; hence `1 ≠ f^λ/n!` for **every** `λ` of size `n ≥ 2`
(the case `n = 1` is the trivial `λ = (1)`, where both sides are `1`).

The maximisers of `f^λ/n!` — the probability that a uniform random permutation
has RSK shape `λ` — are generally **not** rectangles:

| n | maximising λ | f^λ | f^λ/n! |
|:-:|:------------|:---:|:------:|
| 3 | `(2,1)`      | 2   | 1/3    |
| 5 | `(3,1,1)`    | 6   | 1/20   |
| 6 | `(3,2,1)`    | 16  | 1/45   |

At `n = 3` the rectangle partitions are `(3)` and `(1,1,1)`, both with
`f^λ = 1` and `f^λ/n! = 1/6 < 1/3`; the maximum is attained at the
non-rectangle `(2,1)`, not at a rectangle and not at `1/4`. The only numerical
coincidence is `n = 2`, where `f^{(2)} = f^{(1,1)} = 1` and `1/2! = 1/2^{n−1}`,
but there the reading-(A) proportion is still `1 ≠ 1/2`, so the conjecture fails
at `n = 2` as well.

## Files

| File | Description |
|:-----|:------------|
| `README.md` | This document: verdict, the conjecture (English and Chinese), refutations (A) and (B), the `λ = (2,1)` table, the general failure, file list, reproduction commands, and the status against the submission rules. |
| `main.tex` | LaTeX source of the disproof. Standalone `article`; builds with `tectonic main.tex`. |
| `build/main.pdf` | PDF produced by `tectonic -o build main.tex` (≈96 KB). |
| `reproduce.py` | Python 3 (standard library only) exhaustive verification: enumerates the words of content `(2,1)`, classifies Yamanouchi words, lists the SYT reading words, computes `f^{(2,1)}` by hooks and `K_{(2,1),(2,1)}` by brute force, checks both proportions and the maximum clause, and extends everything to all partitions of size `n ≤ 6`. Prints `PASS`, exits `0`. |
| `lean4/lean-toolchain` | Pins `leanprover/lean4:v4.33.1`. |
| `lean4/lakefile.toml` | Lake configuration; project `tlmc418`, library `Main`, no dependencies. |
| `lean4/Main.lean` | Lean 4 formalisation, core Lean only (`import Std`, no Mathlib, no `sorry`). |
| `lean4/Check.lean` | `#print axioms` audit for every theorem. |
| `lean4/README.md` | Statement table, proof strategy, reading conventions, and scope note. |

## Reproducing

Numerical checks (fast; standard library only):

```sh
python3 reproduce.py
```

Observed tail of the output:

```
PASS: 99 checks verified.
Conjecture 00000000418 is FALSE as stated:
  (A) 'Yamanouchi (lattice)' is a synonym, so the proportion of
      lattice words among Yamanouchi words is 2/2 = 1 at (2,1),
      not f/(n!*K) = 2/(6*1) = 1/3; cross-multiplying, 12 != 4.
      Also 1 > 1/4 = 1/2^{n-1}, killing the maximum clause.
  (B) Reading words of standard tableaux are permutations of
      weight (1,1,1), so at weight (2,1) the proportion is 0/2 = 0
      != 1/3.
  General: K_{lambda,lambda} = 1 for all lambda, so the claimed
  value collapses to f^lambda/n!, whose maximisers at n = 3, 5, 6
  are the non-rectangles (2,1), (3,1,1), (3,2,1).
```

The script exits with status `0` on success and non-zero on any failed check.

LaTeX (the PDF lands at `build/main.pdf`):

```sh
tectonic -o build main.tex
```

Lean 4:

```sh
cd lean4
lake build
lake env lean Check.lean
```

The Lean project uses the toolchain pinned in `lean4/lean-toolchain`
(`leanprover/lean4:v4.33.1`) and imports only `Std`; it does not depend on
Mathlib.

## Status against the submission rules

Rule 3 requires each submission to contain the LaTeX source code, a PDF
document, and a Lean 4 project.

- **LaTeX source** — present (`main.tex`), a standalone `article` using only
  `geometry`, `amsmath`, `amssymb`, `amsthm`, `array`, `parskip`, and `xeCJK`
  (needed for the quoted Chinese original). It builds with `tectonic main.tex`.
- **PDF document** — present at `build/main.pdf` (≈96 KB, non-empty), built by
  `tectonic -o build main.tex`.
- **Lean 4 project** — present under `lean4/`, with `lean-toolchain`,
  `lakefile.toml`, `Main.lean`, and `Check.lean`. It is core Lean only
  (`import Std`, no Mathlib) and contains no `sorry`. It formalises: the
  Yamanouchi predicate and the exact count of two words of weight `(2,1)`
  (`112`, `121`; `211` excluded); the two standard tableaux of shape `(2,1)`
  and their reading words; the equality of the Yamanouchi words with the
  row-index readings (reading (A), proportion `2/2 = 1`); the fact that entry
  reading words have weight `(1,1,1)`, so reading (B) gives `0/2 = 0`;
  `f^{(2,1)} = 2`, `3! = 6`, `K_{(2,1),(2,1)} = 1`; the cross-multiplied
  contradiction `2·6 ≠ 2·2` (i.e. `12 ≠ 4`) for reading (A) and `0·6 ≠ 2·2`
  for reading (B); and `1/4 < 1` together with the reading-(A) proportion
  exceeding `1/4`.

### Acceptance gate results (observed in the assembly environment)

| Gate | Command | Result |
|:-----|:--------|:-------|
| a | `cd lean4 && lake build` | exits `0`; `Build completed successfully (3 jobs).` |
| b | `cd lean4 && lake env lean Check.lean` | exits `0`; every theorem reports `does not depend on any axioms` or `depends on axioms: [propext]`; **no `sorryAx`**, no Mathlib |
| c | `tectonic -o build main.tex` | exits `0`; `Writing build/main.pdf` (≈96 KB, non-empty). Plain `tectonic main.tex` also succeeds (it writes `main.pdf` in the current directory) |
| d | `python3 reproduce.py` | prints `PASS: 99 checks verified.`, exits `0` |

## Caveats

- The refutation is complete and elementary. It relies only on the standard
  identity `K_{λ,λ} = 1` (proved in `main.tex` and in this document), the
  hook-length formula, the bijection SYT ↔ Yamanouchi words, and the fact that
  reading words of standard tableaux are permutations.
- The Lean formalisation fixes the counterexample weight `(2,1)` (and the
  `n = 3` rectangle comparison). The general collapse `K_{λ,λ} = 1`, the
  identity `#Yamanouchi = f^λ`, and the `n = 3, 5, 6` maximiser statement are
  proved in `main.tex`/this README and verified exhaustively for all `n ≤ 6` in
  `reproduce.py`; a general Lean treatment would need a development of Young
  tableaux beyond core Lean.
- `main.tex` uses `xeCJK` to typeset the Chinese original of the conjecture;
  Tectonic downloads the Fandol fonts for it automatically on first build.
