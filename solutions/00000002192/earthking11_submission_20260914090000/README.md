# Disproof of conjecture `00000002192`

**Verdict: FALSE.**

This submission disproves conjecture `00000002192` as stated. The refutation is
unconditional, completely elementary, and fits on one line: the standard example
`S_2` is a height-2 poset on `n = 4` elements whose order dimension is **exactly
2**, whereas the conjecture predicts `⌈log₂ log₂ 4⌉ = 1`. The conjecture says the
bound "follows from the deep nesting of standard examples of random posets", and
it is precisely the standard example that refutes it.

## The conjecture

Quoted verbatim from `conjectures/00000002192.md`:

> **English.** Definition: The dimension of a poset is the minimal number of
> linear extensions whose intersection is the poset. Conjecture: The maximal
> dimension of height-2 posets is ⌈log₂ log₂ n⌉ (exact); the bound follows from
> the deep nesting of standard examples of random posets.
>
> **中文。** 定义：偏序的维数指线性扩展的交的最小个数。猜想：高度 2 的偏序的
> 最大维数为 ⌈log₂ log₂ n⌉(精确);界由随机偏序的标准例子的深嵌套。

## `n` is never defined

The statement is ill-posed before it is false. The symbol `n` is never
introduced: it is not the number of elements, the number of minimal elements,
the width, the rank, or anything else. We show that the claim fails under
**every** natural reading.

| Reading of `n` | Counterexample | Formula | Truth |
|:---------------|:---------------|:--------|:------|
| number of elements `|P|` | `S_2` on `n = 4` elements | `⌈log₂ log₂ 4⌉ = 1` | `dim = 2` |
| number of minimal elements | `S_k` has `k` minimal elements and `dim = k` | `⌈log₂ log₂ k⌉ < k` for `k ≥ 2` | `dim = k` |
| width (largest antichain) | `S_k` has width `k` and `dim = k` | `⌈log₂ log₂ k⌉ < k` for `k ≥ 2` | `dim = k` |
| rank / height | every `S_k` has height `2` | `⌈log₂ log₂ 2⌉ = 0` | `dim = k` unbounded |

So no choice of `n` saves the conjecture. The primary, most natural witness is
the first row.

## The witness `S_2`

For `k ≥ 1` the **standard example** `S_k` is the height-2 poset with `k`
minimal elements `a_0, …, a_{k-1}` and `k` maximal elements `b_0, …, b_{k-1}`,
and relations

```
a_j < b_i   ⇔   i ≠ j .
```

For `k = 2` take the four elements `0, 1` (minimal) and `2, 3` (maximal) with
the two relations

```
0 < 3        and        1 < 2 .
```

This poset `S_2` has:

- **height 2**: the chain `0 < 3` exists, and no chain of three elements exists
  (the only relations are the disjoint pairs `0 < 3` and `1 < 2`, so no `x` can
  be both above one relation and below another);
- **dimension exactly 2**.

### Two linear extensions whose intersection is `S_2`

```
L₁ = [0, 3, 1, 2]        order:  0 < 3 < 1 < 2
L₂ = [1, 2, 0, 3]        order:  1 < 2 < 0 < 3
```

Both respect `0 < 3` and `1 < 2`. Their intersection is the set of comparisons
that hold in both orders:

- the pair `{0, 1}` is ordered `0 < 1` in `L₁` but `1 < 0` in `L₂`;
- the pair `{2, 3}` is ordered `3 < 2` in `L₁` but `2 < 3` in `L₂`;
- `0 < 3` and `1 < 2` hold in both.

Hence the intersection is exactly `{(0, 3), (1, 2)} = S_2`, so `dim(S_2) ≤ 2`.

### No single linear extension realises `S_2`, so `dim(S_2) = 2`

A single linear extension is a total order, so it must decide the pair
`{0, 1}`: either `0 < 1` or `1 < 0`. But both `0 < 1` and `1 < 0` are false in
`S_2` (they are incomparable), so in either case the single extension makes a
comparison that is **not** in the poset. Therefore no one extension suffices,
`dim(S_2) ≥ 2`, and together with the upper bound

```
dim(S_2) = 2 .
```

### The contradiction

```
height(S_2) = 2,      n = |S_2| = 4,      dim(S_2) = 2,
conjectured value = ⌈log₂ log₂ 4⌉ = ⌈log₂ 2⌉ = 1,      2 ≠ 1 .
```

The conjectured value is strictly too small, so the conjecture is false.

## The whole family `S_k` refutes the claim

The classical result (Dushnik–Miller) is `dim(S_k) = k`. The lower bound is
worth recording because the conjecture explicitly invokes "the deep nesting of
standard examples":

- In a realizer, for each `i` the incomparable pair `{a_i, b_i}` must be
  reversed by some extension `L` with `b_i <_L a_i`; otherwise `a_i < b_i`
  would lie in the intersection.
- One extension cannot reverse two pairs `{a_i, b_i}` and `{a_j, b_j}` with
  `i ≠ j`: since `i ≠ j`, the relations `a_i < b_j` and `a_j < b_i` hold, and
  `b_j <_L a_j`, `b_i <_L a_i` would give the cycle
  `a_i < b_j < a_j < b_i < a_i` in `L` — impossible.
- So each extension handles at most one `i`, and at least `k` extensions are
  needed. The `k` extensions
  `L_i = [a_j (j ≠ i)] ++ [b_i] ++ [a_i] ++ [b_j (j ≠ i)]` match this bound.
  Hence `dim(S_k) = k`.

For every `k ≥ 2`, `S_k` has height 2 and `2k` elements, and
`dim(S_k) = k > ⌈log₂ log₂ (2k)⌉`. So the standard example refutes the claim for
**every** `k ≥ 2`, not just `k = 2`.

## Even smaller witnesses

| Poset | elements | height | dimension | formula | mismatch |
|:------|:--------:|:------:|:---------:|:--------|:---------|
| `2`-element chain | `2` | `2` | `1` | `⌈log₂ log₂ 2⌉ = 0` | yes |
| `V` (two minima below one maximum) | `3` | `2` | `2` | `⌈log₂ log₂ 3⌉ = 1` | yes |
| `S_2` | `4` | `2` | `2` | `⌈log₂ log₂ 4⌉ = 1` | yes |

The `2`-chain even breaks the formula before `n = 4`: the formula returns `0`,
which is impossible for a non-empty poset (the dimension of any poset is at
least `1`).

## The true growth is linear, not doubly logarithmic

The maximum dimension of a height-2 poset on `n` elements is

```
max dim = ⌊n/2⌋      for n ≥ 4,
```

by Hiraguchi's bound `dim(P) ≤ |P|/2` together with `dim(S_k) = k` (so
`S_{⌊n/2⌋}` attains it). The small cases are `n = 2` (antichain: `dim = 2`) and
`n = 3` (`V`: `dim = 2`), which is why `n ≥ 4` is required.

### Exhaustive verification for `n ≤ 6`

`reproduce.py` enumerates **all** labelled posets of height `≤ 2` on `n`
elements for `n = 1, …, 6` (via minimal-only / maximal-only / isolated
classification and all relation subsets), de-duplicates them, and computes the
exact order dimension of each by a bitmask search over tuples of linear
extensions. The result:

| `n` | number of height-`≤2` posets | true max dim | formula `⌈log₂ log₂ n⌉` |
|:---:|:---------------------------:|:------------:|:-----------------------:|
| 1 | 1 | 1 | undefined (`log₂ log₂ 1`) |
| 2 | 3 | **2** | 0 |
| 3 | 13 | **2** | 1 |
| 4 | 87 | **2** | 1 |
| 5 | 841 | **2** | 2 |
| 6 | 11643 | **3** | 2 |

The true maximum is `1, 2, 2, 2, 2, 3` while the formula is `0, 1, 1, 2, 2`;
they agree only at `n = 5`, by coincidence. (The number of *distinct* labelled
posets of height `≤ 2` grows quickly; the raw enumeration produces them with
multiplicity and is de-duplicated before counting.)

### Asymptotic comparison

| `n` | true max `⌊n/2⌋` | formula `⌈log₂ log₂ n⌉` |
|----:|:----------------:|:-----------------------:|
| `8` | 4 | 2 |
| `16` | 8 | 2 |
| `1024` | 512 | 4 |
| `10^6` | 500000 | 5 |

The true maximum is linear in `n`, the conjectured value is doubly logarithmic
(iterated logarithm); the gap diverges.

## Files

| File | Description |
|:-----|:------------|
| `README.md` | This document: verdict, bilingual quote, the `n`-undefined remark, the `S_2` / `S_k` / chain / `V` witnesses, the true `⌊n/2⌋` value with the exhaustive and asymptotic tables, file list, reproduction commands, and the status against the submission rules. |
| `main.tex` | LaTeX source of the disproof (standalone `article`), compiles with `tectonic --outdir build main.tex`. |
| `build/main.pdf` | PDF produced by `tectonic --outdir build main.tex`. |
| `reproduce.py` | Python 3 (standard library only): exact dimension of `S_2, S_3, S_4` by bitmask tuple search, the `S_2` realizer and the "no single extension" check, the chain and `V` witnesses, exhaustive height-`≤2` enumeration for `n ≤ 6`, the formula comparison, `PASS`/`FAIL`, non-zero exit on failure. |
| `lean4/lean-toolchain` | Pins `leanprover/lean4:v4.33.1`. |
| `lean4/lakefile.toml` | Lake configuration; library `Main` in package `tlmc2192`, no dependencies. |
| `lean4/Main.lean` | Lean 4 formalisation (core Lean only, `import Std`, no Mathlib, no `sorry`): `S_2` on `Fin 4`, linear extensions, realizers, `DimEq 2`, `HeightTwo`, and `conjecture_00000002192_false`. |
| `lean4/Check.lean` | `#print axioms` audit for every theorem. |
| `lean4/README.md` | Statement table, proof strategy, the integer reading of the formula, axis scope note. |

## Reproducing

Python (dependency-free, runs in about fifteen seconds):

```sh
python3 reproduce.py
```

It performs an exact, exhaustive computation and prints `PASS` with exit code
`0` exactly when every check holds:

- `dim(S_k) = k` for `k = 2, 3, 4` by a bitmask search over tuples of linear
  extensions (branch and bound, exact);
- the two extensions `[0,3,1,2]`, `[1,2,0,3]` intersect to `S_2`, and no single
  extension does;
- the `2`-chain (`dim 1`, formula `0`) and the `V` poset (`dim 2`, formula `1`);
- exhaustive maximum dimensions `1, 2, 2, 2, 2, 3` over all height-`≤2` posets
  on `n = 1, …, 6`, against the formula `0, 1, 1, 2, 2` for `n = 2, …, 6`;
- the asymptotic table `n = 8, 16, 1024, 10^6`.

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
and reports no `sorryAx`.

## Status against the submission rules

Rule 3 requires each submission to contain the LaTeX source, a PDF document,
and a Lean 4 project.

- **LaTeX source** — present (`main.tex`), a standalone `article` using only
  `geometry`, `amsmath`, `amssymb`, `amsthm`, `array`, `parskip`, `booktabs`;
  compiles with `tectonic --outdir build main.tex`.
- **PDF document** — present at `build/main.pdf`.
- **Lean 4 project** — present under `lean4/`, with `lean-toolchain` pinned to
  `leanprover/lean4:v4.33.1`, `lakefile.toml` (package `tlmc2192`, library
  `Main`, no dependencies), `Main.lean`, `Check.lean` (`#print axioms`), and
  `README.md`. It formalises the `S_2` witness end to end: the two linear
  extensions whose intersection is `S_2`, the impossibility of a single
  extension, `HeightTwo`, `DimEq 2`, the formula value `1` at `n = 4`, and the
  collected theorem `conjecture_00000002192_false`. It uses core Lean only (no
  Mathlib) and contains no `sorry`; the audit reports no `sorryAx`.

## Caveats

- The conjecture never defines `n`. The refutation is stated for the natural
  reading `n = |P|`; the family `S_k` also refutes the minimal-element, width,
  and rank readings, and the height/rank reading is refuted by any `S_k` with
  `k ≥ 2`.
- The exact value `⌊n/2⌋` is quoted for `n ≥ 4`; the exceptional cases `n = 2`
  (antichain) and `n = 3` (`V`) have maximum dimension `2`, which is only
  larger than `⌊n/2⌋` and thus strengthens the refutation.
- The Lean formalisation proves the contradiction at `n = 4` (the specific
  value the conjecture gets wrong), not the general `⌊n/2⌋` theorem; the latter
  is classical (Dushnik–Miller / Hiraguchi) and is stated in prose.
- Core Lean has no real logarithm, so `⌈log₂ log₂ 4⌉ = 1` is formalised as the
  exact integer iterated logarithm `Nat.log2 (Nat.log2 4) = 1`; at `n = 4` the
  integer and real readings coincide.
