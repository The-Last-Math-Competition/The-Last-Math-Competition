# Disproof of conjecture `00000001070`

**Verdict: FALSE.**

This submission disproves conjecture `00000001070` as stated. The refutation is
unconditional and elementary: the three-element set `A = {0,1,3} ⊆ F_7` has
three-fold sum `3A = F_7`, while the conjectured formula returns `4`.

## The conjecture

> **Definition.** The three-fold sumset `A + A + A`, i.e. repetitions of
> summands are allowed.
> **Conjecture.** The smallest `|A|` with `3A = F_p` is `⌈(p+1)/3⌉ + 1`
> (the three-sum threshold).

Original statement as filed in `conjectures/00000001070.md`:

> **English.** Definition: The three-fold sumset A + A + A. Conjecture: The
> smallest |A| with 3A = F_p is ⌈(p+1)/3⌉ + 1 (the three-sum threshold).
>
> **中文。** 定义：三和集 A + A + A。猜想：F_p 中 3A = F_p 的最小 |A| 为
> ⌈(p+1)/3⌉ + 1(三和阈值)。

## The decisive counterexample: `p = 7`, `A = {0,1,3}`

The `3 × 3 × 3 = 27` ordered triples of `A = {0,1,3}` produce all seven
residues:

| `y` | representation `a + b + c` |
|----:|:---------------------------|
| 0 | 0 + 0 + 0 |
| 1 | 0 + 0 + 1 |
| 2 | 0 + 1 + 1 |
| 3 | 0 + 0 + 3 |
| 4 | 0 + 1 + 3 |
| 5 | 1 + 1 + 3 |
| 6 | 0 + 3 + 3 |

Thus `3A = {0,1,2,3,4,5,6} = F_7` with `|A| = 3`. The conjectured formula
gives

```
⌈(7+1)/3⌉ + 1 = ⌈8/3⌉ + 1 = 3 + 1 = 4 ≠ 3,
```

so the formula overestimates the threshold already at `p = 7`. No two-element
subset of `F_7` works (each of the `C(7,2) = 21` pairs has at most four distinct
three-fold sums), so the true minimum at `p = 7` is exactly `3`.

## Two different thresholds

There are two inequivalent readings of "smallest `|A|`". The conjecture uses
the first, but its formula comes from the second.

- **Existential (what the conjecture literally states).** The least `k` such
  that *some* `k`-element `A` satisfies `3A = F_p`. This grows like `(6p)^{1/3}`
  because `k` elements admit at most `C(k+2,3)` distinct three-fold sums.
- **Universal.** The least `k` such that *every* `k`-element `A` satisfies
  `3A = F_p`. By Cauchy–Davenport this is exactly `⌈(p+2)/3⌉`.

Cauchy–Davenport gives `|A+B| ≥ min(p, |A|+|B|−1)`, hence
`|3A| ≥ min(p, 3|A|−2)`. If `3|A|−2 ≥ p` then every `A` covers `F_p`; and for
`k < ⌈(p+2)/3⌉` the interval `{0,…,k−1}` has `|3A| = 3k−2 < p`, so it does not
cover. Therefore the universal threshold is `⌈(p+2)/3⌉`. The conjectured value
`⌈(p+1)/3⌉ + 1` equals it only when `p ≡ 2 (mod 3)`; it is too large by one at
`p = 3` and at every prime `p ≡ 1 (mod 3)` (for `p ≤ 30`: `3, 7, 13, 19`).

The existential minimum is much smaller and is *not* `⌈(p+2)/3⌉` either. An
exhaustive computation (`reproduce.py`) for all primes `p ≤ 30` gives:

| `p` | true existential min | conjecture `⌈(p+1)/3⌉+1` | universal `⌈(p+2)/3⌉` |
|----:|:--------------------:|:-------------------------:|:---------------------:|
| 2  | 2 | 2  | 2  |
| 3  | 2 | 3  | 2  |
| 5  | 3 | 3  | 3  |
| 7  | 3 | 4  | 3  |
| 11 | 4 | 5  | 5  |
| 13 | 4 | 6  | 5  |
| 17 | 5 | 7  | 7  |
| 19 | 5 | 8  | 7  |
| 23 | 5 | 9  | 9  |
| 29 | 6 | 11 | 11 |

For example, `A = {0,1,2,4}` of size `4` already covers `F_11`, while the
universal threshold is `⌈13/3⌉ = 5`. So the conjectured formula is the answer
to neither question: it is wrong existentially at
`p = 3, 7, 11, 13, 17, 19, 23, 29` and wrong universally at
`p = 3, 7, 13, 19`.

## Files

| File | Description |
|:-----|:------------|
| `README.md` | This document: verdict, witness, both thresholds, reproduction instructions. |
| `main.tex` | Standalone LaTeX source of the disproof. |
| `build/main.pdf` | PDF produced by `tectonic --outdir build main.tex`. |
| `reproduce.py` | Python 3 (standard library only): exhaustive computation of the true minima for all primes `p ≤ 30`, the explicit `p = 7` witness, comparison against both formulas, `PASS`/`FAIL`. |
| `lean4/lean-toolchain` | Pins `leanprover/lean4:v4.33.1`. |
| `lean4/lakefile.toml` | Lake configuration; library `Main`, no dependencies. |
| `lean4/Main.lean` | Lean 4 formalisation of the `p = 7` witness, core Lean only (`import Std`, no Mathlib, no `ZMod`, no `sorry`). |
| `lean4/Check.lean` | `#print axioms` audit for every theorem. |
| `lean4/README.md` | Statement table, proof strategy, and scope note for the formalisation. |

## Reproducing

```sh
python3 reproduce.py
```

It computes the true existential minimum `|A|` with `3A = F_p` for every prime
`p ≤ 30` (exhaustively; the counting bound `C(k+2,3) ≥ p` prunes small `k`),
prints the table against both formulas, prints the explicit three-fold sum of
the `p = 7` witness, and ends with `PASS`/`FAIL` (exit status `0` on `PASS`).

The LaTeX document is built with:

```sh
tectonic --outdir build main.tex
```

The Lean 4 project is built and audited with:

```sh
cd lean4
lake build
lake env lean Check.lean
```

The project uses the toolchain pinned in `lean4/lean-toolchain`
(`leanprover/lean4:v4.33.1`) and imports only `Std`; it does not depend on
Mathlib.
