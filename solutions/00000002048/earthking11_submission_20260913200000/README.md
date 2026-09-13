# Disproof of conjecture `00000002048`

**Verdict: FALSE.**

This submission disproves conjecture `00000002048` as stated. The refutation is
unconditional and elementary: the conjecture's main claim fails already at the
smallest non-trivial prime, `p = 5`, for `A = {0,1} ⊂ F_5`. A general family
shows the failure is systematic and explains why Cauchy–Davenport cannot rescue
the claim.

## The conjecture

> **Definition:** The 3-fold sum of F_p is the coverage of `{x+y+z : x, y, z ∈ A}`.
> **Conjecture:** For `|A| > (p−1)/3`, the 3-fold sum covers `F_p ∖ {0}` (the
> threshold is exact); the threshold is optimal (attained critically by the
> cubic-residue set at the threshold).

Original statement (English and Chinese) as filed in
`conjectures/00000002048.md`:

> **English.** Definition: The 3-fold sum of F_p is the coverage of
> `{x+y+z : x, y, z ∈ A}`. Conjecture: For `|A| > (p−1)/3`, the 3-fold sum
> covers `F_p ∖ {0}` (the threshold is exact); the threshold is optimal
> (attained critically by the cubic-residue set at the threshold).
>
> **中文。** 定义：F_p 的 3-项和指 `{x+y+z : x,y,z\in A}` 的覆盖范围。猜想：
> `|A| >(p-1)/3` 的 A 的 3-项和覆盖 `F_p \setminus {0}`(阈值精确);阈值为最优
> (由三次剩余集在阈值处达到临界)。

## The counterexample

Take `p = 5` and `A = {0, 1} ⊂ F_5`. Then

- `|A| = 2 > 4/3 = (5−1)/3`, so the conjecture's hypothesis holds strictly;
- `3A = {0+0+0, 0+0+1, 0+1+1, 1+1+1} = {0,1,2,3}` (no reduction mod 5 occurs,
  since all sums are `< 5`);
- `4 ∉ 3A`, and `4` is a nonzero element of `F_5`.

Hence `3A = {0,1,2,3}` does **not** cover `F_5 ∖ {0} = {1,2,3,4}`. The main
claim of the conjecture fails at `p = 5`, and the threshold is not exact.

## The general family

For every prime `p ≡ 2 (mod 3)`, put

```
A = {0, 1, …, (p−2)/3} ⊂ F_p,      |A| = (p+1)/3 > (p−1)/3.
```

Writing `p = 3k + 2`, we have `A = {0,…,k}` and every `x,y,z ∈ A` satisfies
`0 ≤ x+y+z ≤ 3k = p−2 < p`. No reduction mod `p` occurs, and every residue in
`{0,…,p−2}` is a sum `a+b+c` with `a,b,c ∈ A` (take `a = min(t,k)`, then split
`t−a` similarly). Therefore

```
3A = {0, 1, …, p−2},     and     p − 1 ∉ 3A.
```

Since `p−1 ≠ 0` in `F_p`, the element `p−1 ∈ F_p ∖ {0}` is never covered:
the conjecture fails for every such prime. This was verified by brute force for
`p = 5, 11, 17, 23, 29, 41, 47, 53, 59, 71, 83, 89`, and in fact for every
prime `p ≤ 100` with `p ≡ 2 (mod 3)`.

**Why Cauchy–Davenport does not save the claim.** Cauchy–Davenport gives
`|3A| ≥ min(p, 3|A| − 2)`. At the family's size `|A| = (p+1)/3`, this bound is
`3|A| − 2 = p − 1 < p`: it certifies only that at most one residue can be
missing, and for this family the missing residue is exactly `p−1`. The bound is
sharp yet strictly weaker than full coverage, so it cannot force the
conjecture's conclusion. (The conjecture also claims optimality is attained by
the cubic-residue set; the interval family above, which is far from a
cubic-residue set for `p > 5`, already violates coverage at the threshold.)

## The 3-fold sum for `p = 5, 11, 17`

| `p` | `A` | `|A|` | `(p−1)/3` | `3A` | missing |
|----:|:----|:-----:|:---------:|:-----|:-------:|
| 5 | `{0,1}` | 2 | `4/3` | `{0,1,2,3}` | 4 |
| 11 | `{0,1,2,3}` | 4 | `10/3` | `{0,…,9}` | 10 |
| 17 | `{0,…,5}` | 6 | `16/3` | `{0,…,15}` | 16 |

In every row `|A| > (p−1)/3`, yet `3A = {0,…,p−2}` misses the nonzero residue
`p−1`.

## Files

| File | Description |
|:-----|:------------|
| `README.md` | This document: verdict, quoted conjecture, counterexample, general family, table, reproduction, status. |
| `main.tex` | LaTeX source of the disproof. Standalone `article`, compiles with `tectonic main.tex`. |
| `build/main.pdf` | PDF produced by `tectonic main.tex` (the artifact is placed in `build/`). |
| `reproduce.py` | Python 3 (standard library only) brute force: `3A` for the witness and the general family up to `p ≤ 100`; prints `PASS`/`FAIL`, non-zero exit on failure. |
| `lean4/lean-toolchain` | Pins `leanprover/lean4:v4.33.1`. |
| `lean4/lakefile.toml` | Lake configuration; library `Main`, no dependencies. |
| `lean4/Main.lean` | Lean 4 formalisation, core Lean only (`import Std`, no Mathlib, no `sorry`). |
| `lean4/Check.lean` | `#print axioms` audit for every theorem. |
| `lean4/README.md` | Statement table, proof strategy, and scope note for the formalisation. |

## Reproducing

Python (dependency-free, runs in under a second):

```sh
python3 reproduce.py
```

It enumerates all triples for `p = 5`, `A = {0,1}`, asserts `3A = {0,1,2,3}`,
`4 ∉ 3A` and `|A| = 2 > 4/3`, then repeats the check for `A = {0,…,(p−2)/3}`
for every prime `p ≤ 100` with `p ≡ 2 (mod 3)`. A `FAIL` (non-zero exit status)
means a claimed fact did not verify.

LaTeX document:

```sh
tectonic main.tex
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

- **LaTeX source** — present (`main.tex`), a standalone `article` that uses only
  `geometry`, `amsmath`, `amssymb`, `amsthm`, `array`, `parskip`, and
  `booktabs`, and compiles with `tectonic main.tex`.
- **PDF document** — present at `build/main.pdf`, produced by
  `tectonic main.tex` and moved into `build/` (the same location as the
  template submission).
- **Lean 4 project** — present under `lean4/`, with `lean-toolchain`,
  `lakefile.toml`, `Main.lean`, `Check.lean`, and a `README.md`. It formalises
  the concrete witness (`sum3 5 witnessA = [0,1,2,3]`,
  `(sum3 5 witnessA).contains 4 = false`,
  `coversNonzero 5 witnessA = false`), the general family
  (`family_not_cover`, `family_threshold`, `general_family_refutes`), and the
  Cauchy–Davenport arithmetic (`cauchy_davenport_at_threshold`). It uses core
  Lean only (no Mathlib) and contains no `sorry`;
  `lake env lean Check.lean` reports no `sorryAx` for any theorem.
