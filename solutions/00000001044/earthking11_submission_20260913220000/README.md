# Disproof of conjecture `00000001044`

**Verdict: FALSE.**

This submission disproves conjecture `00000001044` as stated. The refutation is
unconditional, elementary, and complete at the smallest non-trivial witness
`(q, n) = (3, 2)`. At that witness the hypothesis `d = gcd(n, q²−1) > 1` holds
and `(q−1)/d = 1`, yet **all three** choices `a ∈ {0,1,2}` give a value set
whose complement has size `1`. Hence `a = 0` is not the unique minimiser, and
the other `a` do not give a strictly larger value set — they tie it. The two
clauses of the conjecture are also mutually inconsistent, and the numerical
formula `(q−1)/d`, as well as the claimed location `a = 0`, fail in further
examples.

## The conjecture

> **Definition:** the value set of the Dickson polynomial D_n(x,a) is its image
> over F_q. **Conjecture:** when gcd(n, q²−1) = d > 1 (the non-permutation
> case), the minimum size of the complement of the value set is (q−1)/d,
> attained at a = 0 (the monomial x^n); every other a gives a strictly larger
> value set.

Original statement (English and Chinese) as filed in
`conjectures/00000001044.md`:

> **English.** Definition: The value set of the Dickson polynomial
> `D_n(x,a)` is its image over `F_q`. Conjecture: When
> `gcd(n, q²−1) = d > 1` (the non-permutation case), the minimum size of the
> complement of the value set is `(q−1)/d`, attained at `a = 0` (the monomial
> `x^n`); every other `a` gives a strictly larger value set.
>
> **中文。** 定义：Dickson 多项式 `D_n(x,a)` 的值集指其在 `F_q` 上的像。
> 猜想：当 `gcd(n,q²−1)=d>1`（非置换情形）时，值集补集的最小尺寸为
> `(q−1)/d`，且该极值在 `a=0`（单项式 `x^n`）时取得；一切其他 `a` 给出严格
> 更大的值集。

The claim has two clauses:

- **(C1)** the minimum complement size equals `(q−1)/d` and is attained at
  `a = 0`;
- **(C2)** every other `a` gives a *strictly larger* value set.

Both fail at `(q,n) = (3,2)`; in fact (C1) and (C2) are mutually inconsistent
on their own.

## Setup

Dickson polynomials use the recursion
`D_0 = 2`, `D_1 = x`, `D_k = x·D_{k−1} − a·D_{k−2}` (k ≥ 2), so that
`D_2(x,a) = x² − 2a` and `D_3(x,a) = x³ − 3ax`. The *value set* is the image
`V_q(n,a) = {D_n(x,a) : x ∈ F_q} ⊆ F_q`, and the *complement size* is
`comp_q(n,a) = q − |V_q(n,a)|`.

## Primary counterexample: (q, n) = (3, 2)

Here `D_2(x,a) = x² − 2a` over `F_3`, and

- `d = gcd(n, q²−1) = gcd(2, 8) = 2 > 1`, so the conjecture's hypothesis holds;
- `(q−1)/d = (3−1)/2 = 1`, the conjectured minimum.

| `a` | `x ↦ D_2(x,a)` on `x = 0,1,2` | value set `V_3(2,a)` | `|V_3(2,a)|` | complement |
|:---:|:------------------------------|:--------------------:|:------------:|:----------:|
| 0 | `0, 1, 1` | `{0,1}` | 2 | **1** |
| 1 | `1, 2, 2` | `{1,2}` | 2 | **1** |
| 2 | `2, 0, 0` | `{0,2}` | 2 | **1** |

Every `a` gives complement `1` and value-set size `2`:

- `a = 0` is **not** the unique minimiser (`a = 1` and `a = 2` attain the same
  complement `1`), and
- neither `a = 1` nor `a = 2` gives a *strictly larger* value set than `a = 0`
  (all three value sets have size `2`).

This is a direct disproof of the conjecture as stated.

## The statement is internally inconsistent

Write `v(a) = |V_q(n,a)|`, so the complement size is `q − v(a)`. Clause (C1)
says `a = 0` minimises the complement, i.e. `q − v(0) ≤ q − v(a)`, equivalently
`v(a) ≤ v(0)`, for every `a`. Clause (C2) says every `a ≠ 0` has `v(a) > v(0)`.
The two requirements `v(a) ≤ v(0)` and `v(a) > v(0)` cannot both hold for any
`a ≠ 0`. So whenever `F_q` has more than one element, the conjecture as written
is unsatisfiable: a complement-minimiser whose other points *all* have strictly
larger value sets cannot exist. The plausible intended clause (C2) would have
been "every other `a` gives a strictly **smaller** value set" (a strictly larger
complement) — which the examples below also refute. At `(3,2)` the inconsistency
is explicit: `v(1) = v(0) = 2`, violating the strict inequality demanded by
(C2) while realising the minimum demanded by (C1).

## The same tie at (5, 2) and (7, 2)

For `n = 2`, `D_2(x,a) = x² − 2a`: the value set is the set of squares shifted
by `−2a`, and when `2` is invertible the shift ranges over all of `F_q` as `a`
does, so every `a` gives a translate of the same square set.

| `(q,n)` | `d = gcd(n, q²−1)` | `(q−1)/d` | complement sizes `comp_q(n,a)` | value-set sizes |
|:-------:|:------------------:|:---------:|:-------------------------------|:---------------:|
| `(5,2)` | `gcd(2,24) = 2` | `2` | `a = 0,1,2,3,4 : 2,2,2,2,2` | all `3` |
| `(7,2)` | `gcd(2,48) = 2` | `3` | `a = 0,…,6 : 3,3,3,3,3,3,3` | all `4` |

In both rows `d > 1` and the numerical value `(q−1)/d` is correct, but the
minimum is attained by *every* `a`, not uniquely by `a = 0`, and no `a` yields
a strictly larger value set — clause (C2) fails for an infinite family, not
just at `q = 3`.

## The reversal at (7, 3): `a = 0` is the worst choice

Here `D_3(x,a) = x³ − 3ax` over `F_7`, `d = gcd(3, 48) = 3 > 1`, and
`(q−1)/d = 6/3 = 2`.

| `a` | value set `V_7(3,a)` | `|V_7(3,a)|` | complement |
|:---:|:---------------------|:------------:|:----------:|
| 0 | `{0,1,6}` (the cubes) | 3 | **4** |
| 1 | `{0,2,3,4,5}` | 5 | 2 |
| 2 | `{0,2,3,4,5}` | 5 | 2 |
| 3 | `{0,1,3,4,6}` | 5 | 2 |
| 4 | `{0,2,3,4,5}` | 5 | 2 |
| 5 | `{0,1,3,4,6}` | 5 | 2 |
| 6 | `{0,1,3,4,6}` | 5 | 2 |

`a = 0` gives the **largest** complement, `4`, which strictly exceeds the
conjectured minimum `(q−1)/d = 2`, while every nonzero `a` gives the smaller
complement `2`. So `a = 0` maximises rather than minimises the complement: at
`(7,3)` the conjecture has the direction exactly backwards.

## Further breakages of the formula and of the "non-permutation" label

- **`(q,n) = (5,3)`.** `d = gcd(3,24) = 3 > 1`, but `d ∤ (q−1) = 4`, so
  `(q−1)/d = 4/3` is not an integer and cannot be a set size. Moreover
  `D_3(x,0) = x³` permutes `F_5` (since `gcd(3,5−1) = 1`), so
  `V_5(3,0) = F_5` and `comp_5(3,0) = 0`. In the very case the conjecture
  labels "non-permutation", the monomial `a = 0` is in fact a permutation
  polynomial, and the true minimum complement is `0`, not `(q−1)/d`.
- **`(q,n) = (5,4)`.** `d = gcd(4,24) = 4` and `(q−1)/d = 1`, but the true
  minimum complement is `2` (attained at `a = 2,3`), and no `a ∈ F_5` attains
  the claimed value `1`: `comp_5(4,a) = 3,3,2,2,3` for `a = 0,…,4`, with
  `comp_5(4,0) = 3`. So the numerical value `(q−1)/d` can fail outright.

## The torus-reading caveat

One might try to rescue the claim by reading "value set" on the norm-1 torus
(the subgroup of order `q+1` of `F_{q²}^×`) instead of over `F_q`. Under that
reading the monomial `a = 0` **is** the unique minimiser, so the "uniqueness at
`a = 0`" half of the claim survives in a qualified sense. But the minimum
complement there is `0`, not `(q−1)/d`: the value `(q−1)/d` is not what the
torus reading produces. Consequently that reading does not save the stated
formula either, and in any case it contradicts the conjecture's own definition,
which explicitly places the value set over `F_q`. The refutation above uses the
definition as written.

## Files

| File | Description |
|:-----|:------------|
| `README.md` | This document: verdict, quoted conjecture, counterexample, tables, inconsistency remark, caveat, reproduction, status. |
| `main.tex` | LaTeX source of the disproof. Standalone `article`, compiles with `tectonic main.tex`. |
| `build/main.pdf` | PDF produced by `tectonic -o build main.tex` (5 pages). |
| `reproduce.py` | Python 3 (standard library only) brute force over `F_q` for all `a`; prints `PASS`/`FAIL`, non-zero exit on failure. |
| `lean4/lean-toolchain` | Pins `leanprover/lean4:v4.33.1`. |
| `lean4/lakefile.toml` | Lake configuration; library `Main`, project `tlmc1044`, no dependencies. |
| `lean4/Main.lean` | Lean 4 formalisation, core Lean only (`import Std`, no Mathlib, no `sorry`). |
| `lean4/Check.lean` | `#print axioms` audit for every theorem. |
| `lean4/README.md` | Statement table, proof strategy, and scope note for the formalisation. |

## Reproducing

Python (dependency-free, runs in under a second):

```sh
python3 reproduce.py
```

It implements the Dickson recursion over the residues of `F_q`, computes the
complement size for every `a`, and **asserts** the `(3,2)` tie, the `(5,2)` and
`(7,2)` ties, and the `(7,3)` reversal (plus the `(5,3)`/`(5,4)` breakages). A
`FAIL` (non-zero exit status) means a claimed fact did not verify.

LaTeX document:

```sh
tectonic main.tex            # produces main.pdf in the current directory
tectonic -o build main.tex   # produces build/main.pdf (the submitted artifact)
```

Lean 4 project:

```sh
cd lean4
lake build
lake env lean Check.lean
```

## Status against the submission rules

The repository rules require each submission to include the LaTeX source code, a
PDF document, and a Lean 4 project.

- **LaTeX source** — present (`main.tex`), a standalone `article` using only
  `geometry`, `amsmath`, `amssymb`, `amsthm`, `array`, `parskip`, `booktabs`
  and `ctex` (the latter with `fontset=fandol`, so the build does not depend on
  host system fonts), and it compiles with `tectonic main.tex`.
- **PDF document** — present at `build/main.pdf`, produced by `tectonic` (5
  pages), including the bilingual quote, the refutation tables, the
  inconsistency remark, and the torus-reading caveat.
- **Lean 4 project** — present under `lean4/`, with `lean-toolchain`
  (`v4.33.1`), `lakefile.toml` (project `tlmc1044`, library `Main`),
  `Main.lean`, `Check.lean`, and a `README.md`. It formalises the concrete
  witness (`compSize 3 2 0 = compSize 3 2 1 = compSize 3 2 2 = 1`,
  `biggerValueSet 3 2 1 = false`, `biggerValueSet 3 2 2 = false`,
  `tieWithZero 3 2 = true`), the packaged disproof
  `conjecture_00000001044_false`, the `(5,2)`/`(7,2)` ties, the `(7,3)`
  reversal (`q7n3_a0_largest`, `q7n3_nonzero_beats`), and extra breakages at
  `(5,3)` and `(5,4)`. It uses core Lean only (no Mathlib) and contains no
  `sorry`; `lake env lean Check.lean` reports no `sorryAx` (the concrete
  computations depend on no axioms at all, and the two divisibility facts use
  only `propext`).
- **Reproducibility script** — `reproduce.py` (standard library only) prints
  `PASS` and exits `0` when every asserted fact verifies.
