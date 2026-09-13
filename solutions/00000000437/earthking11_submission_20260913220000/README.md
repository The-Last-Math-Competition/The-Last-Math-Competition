# Disproof of conjecture `00000000437`

**Verdict: FALSE.**

This submission disproves conjecture `00000000437` as stated. The numerical
formula in the conjecture (Witt's formula) is a true classical theorem; the
appended **parity clause** is false. The refutation is unconditional and
elementary: two powers of two, namely `n = 1` and `n = 2`, have different
parities, `L_1 = 2` and `L_2 = 1`, so the parity of `L_n` is not determined by
whether `n` is a power of two.

## The conjecture

Quoted verbatim from `conjectures/00000000437.md`:

> **English.** Definition: The shuffle algebra Sh(V) (tensor algebra with
> shuffle product). Conjecture: The n-th graded dimension of the Lie-primitive
> space of Sh(V) for dim V = 2 is (1/n)Σ_{d|n} μ(d)·2^{n/d} (Witt's formula),
> and its parity is determined explicitly by whether n is a power of 2.
>
> **中文。** 定义：shuffle 代数 Sh(V)(张量代数带 shuffle 积)。猜想：shuffle
> 代数 Sh(V) 的李代数本原空间的第 n 个分次维数在 dim V = 2 时为
> (1/n)Σ_{d|n} μ(d)·2^{n/d}(Witt 公式),其奇偶性由 n 是否为 2 的幂显式给出。

Write

```
L_n = (1/n) Σ_{d|n} μ(d) · 2^(n/d).
```

`L_n` counts the binary Lyndon words of length `n` (equivalently the aperiodic
binary necklaces of length `n`, equivalently the monic irreducible polynomials
of degree `n` over `F_2`); all of these satisfy the formula above. That formula
is **not** in dispute. The conjecture has two parts, and only the second fails:

1. **(Witt's formula, true.)** The `n`-th graded dimension equals `L_n`.
2. **(Parity clause, false.)** The parity of `L_n` "is determined explicitly
   by whether `n` is a power of 2."

## The value table, `n = 1` … `20`

`L_n` and its parity, together with the predicate "`n` is a power of two"
(under the standard convention `2^0 = 1`, so `n = 1` is a power of two):

| `n` | `L_n` | parity | power of 2? |
|----:|------:|:------:|:-----------:|
| 1  | 2     | even | yes |
| 2  | 1     | odd  | yes |
| 3  | 2     | even | no  |
| 4  | 3     | odd  | yes |
| 5  | 6     | even | no  |
| 6  | 9     | odd  | no  |
| 7  | 18    | even | no  |
| 8  | 30    | even | yes |
| 9  | 56    | even | no  |
| 10 | 99    | odd  | no  |
| 11 | 186   | even | no  |
| 12 | 335   | odd  | no  |
| 13 | 630   | even | no  |
| 14 | 1161  | odd  | no  |
| 15 | 2182  | even | no  |
| 16 | 4080  | even | yes |
| 17 | 7710  | even | no  |
| 18 | 14532 | even | no  |
| 19 | 27594 | even | no  |
| 20 | 52377 | odd  | no  |

The first twelve values `2, 1, 2, 3, 6, 9, 18, 30, 56, 99, 186, 335` are the
ones quoted in the task statement; they are reproduced by `reproduce.py`, which
checks all `n ≤ 60`.

The parity visible in the table does not track the power-of-two predicate:
`n = 1, 2` are both powers of two with parities even and odd; `n = 8, 16` are
powers of two with even parity; and `n = 6, 10, 12, 14` are not powers of two
yet have odd parity.

## The refutation

### The sharpest witness: `n = 1` and `n = 2`

```
L_1 = 1 · 2^1 / 1 = 2                    (even)
L_2 = (μ(1)·2^2 + μ(2)·2^1) / 2 = (4 − 2)/2 = 1   (odd)
```

Both `1 = 2^0` and `2 = 2^1` are powers of two, but `L_1` is even and `L_2` is
odd. Hence there is **no** function of the predicate "`n` is a power of two"
that returns the parity of `L_n`; the parity clause is false. This is the
smallest possible witness, and it does not depend on which explicit parity
formula the file had in mind (the file supplies none).

### The fallback witness: `n = 2` and `n = 8`

If one declines to count `1` as a power of two (some authors exclude `2^0`),
the refutation is unchanged, because the two proper powers of two `2` and `8`
already have different parities:

```
L_2 = 1                                  (odd)
L_8 = (2^8 − 2^4)/8 = (256 − 16)/8 = 30  (even)
```

So even under the restricted convention "powers of two are 2, 4, 8, 16, …",
parity is not determined by whether `n` is a power of two.

### The "if and only if" reading fails at `n = 6`

A natural sharpening of the clause is the equivalence "`L_n` is odd **iff** `n`
is a power of two". It is false in **both** directions:

- `n = 8` is a power of two, but `L_8 = 30` is even (likewise `n = 16`,
  `L_16 = 4080` even).
- `n = 6` is not a power of two, yet `L_6 = (64 − 8 − 4 + 2)/6 = 54/6 = 9` is
  odd.

So the "iff" reading also fails. The obstruction is intrinsic:
`6 = 2^1 · 3` has `v_2(6) = 1` and odd part `3` (squarefree).

## The true repaired characterisation

Parity is not a function of the power-of-two predicate alone, but it does have
an exact description, verified for all `n ≤ 60` by `reproduce.py`:

> Write `n = 2^a · m` with `m` odd (so `a = v_2(n)`). Then
> **`L_n` is odd if and only if `a ∈ {1, 2}` and `m` is squarefree.**

Equivalently: `L_n` is even for every odd `n`, and for even `n` the value `L_n`
is odd exactly when `v_2(n) ∈ {1,2}` and the odd part of `n` has no repeated
prime factor.

This is proved (not merely checked) in `main.tex`: from
`n·L_n = Σ_{d|n} μ(d)·2^(n/d)`, the unique squarefree divisor of `n` with the
smallest exponent is the largest one, `rad(n) = ∏_{p|n} p`, so
`v_2(n·L_n) = n/rad(n)` and therefore `v_2(L_n) = n/rad(n) − v_2(n)`. This
vanishes precisely when `v_2(n) ∈ {1,2}` and the odd part is squarefree.
(An independent numeric check of the criterion for all `n ≤ 60` is included in
`reproduce.py`.)

## Caveats

- **Witt's formula is true and is not being disproved.** The numerical part of
  the conjecture is a standard theorem. The verdict FALSE refers solely to the
  parity clause.
- **The parity clause is under-specified.** The file gives no explicit parity
  formula, only the assertion that parity "is determined explicitly by whether
  `n` is a power of 2". The refutation works under every faithful reading: the
  `(1,2)` witness defeats the functional reading, the `(2,8)` fallback defeats
  the restricted `1`-is-not-a-power-of-two reading, and `n = 6` defeats the
  iff reading.
- **Convention on `1`.** Under `2^0 = 1` the smallest witness is `(1,2)`; under
  the convention that `1` is not a power of two the smallest witness is
  `(2,8)`. The verdict is the same either way.
- **The repair is not cosmetic.** The corrected criterion uses
  `v_2(n) ∈ {1,2}` and squarefreeness of the odd part, which are independent of
  the power-of-two predicate.
- **Scope of the numerics.** `L_n` for `n ≤ 60` and the repaired criterion are
  checked by `reproduce.py`; the finite witnesses `L_1, L_2, L_6, L_8, L_24`
  and the parity statements are proved in core Lean in `lean4/Main.lean`.

## Files

| File | Description |
|:-----|:------------|
| `README.md` | This document: verdict, bilingual quote, table, witnesses, repaired criterion, caveats, reproduction, status. |
| `main.tex` | LaTeX source. Standalone `article` (with `ctex`/Fandol for the Chinese quote); compiles with `tectonic main.tex`. |
| `build/main.pdf` | PDF produced by `tectonic --outdir build main.tex` (7 pages). |
| `reproduce.py` | Python 3 standard library only: Möbius by factorisation, `L_n` for `n ≤ 60`, table, assertions, `PASS`/`FAIL`, non-zero exit on failure. |
| `lean4/lean-toolchain` | Pins `leanprover/lean4:v4.33.1`. |
| `lean4/lakefile.toml` | Lake configuration; package `tlmc437`, library `Main`, no dependencies. |
| `lean4/Main.lean` | Core-Lean formalisation (`import Std`, no Mathlib, no `sorry`, `decide` only). |
| `lean4/Check.lean` | `#print axioms` audit for every theorem. |
| `lean4/README.md` | Statement table, proof strategy, ascending-`minFac` pitfall note, scope. |

## Reproducing

Python (dependency-free, runs in under a second):

```sh
python3 reproduce.py
```

It computes `μ` by factorisation, evaluates `L_n` for `n ≤ 60`, asserts
`L_1 = 2`, `L_2 = 1`, `L_6 = 9`, that `1` and `2` are powers of two with
different parities, the `(2,8)` fallback, the `n = 6` iff-violation, and the
repaired characterisation for all `n ≤ 60`. A `FAIL` (non-zero exit status)
means a claimed fact did not verify.

LaTeX document:

```sh
tectonic --outdir build main.tex      # produces build/main.pdf
# or simply: tectonic main.tex        # produces main.pdf
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
  `geometry`, `ctex` (Fandol fonts, for the Chinese quote), `amsmath`,
  `amssymb`, `amsthm`, `array`, `parskip`, and `booktabs`; it compiles with
  `tectonic main.tex`.
- **PDF document** — present at `build/main.pdf` (7 pages, ~93 KiB), produced
  by `tectonic --outdir build main.tex`, the same location as the template
  submission.
- **Lean 4 project** — present under `lean4/` with `lean-toolchain`
  (`leanprover/lean4:v4.33.1`), `lakefile.toml` (package `tlmc437`),
  `Main.lean`, `Check.lean`, and a `README.md`. It formalises `witt 1 = 2`,
  `witt 2 = 1`, `witt 6 = 9`, `witt 8 = 30`, `witt 24 = 698870`, the
  power-of-two flags `isPow2 1 = isPow2 2 = true`, `isPow2 6 = false`, the
  parity witnesses `witt 1 % 2 ≠ witt 2 % 2` and `witt 2 % 2 ≠ witt 8 % 2`,
  the negated functional reading, and the collected
  `conjecture_00000000437_false`. It uses core Lean only (no Mathlib), contains
  no `sorry`, and uses `decide` (never `native_decide`), so the `#print axioms`
  audit reports neither `sorryAx` nor `Lean.ofReduceBool`.
