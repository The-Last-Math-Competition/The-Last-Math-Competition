# Disproof of conjecture `00000000443`

**Verdict: FALSE.**

This submission disproves conjecture `00000000443` as stated. There are two
**independent** failures, either of which alone refutes the conjecture:

- **(A) The inequality itself is false for every `n >= 4`.** It first fails at
  `n = 4`: the exact dimension is `dim L_4 = 3`, while the claimed bound is
  `2^3 - 2^2 = 4`, so `3 < 4`.
- **(B) The prime-gap formula is false at `n = 3, 7, 11`.** The conjecture claims
  the gap is *exactly* half of `2^((n-1)/2)`; the actual gaps are `2, 30, 774`
  against claimed `1, 4, 16`. The formula coincidentally holds at `n = 5`, and is
  not even integral at `n = 2`.

The exact dimensions are the standard ones, given by Witt's formula; the disproof
is pure arithmetic and uses no structure theory. Note the prompt's aside that the
inequality "holds only at `n = 2` (`dim 1 >= 1`)": recomputing,
`2^(2-1) - 2^ceil(2/2) = 2 - 2 = 0`, so the correct statement is `dim L_2 = 1 >= 0`.
The inequality holds at `n = 2` and `n = 3` and fails from `n = 4` onward.

## The conjecture

> **English.** Definition: The n-th homogeneous dimension of the free Lie algebra
> L(V) is given by Witt's formula (1/n)Σ_{d|n}μ(d)k^{n/d}. Conjecture: For k = 2 and
> all n ≥ 2, dim L_n ≥ 2^{n−1} − 2^{⌈n/2⌉}, and for n prime the gap between this
> bound and the exact value is exactly half of 2^{(n−1)/2}.
>
> **中文。** 定义：自由李代数 L(V) 的第 n 齐次分量维数由 Witt 公式
> (1/n)Σ_{d|n}μ(d)k^{n/d} 给出。猜想：对 k=2 与一切 n≥2,
> dim L_n ≥ 2^{n−1}−2^{⌈n/2⌉},且该下界在 n 为素数时与精确值之差恰为
> 2^{(n−1)/2} 的一半。

Original statement as filed in `conjectures/00000000443.md`.

## Setup: Witt's formula

Witt's formula gives the dimension of the degree-`n` part of the free Lie algebra
on `k` generators:

$$\dim L_n = \frac{1}{n}\sum_{d \mid n} \mu(d)\, k^{\,n/d}.$$

We use `k = 2`, so `dim L_n = (1/n)·Σ_{d|n} μ(d)·2^{n/d}`. The Möbius values used
are `μ(1)=1`, `μ(2)=−1`, `μ(3)=−1`, `μ(4)=0`, `μ(6)=1`, `μ(12)=0`, etc.

## Exact dimensions

| `n` | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 |
|----:|--:|--:|--:|--:|--:|--:|--:|--:|--:|---:|---:|---:|
| `dim L_n` | 2 | 1 | 2 | 3 | 6 | 9 | 18 | 30 | 56 | 99 | 186 | 335 |

Worked example, `n = 4`: divisors `1, 2, 4`, so
`dim L_4 = (1/4)(1·2^4 + (−1)·2^2 + 0·2^1) = (1/4)(16 − 4) = 3`.

## The claimed bound

The conjectured bound is `B(n) = 2^{n−1} − 2^{⌈n/2⌉}`.

| `n` | `dim L_n` | `B(n)` | `dim L_n >= B(n)`? |
|----:|----------:|-------:|:-------------------|
| 1  | 2   | `2^0 − 2^1 = −1`     | yes |
| 2  | 1   | `2^1 − 2^1 = 0`      | yes |
| 3  | 2   | `2^2 − 2^2 = 0`      | yes |
| 4  | 3   | `2^3 − 2^2 = 4`      | **no** |
| 5  | 6   | `2^4 − 2^3 = 8`      | **no** |
| 6  | 9   | `2^5 − 2^3 = 24`     | **no** |
| 7  | 18  | `2^6 − 2^4 = 48`     | **no** |
| 8  | 30  | `2^7 − 2^4 = 112`    | **no** |
| 9  | 56  | `2^8 − 2^5 = 224`    | **no** |
| 10 | 99  | `2^9 − 2^5 = 480`    | **no** |
| 11 | 186 | `2^10 − 2^6 = 960`   | **no** |
| 12 | 335 | `2^11 − 2^6 = 1984`  | **no** |

The inequality holds at `n = 2, 3` and fails for **every** `n` in `[4, 12]`.

## Failure (A): the inequality is false for every `n >= 4`

Since `dim L_4 = 3` and `B(4) = 2^3 − 2^2 = 4`, we have `3 < 4`, so the universally
quantified inequality fails at `n = 4`. A single counterexample refutes a universal
statement. In fact the bound fails throughout the tested range:

| `n` | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 |
|----:|--:|--:|--:|--:|--:|--:|--:|--:|--:|
| `dim L_n` | 3 | 6 | 9 | 18 | 30 | 56 | 99 | 186 | 335 |
| `B(n)` | 4 | 8 | 24 | 48 | 112 | 224 | 480 | 960 | 1984 |
| fails? | yes | yes | yes | yes | yes | yes | yes | yes | yes |

## Failure (B): the prime-gap formula is false at `n = 3, 7, 11`

The conjecture additionally asserts that for prime `n` the gap between the bound and
the exact value equals exactly `(1/2)·2^{(n−1)/2}`.

| prime `n` | `dim L_n` | `B(n)` | actual gap \|`B−dim`\| | claimed `(1/2)2^{(n−1)/2}` | holds? |
|----------:|----------:|-------:|---------------------:|---------------------------:|:-------|
| 2  | 1   | 0   | 1   | not an integer | ill-defined |
| 3  | 2   | 0   | 2   | 1   | **no** |
| 5  | 6   | 8   | 2   | 2   | yes (coincidence) |
| 7  | 18  | 48  | 30  | 4   | **no** |
| 11 | 186 | 960 | 774 | 16  | **no** |

Explicitly: `n = 3` gives `|0 − 2| = 2 != 1 = (1/2)2^1`; `n = 7` gives
`|48 − 18| = 30 != 4 = (1/2)2^3`; `n = 11` gives
`|960 − 186| = 774 != 16 = (1/2)2^5`. The formula happens to hold at `n = 5`
(`|8 − 6| = 2 = (1/2)2^2`), but a coincidence at one prime cannot support a claim
quantified over all primes. At `n = 2` the value `(1/2)·2^{(n−1)/2} = 1/√2` is
irrational while the gap is the integer `1`, so the clause is not even well-defined
there.

## Independence of (A) and (B)

Failure (A) concerns the inequality and is witnessed at the composite value `n = 4`
(and all `n >= 4` tested). Failure (B) concerns the prime-gap identity and is
witnessed at the primes `n = 3, 7, 11`. The conjecture is the conjunction of the two
assertions, so either failure alone makes it false; removing either failure still
leaves the other.

## Files

| File | Description |
|:-----|:------------|
| `README.md` | This document: verdict, the two failures, tables, reproduction, rule status. |
| `main.tex` | LaTeX source of the disproof (Witt's formula, both tables, both failures). Compiles standalone with `tectonic main.tex`. |
| `build/main.pdf` | Compiled PDF produced by `tectonic --outdir build main.tex` (tectonic 0.17.0); checked-in build artifact. |
| `reproduce.py` | Python 3 (standard library only) reproduction: hand-written Möbius function, Witt dimensions `n = 1..12`, the bound, the prime gaps, and PASS/FAIL checks; `python3 reproduce.py` exits 0 and prints `PASS`. |
| `lean4/lean-toolchain` | Pins `leanprover/lean4:v4.33.1`. |
| `lean4/lakefile.toml` | Lake library `Main` for the project `tlmc443`; the project builds with `lake build`. |
| `lean4/Main.lean` | Core-Lean-only formalisation of the arithmetic: `mobius`, `wittDim`, the failures, and a final theorem. |
| `lean4/Check.lean` | `#print axioms` audit of every theorem, run via `lake env lean Check.lean`. |
| `lean4/README.md` | Statement table, proof strategy, and scope note for the Lean development. |

## Reproducing

The numerical checks are dependency-free and run in well under a second:

```sh
python3 reproduce.py
```

It prints the Witt dimensions for `n = 1..12`, the bound table, and the prime-gap
table, then verifies that (A) `dim L_n < B(n)` for all `n` in `[4, 12]` and
(B) the gap claim fails at `n = 3, 7, 11`. It ends with `PASS` (exit status `0`) only
if every check succeeds; a non-zero exit indicates a failed check.

The LaTeX document is built with:

```sh
tectonic main.tex
```

The Lean 4 project is built with:

```sh
cd lean4
lake build
lake env lean Check.lean
```

The Lean project uses the toolchain pinned in `lean4/lean-toolchain`
(`leanprover/lean4:v4.33.1`) and imports only `Std`; it does not depend on Mathlib.

## Status against the submission rules

Rule 3 requires each submission to contain the LaTeX source code, a PDF document,
and a Lean 4 project.

- **LaTeX source** — present (`main.tex`), a standalone `article` using only
  `amsmath`, `amssymb`, `amsthm`, and `array`, designed to compile with
  `tectonic main.tex`.
- **PDF document** — present at `build/main.pdf`, produced from `main.tex` with
  `tectonic --outdir build main.tex` (tectonic 0.17.0), and checked in. The source
  is self-contained (no external figures, no non-standard packages).
- **Lean 4 project** — present under `lean4/`, with `lean-toolchain`,
  `lakefile.toml`, `Main.lean`, and `Check.lean`. It formalises the arithmetic core:
  a hand-written `mobius`, `wittDim` implementing `(1/n)·Σ_{d|n} μ(d)·2^{n/d}` by a
  bounded divisor loop, `wittDim 4 = 3`, `B(4) = 4`, `wittDim 4 < B(4)`, the
  gap failure at `n = 3`, gap failures at `n = 7, 11`, and a final theorem
  `conjecture_00000000443_false` combining them. It is written in core Lean only
  (no Mathlib) and contains no `sorry`; it builds successfully with `lake build`
  on `leanprover/lean4:v4.33.1`, and `lake env lean Check.lean` reports that all
  listed theorems depend on no axioms (no `sorryAx`, no `Lean.ofReduceBool`).
- **Build note** — Both artifacts were produced and verified: `build/main.pdf` is
  the compiled PDF from `tectonic --outdir build main.tex` (tectonic 0.17.0), and
  the Lean project builds with `lake build` on the pinned toolchain
  `leanprover/lean4:v4.33.1` ("Build completed successfully", exit 0, no errors,
  no `sorry`). `lake env lean Check.lean` prints the axioms of each theorem: all
  listed theorems depend on no axioms, with no `sorryAx` and no Mathlib
  dependency. `python3 reproduce.py` exits 0 and prints `PASS`.
