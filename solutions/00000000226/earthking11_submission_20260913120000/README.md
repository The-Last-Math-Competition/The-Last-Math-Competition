# Disproof of conjecture `00000000226`

**Verdict: FALSE.**

This submission disproves the proportion claim of conjecture `00000000226` as
stated. The refutation is unconditional and elementary: both Cullen and Woodall
numbers are odd, so "least prime factor 3" is the same as "divisible by 3";
reducing modulo 3 with period 6 gives a Cullen proportion of `2/6 = 1/3` and a
Woodall proportion of `2/6 = 1/3`, whose sum is `2/3`, not the conjectured `1`.

## The conjecture

Original statement (English and Chinese) as filed in
`conjectures/00000000226.md`:

> **English.** Definition: Cullen numbers C_n = n·2ⁿ+1 and Woodall numbers
> W_n = n·2ⁿ−1. Conjecture: The count of Cullen primes is asymptotically
> x/log²x times an explicit sieve constant; the proportion of Cullen numbers
> with least prime factor 3 is an explicit rational, and the corresponding
> proportions for Cullen and Woodall numbers sum to 1 (complementary symmetry
> mod 3). (Cullen-Woodall counting constant)
>
> **中文。** 定义：Cullen 数 C_n=n·2ⁿ+1 与 Woodall 数 W_n=n·2ⁿ−1。猜想：Cullen
> 素数的计数渐近为 x/log²x 乘显式筛常数；最小素因子为 3 的 Cullen 数比例为
> 显式有理数且与 Woodall 对应比例之和为 1（模 3 的互补对称）。（Cullen-Woodall
> 计数常数）

The claim refuted here is the second and third parts: the explicit rational
proportion for Cullen numbers with least prime factor 3, and the assertion that
the Cullen and Woodall proportions sum to 1. The asymptotic prime-counting
claim (Cullen primes ~ x/log²x times a sieve constant) is not addressed and is
independent of the refutation.

## Why it is false

### Step 1: both sequences are odd, so "least prime factor 3" = "divisible by 3"

For `n ≥ 1`, `n·2ⁿ` is even. Hence `C_n = n·2ⁿ + 1` is odd and
`W_n = n·2ⁿ − 1` is odd. Since 2 is not a factor of an odd number, the least
prime factor of an odd number `N` is 3 exactly when `3 | N`:

- if `3 | N`, the smallest prime factor is 3 (2 is excluded, 3 divides);
- if the least prime factor is 3, then `3 | N` by definition.

So counting Cullen/Woodall numbers with least prime factor 3 is the same as
counting those divisible by 3.

### Step 2: reduction modulo 3 has period 6

Modulo 3, `2 ≡ −1`, so `2ⁿ ≡ (−1)ⁿ`, i.e. `2ⁿ mod 3 = 1` for even `n` and
`2` for odd `n`. The pair `(n mod 3, n mod 2)` has combined period
`lcm(3,2) = 6`, so `n mod 6` determines both `n mod 3` and the parity of `n`.
Therefore `C_n mod 3` and `W_n mod 3` depend only on `n mod 6`.

### Step 3: the residue table

| `n mod 6` | `2ⁿ mod 3` | `C_n mod 3` | `W_n mod 3` |
|:---------:|:----------:|:-----------:|:-----------:|
| 0 | 1 | 1 | 2 |
| 1 | 2 | **0** | 1 |
| 2 | 1 | **0** | 1 |
| 3 | 2 | 1 | 2 |
| 4 | 1 | 2 | **0** |
| 5 | 2 | 2 | **0** |

(The rows for `n mod 6 = 0, 1, 2, 3, 4, 5` are witnessed by the representatives
`n = 6, 7, 8, 9, 10, 11`, all `≥ 1`; the table is reproduced in
`lean4/Main.lean` as `residue_table`.)

### Step 4: the two equivalences

- `3 | C_n = n·2ⁿ + 1  ⟺  n ≡ 1 or 2 (mod 6)`, so the Cullen proportion is
  exactly `2/6 = 1/3`.
- `3 | W_n = n·2ⁿ − 1  ⟺  n ≡ 4 or 5 (mod 6)`, so the Woodall proportion is
  exactly `2/6 = 1/3`.

### Step 5: the proportions sum to 2/3, not 1

```
1/3 + 1/3 = 2/3 ≠ 1.
```

The two sets of residues `{1,2}` and `{4,5}` are complementary only *inside*
the six residue classes; the classes `0` and `3` are divisible by 3 in neither
sequence, which is exactly why the proportions do not complete to 1. The
asserted "complementary symmetry mod 3" fails.

This was verified computationally by the project owner: over `n ≤ 60000` the
densities are `0.3333` for each sequence, with divisible residues exactly
`{1,2}` for Cullen and `{4,5}` for Woodall.

## Files

| File | Description |
|:-----|:------------|
| `README.md` | This document: verdict, the refutation, the residue table, reproduction instructions. |
| `main.tex` | LaTeX source of the disproof. Standalone `article` (amsmath/amssymb/amsthm), compiles with `tectonic --outdir build main.tex`. |
| `build/main.pdf` | PDF produced by the command above. |
| `reproduce.py` | Python 3 (standard library only): verifies both iff statements for all `n ≤ 2000`, prints the residue table, checks parity, asserts the proportions sum to `2/3 ≠ 1`, prints `PASS`/`FAIL`, exits 0. |
| `lean4/lean-toolchain` | Pins `leanprover/lean4:v4.33.1`. |
| `lean4/lakefile.toml` | Lake configuration; library `Main`, no dependencies. |
| `lean4/Main.lean` | Core Lean 4 formalisation (`import Std`, no Mathlib, no `sorry`, no `axiom`, no `native_decide`). |
| `lean4/Check.lean` | `#print axioms` audit for every theorem. |
| `lean4/README.md` | Statement table, proof strategy, and environment notes for the formalisation. |

## Reproducing

The Python check is dependency-free:

```sh
python3 reproduce.py
```

It verifies, for every `1 ≤ n ≤ 2000`, both
`(C_n % 3 == 0) == (n % 6 in (1,2))` and
`(W_n % 3 == 0) == (n % 6 in (4,5))`, prints the residue table, checks that
`C_n` and `W_n` are odd throughout, and asserts `Fraction(2,6) + Fraction(2,6)
== Fraction(2,3) != 1`. It prints `PASS` and exits 0 on success.

The LaTeX document is built with:

```sh
mkdir -p build
tectonic --outdir build main.tex
```

The Lean 4 project is built and audited with:

```sh
cd lean4
export PATH="$HOME/.elan/bin:$PATH"
lake build
lake env lean Check.lean
```

The project uses the toolchain pinned in `lean4/lean-toolchain`
(`leanprover/lean4:v4.33.1`) and imports only `Std`; it does not depend on
Mathlib and needs no cache download.

## Status against the submission rules

Rule 3 requires each submission to contain the LaTeX source code, a PDF
document, and a Lean 4 project.

- **LaTeX source** — present (`main.tex`), a standalone `article` using only
  `geometry`, `amsmath`, `amssymb`, `amsthm`, `array`, and `booktabs`, with the
  two equivalence theorems, the `2/3` conclusion, and the residue table.
- **PDF document** — present at `build/main.pdf`, produced by
  `tectonic --outdir build main.tex`.
- **Lean 4 project** — present under `lean4/`, with `lean-toolchain`,
  `lakefile.toml`, `Main.lean`, and `Check.lean`. `lake build` exits 0, and
  `lake env lean Check.lean` prints the axioms of every theorem: only
  `propext` (and `Quot.sound` for the theorems using `omega`/`rw`), with no
  `sorryAx` and no `Lean.ofReduceBool`.

## The Lean formalisation in one paragraph

`lean4/Main.lean` proves `2^n % 3 = 2^(n % 6) % 3`, then
`(n*2^n) % 3 = ((n % 6) * 2^(n % 6)) % 3`, then the period-6 forms of
`(n*2^n+1) % 3` and `(n*2^n+2) % 3`. Splitting `n % 6` into the six residues
(closing each by `decide`) yields `cullen_div3_iff`
(`(n*2^n+1) % 3 = 0 ↔ n % 6 = 1 ∨ n % 6 = 2`) and `woodall_div3_iff`
(`(n*2^n+2) % 3 = 0 ↔ n % 6 = 4 ∨ n % 6 = 5`); the `+2` form is `−1 mod 3`,
and for `n ≥ 1` it is converted to `W_n % 3` by `woodall_W_div3_iff` using
`n*2^n ≥ 1`. The parity lemmas `cullen_odd` and `woodall_odd` establish that
2 is never a factor. Finally `proportions_sum` records `2 + 2 = 4` and
`4 ≠ 6` over the common denominator 6 (core `Rat` operations are irreducible,
so `decide` cannot reduce `ℚ`, and the arithmetic is done in `Nat` instead),
and `conjecture_00000000226_false` collects the two equivalences and the
non-sum.
