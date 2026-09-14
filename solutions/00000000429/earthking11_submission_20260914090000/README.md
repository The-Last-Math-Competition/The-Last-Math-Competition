# Disproof of conjecture `00000000429`

**Verdict: FALSE.**

This submission disproves conjecture `00000000429` as stated. The refutation is
unconditional, completely elementary, and rests on a single explicit value of a
q-binomial coefficient at `q = −1`:

```
[6 choose 2]_{q=−1} = 3 ,
```

and `3` is neither `2^t` nor `−2^t` for any integer `t`. Hence no formula
`v(n,k)` whatsoever — 2-adic or otherwise — can make the value of
`[n choose k]_q` at `q = −1` equal to `2^{v(n,k)}` for all `n,k`, and the same
witness defeats the weaker ``signed'' reading `value = ± 2^{v(n,k)}`.

## The conjecture

Quoted verbatim from `conjectures/00000000429.md` (bilingual; the English and
Chinese texts are identical in content):

> **English.** Definition: The q-binomial `[n choose k]_q` at `q = 1` counts
> binomial coefficients. Conjecture: Its value at `q = −1` is of the explicit
> form `2^{v(n,k)}` (`v` a 2-adic valuation formula, giving a complete signed
> version).
>
> **中文。** 定义：q-binomial `[n choose k]_q` 在 q = 1 的计数。猜想：q = −1
> 的值为 `2^{v(n,k)}` 型显式(`v` 为 2-adic 赋值公式,给出完整符号版)。

## How the statement is read

The filed text is informal in one essential respect; we record which reading we
refute.

1. **The claim is about the value, not only its valuation.** The sentence says
   the value *is of the explicit form* `2^{v(n,k)}`. Taken literally this
   asserts that every value `[n choose k]_{q=−1}` is a (nonnegative integer)
   power of two. This is the primary reading, and it is false.
2. **The parenthetical invites a weaker reading.** "Giving a complete signed
   version" may be read as allowing a sign, i.e.
   `[n choose k]_{q=−1} = ± 2^{v(n,k)}`. This weaker reading is **also** false,
   by the same witness (`3 ≠ ± 2^t` for every `t`).
3. **`v` takes nonnegative integer values.** A "2-adic valuation formula"
   produces an exponent `v(n,k) ∈ ℕ`, so `2^{v(n,k)}` is a nonnegative integer
   power of two and `± 2^{v(n,k)}` is a *signed* power of two (with
   `± 2^0 = ±1`). The witness `3` lies outside both families.
4. **Domain.** `0 ≤ k ≤ n`, as usual; `[n choose k]_{q=−1} = 0` for `k > n`.

## The witness and the value table

The q-binomial coefficient is defined for `0 ≤ k ≤ n` by the product formula

```
[n choose k]_q = (1−q^n)(1−q^{n−1})···(1−q^{n−k+1}) / ((1−q)(1−q^2)···(1−q^k)),
```

which is a polynomial in `q` with nonnegative integer coefficients, and,
equivalently, by the Pascal recursion

```
[n choose k]_q = [n−1 choose k−1]_q + q^k [n−1 choose k]_q ,
[n choose 0]_q = 1 ,   [0 choose k]_q = 0  (k ≥ 1).
```

The product formula is `0/0` at `q = −1` and must not be substituted directly;
set `q = −1` in the *polynomial* (equivalently, in the recursion), which gives
the exact **integer** recursion

```
[n choose k]_{q=−1} = [n−1 choose k−1]_{q=−1} + (−1)^k [n−1 choose k]_{q=−1} .
```

**Decisive witness.** Substituting `q = −1` into
`[6 choose 2]_q = 1 + q + 2q^2 + 2q^3 + 3q^4 + 2q^5 + 2q^6 + q^7 + q^8`
gives

```
[6 choose 2]_{q=−1} = 1 − 1 + 2 − 2 + 3 − 2 + 2 − 1 + 1 = 3 ,
```

and `3` is not `2^t` for any integer `t` (powers of two are `1, 2, 4, 8, …`,
and `2 < 3 < 4`), nor is it `−2^t` (which is negative). **Therefore the
conjecture is false as filed, for every candidate formula `v`.**

**Table `[n choose k]_{q=−1}` for `n ≤ 12`** (row `n`, column `k`; blanks are
`k > n`), computed by the integer recursion above:

| n\k | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 |
|----:|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|
| 0  | 1 |   |   |   |   |   |   |   |   |   |    |    |   |
| 1  | 1 | 1 |   |   |   |   |   |   |   |   |    |    |   |
| 2  | 1 | 0 | 1 |   |   |   |   |   |   |   |    |    |   |
| 3  | 1 | 1 | 1 | 1 |   |   |   |   |   |   |    |    |   |
| 4  | 1 | 0 | 2 | 0 | 1 |   |   |   |   |   |    |    |   |
| 5  | 1 | 1 | 2 | 2 | 1 | 1 |   |   |   |   |    |    |   |
| 6  | 1 | 0 | **3** | 0 | 3 | 0 | 1 |   |   |   |    |    |   |
| 7  | 1 | 1 | 3 | **3** | 3 | 3 | 1 | 1 |   |   |    |    |   |
| 8  | 1 | 0 | 4 | 0 | **6** | 0 | 4 | 0 | 1 |   |    |    |   |
| 9  | 1 | 1 | 4 | 4 | 6 | 6 | 4 | 4 | 1 | 1 |    |    |   |
| 10 | 1 | 0 | **5** | 0 | 10 | 0 | 10 | 0 | 5 | 0 | 1 |    |   |
| 11 | 1 | 1 | 5 | 5 | 10 | 10 | 10 | 10 | 5 | 5 | 1 | 1 |   |
| 12 | 1 | 0 | 6 | 0 | 15 | 0 | 20 | 0 | 15 | 0 | 6 | 0 | 1 |

Further small counterexamples to the `2^{v(n,k)}` form:
`[7 choose 3]_{q=−1} = 3`, `[8 choose 4]_{q=−1} = 6`,
`[10 choose 2]_{q=−1} = 5`. The smallest *interior* entry that is not a signed
power of two is `3 = [6 choose 2]_{q=−1}`; the smallest entry that is not a
power of two at all is the zero `[2 choose 1]_{q=−1} = 0` (and `0` is not
`2^t`). For `n ≤ 20` there are **102** nonzero values that are not `±` a power
of two.

## The correct characterisation (q-Lucas, d = 2)

The true description of the whole table is the `d = 2` case of the q-Lucas
theorem:

```
[n choose k]_{q=−1} = C(floor(n/2), floor(k/2))   if NOT (n even and k odd),
[n choose k]_{q=−1} = 0                            if n is even and k is odd.
```

`reproduce.py` verifies this rule for all `0 ≤ k ≤ n ≤ 20` with **0
mismatches**, and it explains every entry above:
`[6 choose 2] = C(3,1) = 3`, `[8 choose 4] = C(4,2) = 6`,
`[10 choose 2] = C(5,1) = 5`, `[2 choose 1] = 0` (since `2` is even and `1` is
odd).

### The "parity of `C(n,k)`" rule is FALSE

A frequently proposed rationale is

```
[n choose k]_{q=−1} ?= C(floor(n/2), floor(k/2))  whenever C(n,k) is odd,
[n choose k]_{q=−1} ?= 0                           whenever C(n,k) is even.
```

**This is wrong, and we explicitly disclaim it.** It fails **73 times** for
`n ≤ 20`. The smallest failure is

```
[8 choose 4]_{q=−1} = 6 ,   while   C(8,4) = 70 is even,
```

so that rule would predict `0` instead of `6`. The parity of `C(n,k)` is
irrelevant; the correct criterion above depends on the parities of `n` and `k`,
not on that of the binomial coefficient. (Note also that
`[6 choose 2]_{q=−1} = 3` with `C(6,2) = 15` odd happens to agree, which is
presumably why the wrong rule looks plausible on small cases.)

### A true but different statement (context)

By Kummer's theorem the 2-adic valuation of the value satisfies the true
identity

```
v_2( [n choose k]_{q=−1} ) = v_2( C(floor(n/2), floor(k/2)) ) .
```

This is a statement about the **valuation** of the value, not about the value
being a power of two, and it does not rescue the conjecture: e.g. `v_2(3) = 0`,
so `2^{v_2([6 choose 2]_{q=−1})} = 2^0 = 1 ≠ 3`.

## Alternative readings tested

We tried to save the conjecture by varying each convention; none succeeds.

| Reading | Outcome |
|:--------|:--------|
| Value `= 2^{v(n,k)}` (literal, unsigned) | **false**: `[6 choose 2]_{q=−1} = 3` is not a power of two. |
| Value `= ± 2^{v(n,k)}` (signed parenthetical) | **false**: `3 ≠ ±2^t` for every integer `t`. |
| `q` a primitive `d`-th root of unity, `d ≥ 3` | values are **non-integer algebraic numbers** (e.g. `[2 choose 1]_ζ = 1+ζ`), not integer powers of two; the `2^{v}` claim fails a fortiori. |
| Restrict to `k = 1` | **false**: `[2 choose 1]_{q=−1} = 0` is not `2^t` or `±2^t` (nor is `[n choose 1]_{q=−1} = 0` for any even `n`). |
| Restrict to even `n` | **false**: `[8 choose 4]_{q=−1} = 6` (with `n = 8` even) is not a signed power of two. |
| Read the value as `2^{v_2(C(n,k))}` (the parity-of-`C(n,k)` rule) | **false** for `n ≤ 20`: 73 mismatches; see above. |
| Read `v` as `v_2` of the value itself | **false**: `v_2(3) = 0`, so `2^{v_2(3)} = 1 ≠ 3`. The true Kummer identity concerns valuations only. |

Only the corrected q-Lucas rule correctly describes the value; it is not of the
conjectured form and yields `3` at `(6,2)`. The refutation therefore stands
under every reading of the filed text.

## Files

| File | Description |
|:-----|:------------|
| `README.md` | This document: verdict, bilingual quote, reading conventions, witness, value table, corrected q-Lucas rule, the false parity rule, alternative readings, file list, repro commands, rule-3 status. |
| `main.tex` | LaTeX source of the disproof (standalone `article`); compiled with `tectonic --outdir build main.tex`. |
| `build/main.pdf` | PDF produced by `tectonic --outdir build main.tex`. |
| `reproduce.py` | Python 3 (standard library only): exact integer Pascal recursion for `n ≤ 20`, independent exact-polynomial cross-check for `n ≤ 12`, q-Lucas verification (0 mismatches), the false parity rule (73 mismatches), the non-power-of-two census, `PASS`/`FAIL` with non-zero exit on failure. |
| `lean4/lean-toolchain` | Pins `leanprover/lean4:v4.33.1`. |
| `lean4/lakefile.toml` | Lake configuration; project/library name `tlmc429`, no dependencies. |
| `lean4/Main.lean` | Lean 4 formalisation, core Lean only (`import Std`, no Mathlib, no `sorry`). |
| `lean4/Check.lean` | `#print axioms` audit for every theorem. |
| `lean4/README.md` | Statement table, proof strategy, pitfalls avoided, axiom audit, scope note. |

## Reproducing

Python (dependency-free, runs in a fraction of a second):

```sh
python3 reproduce.py
```

It computes `[n choose k]_{q=−1}` by the integer Pascal recursion for `n ≤ 20`,
cross-checks against the exact polynomial (Gaussian binomial divided out over
`ℚ` and then evaluated at `q = −1`) for `n ≤ 12`, verifies the corrected
q-Lucas rule with 0 mismatches, documents 73 mismatches for the false
parity-of-`C(n,k)` rule, and checks that `3` is not `±2^t`. It prints `PASS`
and exits `0` exactly when every check holds.

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

`lake build` exits `0` (it compiles in well under a second); `lake env lean
Check.lean` prints `#print axioms` for every theorem and reports no `sorryAx`
(only `propext` and `Quot.sound` for the general statements; the concrete
integer evaluations depend on no axioms).

## Status against the submission rules

Rule 3 requires each submission to contain the LaTeX source, a PDF document,
and a Lean 4 project.

- **LaTeX source** — present (`main.tex`), a standalone `article` using only
  `geometry`, `amsmath`, `amssymb`, `amsthm`, `array`, `parskip`, `booktabs`;
  compiles with `tectonic main.tex`.
- **PDF document** — present at `build/main.pdf`.
- **Lean 4 project** — present under `lean4/`, with `lean-toolchain` (pinned to
  `leanprover/lean4:v4.33.1`), `lakefile.toml`, `Main.lean`, `Check.lean`, and a
  `README.md`. It formalises `[6 choose 2]_{q=−1} = 3` (`qb_6_2`),
  `[8 choose 4]_{q=−1} = 6` (`qb_8_4`), the general facts
  `2^t ≠ 3` and `−2^t ≠ 3` for all `t`, and the failure of the conjecture
  stated for an arbitrary `v : ℕ → ℕ → ℕ` (`conjecture_00000000429_false`),
  signed and unsigned. It uses core Lean only (no Mathlib) and contains no
  `sorry`; the audit reports no `sorryAx`.

## Caveats

- The filed conjecture is informal; we refute its literal value-form reading and
  its natural signed weakening. The value `[6 choose 2]_{q=−1} = 3` is a
  complete, unconditional disproof of both, and of every reading under which the
  right-hand side is an integer power of two.
- The correct q-Lucas description in this document is verified computationally
  for `n ≤ 20` and proved informally; the true Kummer valuation identity is
  mentioned for context but is a different statement and is not used to support
  the conjecture.
- The Chinese text is kept in this markdown file rather than in the PDF, because
  the PDF font used here does not embed CJK glyphs; the English and Chinese
  filings are identical in content.
