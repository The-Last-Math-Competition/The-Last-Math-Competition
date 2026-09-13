# Disproof of conjecture `00000001260`

**Verdict: FALSE.**

This submission disproves conjecture `00000001260` as stated. The conjecture
asserts a *universal* upper bound, `p(n) ≤ n + 2`, for the factor complexity of
every primitive substitution in the "purely substitutive class" (纯替换类).
The Thue–Morse word — a two-letter, constant-length but genuinely primitive
substitution — has six distinct factors of length 3, so `p(3) = 6 > 5 = 3 + 2`
and the asserted bound fails already at `n = 3`. The failure is systematic, not
an accident: the Tribonacci word named in the conjecture itself satisfies
`p(n) = 2n + 1 > n + 2` for every `n ≥ 2`.

## The conjecture

Quoted verbatim from `conjectures/00000001260.md`:

> **English.** Definition: The factor complexity `p(n)` of a primitive
> substitution counts distinct factors of length `n`. Conjecture: The optimal
> upper bound is `p(n) ≤ n+2` within the purely substitutive class, attained by
> three-letter substitution families beyond the Tribonacci word; `p(n) = n+1`
> occurs only for Sturmian words.
>
> **中文。** 定义:primitive 替换的因子复杂度 p(n) 指长度 n 的相异因子数。
> 猜想:p(n) 的最优上界为 p(n) ≤ n+2(在纯替换类中),且该界由 Tribonacci 词
> 以外的三字母替换族达到;p(n)=n+1 仅限 Sturmian。

The filed text contains a definition, a universal bound, an attainment claim,
and a classification claim. The *universal bound* is the load-bearing part; we
refute it. The textual sentence is also garbled: it mixes a universal bound
(`p(n) ≤ n+2` "within the class") with an *attainment* claim ("attained by
three-letter substitution families"), which are statements of different logical
type. Under the literal reading there is no ambiguity: the bound is false.

## The Thue–Morse counterexample

**Definition (substitution).** The Thue–Morse substitution on `{0,1}` is

```
0 ↦ 01,    1 ↦ 10.
```

Its fixed point starting with `0` is the Thue–Morse word

```
TM = 0110100110010110 01101001 10010110 10010110 01101001 ...
```

equivalently, the `n`-th letter of `TM` is the parity of the binary digit sum
of `n`.

**Primitivity.** The incidence matrix of `0 ↦ 01, 1 ↦ 10` is

```
M = [[1, 1],
     [1, 1]]
```

— every entry is positive, hence `M^k` is positive for every `k ≥ 1` and the
substitution is primitive (the defining condition already holds at `k = 1`).
The Thue–Morse word is standardly *purely substitutive*: it is the fixed point
of an actual substitution, and that substitution is primitive. It is a
constant-length substitution, and the filed text imposes **no** restriction
excluding constant-length substitutions and **no** restriction on the alphabet
size.

**The bound fails at `n = 3`.** The six blocks

```
011,  110,  101,  010,  100,  001
```

each occur in `TM` as a length-3 factor (they start at positions `0,1,2,3,4,5`
of the prefix, respectively) and are pairwise distinct, so `p(3) ≥ 6`.
Enumerating all length-3 factors over the prefix of length `2^18` gives exactly
`6`, so

```
p(3) = 6  >  5 = 3 + 2.
```

This single inequality refutes the universal upper bound `p(n) ≤ n+2`.
Refuting a universal *upper* bound requires only a *lower* bound at one point;
each of the six blocks is a genuine factor by construction, so no completeness
argument is needed.

## The complexity table for `n = 1,…,15`

Counting distinct length-`n` factors of `TM` over the prefix of length `2^18`:

| `n`    | 1 | 2 | 3 | 4  | 5  | 6  | 7  | 8  | 9  | 10 | 11 | 12 | 13 | 14 | 15 |
|:-------|--:|--:|--:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `p(n)` | 2 | 4 | 6 | 10 | 12 | 16 | 20 | 22 | 24 | 28 | 32 | 36 | 40 | 42 | 44 |
| `n+2`  | 3 | 4 | 5 | 6  | 7  | 8  | 9  | 10 | 11 | 12 | 13 | 14 | 15 | 16 | 17 |

The bound holds only at `n = 2` (where `p(2) = 4 = 2+2`); it fails for every
`n ≥ 3`, first at `n = 3`. Numerical verification confirms `p(n) > n+2` for
every `n ∈ [3, 300]`.

## Bonus counterexamples

### The Tribonacci word — the word the conjecture names

The Tribonacci word is the fixed point of the primitive three-letter
substitution

```
0 ↦ 01,   1 ↦ 02,   2 ↦ 0.
```

Its factor complexity is exactly `p(n) = 2n + 1`. Hence `p(n) = 2n+1 > n+2`
for every `n ≥ 2`: the very word the conjecture names as the reference point
*also* violates the asserted universal bound. Computation over a prefix of
length `223317` reproduces

```
p(1..15) = 3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 25, 27, 29, 31  (= 2n+1).
```

### The period-doubling word

The period-doubling word is the fixed point of `0 ↦ 01, 1 ↦ 00`. Computation
over a prefix of length `65536` gives

```
p(1..14) = 2, 3, 5, 6, 8, 10, 11, 12, 14, 16, 18, 20, 21, 22,
```

so the bound `p(n) ≤ n+2` first fails at `n = 5`, where `p(5) = 8 > 7`.

### Sturmian words confirm the second clause

The Fibonacci word, fixed point of `0 ↦ 01, 1 ↦ 0`, is the archetypal Sturmian
word and satisfies `p(n) = n + 1` for all `n`. Computation over a prefix of
length `131072` gives `p(1..14) = 2, 3, …, 15`, exactly `n+1`. The
classification clause `p(n) = n+1` only for Sturmian words is therefore
consistent with the data; it is the universal bound that fails.

## Reading caveat (honesty statement)

This refutation targets the **literal universal reading** of the filed text:
"the optimal upper bound is `p(n) ≤ n+2` within the purely substitutive class",
with no alphabet restriction and no exclusion of constant-length substitutions.

- If "purely substitutive" were silently restricted to **three-letter**
  substitutions, or to **Pisot-type** substitutions, the Thue–Morse
  counterexample (two letters, constant length) would be excluded and the
  refutation would not apply. **No such restriction appears in the filed
  text.**
- If the conjecture were reinterpreted as a statement about the **minimal
  growth rate over the class** rather than a universal upper bound, the
  Thue–Morse word would again be irrelevant. **No such reinterpretation is
  present in the text.** The sentence plainly asserts a bound `p(n) ≤ n+2`
  holding within the class.
- The sentence itself is garbled, mixing a universal bound with an attainment
  claim; it is not a precise mathematical statement, and the text supplies no
  repaired reading.

Under the literal reading there is no ambiguity: the bound is false.

## Files

| File | Description |
|:-----|:------------|
| `README.md` | This document: verdict, bilingual quote, definitions, tables, bonuses, caveat, reproduction, status. |
| `main.tex` | LaTeX source; standalone `article`, compiles with `tectonic --outdir build main.tex`. |
| `build/main.pdf` | PDF produced by `tectonic --outdir build main.tex`. |
| `reproduce.py` | Python 3 standard-library-only reproduction; prints `PASS`/`FAIL`, non-zero exit on failure. |
| `lean4/lean-toolchain` | Pins `leanprover/lean4:v4.33.1`. |
| `lean4/lakefile.toml` | Lake configuration; library `Main`, name `tlmc1260`, no dependencies. |
| `lean4/Main.lean` | Core-Lean-only formalisation (`import Std`, no Mathlib, no `sorry`). |
| `lean4/Check.lean` | `#print axioms` audit for every theorem. |
| `lean4/README.md` | Statement table, proof strategy, and scope note for the formalisation. |

## Reproducing

Python (standard library only, ~16 seconds):

```sh
python3 reproduce.py
```

It builds the Thue–Morse prefix of length `2^18` by iterated substitution,
counts distinct length-`n` factors for `n = 1..300`, verifies `p(3) = 6` and
`p(n) > n+2` for all `n ∈ [3,300]`, and also computes the period-doubling,
Tribonacci, and Fibonacci complexities. It prints `PASS` and exits `0` exactly
when every check holds; a `FAIL` (non-zero exit) means a claimed fact did not
verify.

LaTeX document:

```sh
tectonic --outdir build main.tex
# writes build/main.pdf directly (plain `tectonic main.tex` writes main.pdf
# in the current directory)
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
  `geometry`, `amsmath`, `amssymb`, `amsthm`, `array`, `parskip`, and
  `booktabs`, compiled with `tectonic --outdir build main.tex`.
- **PDF document** — present at `build/main.pdf`, produced by
  `tectonic --outdir build main.tex`.
- **Lean 4 project** — present under `lean4/`, with `lean-toolchain`,
  `lakefile.toml`, `Main.lean`, `Check.lean`, and `README.md`. It formalises
  the concrete lower bound (`tm_p3_ge_6`, `tm_p3_eq_6`, `tm_refutes_bound`),
  the consistency of the closed form with the substitution
  (`tm_prefix_agrees`), primitivity via the positive incidence matrix
  (`incidence_positive`), and the packaged refutation
  (`conjecture_00000001260_false`). It uses core Lean only (no Mathlib) and
  contains no `sorry`; `lake env lean Check.lean` reports no `sorryAx` and no
  `Lean.ofReduceBool`.
