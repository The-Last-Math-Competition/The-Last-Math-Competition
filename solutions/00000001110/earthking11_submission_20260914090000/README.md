# Disproof of conjecture `00000001110`

**Verdict: FALSE.**

This submission disproves conjecture `00000001110` as stated. The refutation is
unconditional, completely explicit, and does not depend on any unproved
hypothesis: in type `A_5` (the symmetric group `S_6`), where the Coxeter number
is `h = 6`, the number of reduced words of the longest element `w_0` is

```
292864 = 2^11 * 11 * 13,
```

and the primes `11` and `13` both exceed `h = 6`. The smallest counterexample
is `n = 6`; the cases `n = 2, 3, 4, 5` are `h`-smooth (counts `1, 2, 16, 768`).

## The conjecture

Quoted verbatim from `conjectures/00000001110.md`:

> **English.** Conjecture: The prime factorization of the number of reduced
> words of the longest element w₀ involves only primes ≤ h (smoothness of
> reduced-word counting).
>
> **中文。** 猜想：最长元素 w₀ 的约化词的个数的素因子分解仅含 ≤ h 的素数
> (约化词计数的平滑性)。

## Disambiguation of `h` and the scope

The filed statement never defines `h` and never says which groups are
quantified over. We adopt the standard reading and record it as a deliberate
convention (this is also stated prominently in `main.tex`):

1. **Scope.** All finite Coxeter groups `W`, with `w_0` the longest element and
   `#Red(w_0)` the number of reduced words (reduced decompositions) of `w_0`.
   Under this reading the symmetric group `S_n` (type `A_{n-1}`) is included.
2. **Meaning of `h`.** `h` is the **Coxeter number** of `W`. In type
   `A_{n-1}` (that is, `W = S_n`) one has `h = n`.

A universal claim over finite Coxeter groups is refuted by one group violating
it. Under the standard reading, `n = 6` is such a group.

## The witness: `n = 6`, `h = 6`

The classical bijection (cited, not formalised — see the caveats) is

```
reduced words of w_0 in S_n  <->  standard Young tableaux of shape
(n-1, n-2, ..., 1)  <->  linear extensions of the staircase poset.
```

For `n = 6` the staircase shape is `(5,4,3,2,1)`, with `15 = 6*5/2` boxes. Its
hook lengths are

```
9 7 5 3 1
7 5 3 1
5 3 1
3 1
1
```

so the hook product is `9 * 7^2 * 5^3 * 3^4 * 1^5 = 4465125`, and the
hook-length formula gives

```
#Red(w_0) = 15! / 4465125 = 1307674368000 / 4465125 = 292864
          = 2^11 * 11 * 13.
```

Both `11 > 6 = h` and `13 > 6 = h`, so the count is not `h`-smooth.

### Three independent computations of `292864`

1. **Hook-length formula.** `15! / (9 * 7^2 * 5^3 * 3^4) = 292864`. The
   general staircase hook multiset is: `2k-1` with multiplicity `m+1-k` for
   `k = 1, ..., m`, where `m = n-1` rows.
2. **Dynamic programming over the weak order of `S_6`.** With
   `R(e) = 1` and `R(w) = sum_{i : w s_i < w} R(w s_i)` (the standard
   recurrence counting reduced decompositions by their final letter), the
   value at `w = w_0` is `292864`. This uses no hook-length input at all.
3. **Dynamic programming over the order ideals of the staircase poset.** The
   number of saturated chains from the empty ideal to the full ideal in the
   lattice of order ideals of `(5,4,3,2,1)` is `292864`.

All three agree exactly; methods 1 and 2 are carried out for every
`n = 2, ..., 9` in `reproduce.py`, and method 3 additionally for `n <= 6`.

The count `292864` also matches OEIS [A005118](https://oeis.org/A005118)
(`1, 2, 16, 768, 292864, 1100742656, ...` for `n = 2, 3, 4, 5, 6, 7, ...`).

## Count table

`h = n` in type `A_{n-1}`. The last column is the set of prime factors of
`#Red(w_0)` that exceed `h`; emptiness means `h`-smooth.

| `n` | `h = n` | `#Red(w_0)` (factorisation) | primes > `h` |
|----:|:-------:|:----------------------------|:-------------|
| 4 | 4 | `16 = 2^4` | none |
| 5 | 5 | `768 = 2^8 * 3` | none |
| 6 | 6 | `292864 = 2^11 * 11 * 13` | **11, 13** |
| 7 | 7 | `1100742656 = 2^18 * 13 * 17 * 19` | 13, 17, 19 |
| 8 | 8 | `48608795688960 = 2^25 * 3 * 5 * 13 * 17 * 19 * 23` | 13, 17, 19, 23 |

(The script also covers `n = 2, 3, 9`; `n = 2, 3` are smooth, `n = 9` gives
`29258366996258488320 = 2^34 * 3 * 5 * 17^2 * 19 * 23 * 29 * 31` with
`17, 19, 23, 29, 31 > 9`.)

Every `n >= 6` shown violates the bound; `n = 6` is the first.

## Failed rescue readings

We tried to save the conjecture by re-reading `h` or restricting the scope.
None of the standard readings works.

| Reading | Outcome |
|:--------|:--------|
| `h = n - 1` (height of the highest root) | At `n = 6`: `11, 13 > 5`. Refuted. |
| `h = n/2` | At `n = 6`: `11, 13 > 3`. Refuted. |
| Restrict to simply-laced types | `A_5` **is** simply-laced, so the witness is inside the restricted family. Refuted. |
| Count distinct commutation classes instead of reduced words | Fails even harder: `n = 5` gives `62 = 2 * 31` with `31 > 5`; `n = 6` gives `908 = 2^2 * 227` with `227 > 6`. (Values computed in `reproduce.py` and matching OEIS [A006245](https://oeis.org/A006245).) |
| Restrict the rank to `n <= 5` | The statement becomes true (`1, 2, 16, 768` are `n`-smooth), but this is a strictly weaker claim than the one filed. |
| Use an artificial `h`, e.g. the number of positive roots `n(n-1)/2 = 15` | At `n = 6` this covers `11, 13`; but `15` is not the Coxeter number and this is not the standard reading. Recorded as a caveat, not a rescue. |

The only readings that avoid the counterexample replace `h` by something other
than the Coxeter number, or restrict the rank. Under the standard reading the
conjecture is false.

## Caveats

- **(i) The file never pins down `h` or the scope.** The refutation adopts the
  standard reading (`h` = Coxeter number, all finite Coxeter groups, type `A`
  included) and says so. If one instead restricts to `n <= 5` or redefines `h`
  artificially, the statement can be made true; that changes the claim rather
  than rescuing the filed one.
- **(ii) The bijection is cited, not formalised.** The equivalence
  `reduced words of w_0 in S_n <-> SYT of the staircase shape <-> linear
  extensions of the staircase poset` is a classical theorem used as an input.
  Core Lean (which the accompanying formalisation uses) has no Coxeter groups,
  so the Lean development formalises the *arithmetic evaluation*
  `15! / (9 * 7^2 * 5^3 * 3^4) = 292864` and the divisibility facts, not the
  bijection. The count is nevertheless confirmed by two independent dynamic
  programs in `reproduce.py`.
- **The count is of reduced words, taken literally.** Counting commutation
  classes instead is a different quantity (and fails sooner, as recorded
  above).
- Only finite types are considered, since `w_0` and the Coxeter number exist
  there; this is the natural scope of the statement.

## Files

| File | Description |
|:-----|:------------|
| `README.md` | This document: verdict, bilingual quote, `h`/scope disambiguation, witness with the three computations, tables, failed rescues, caveats, file list, repro commands, rule status. |
| `main.tex` | LaTeX source (standalone `article`) of the disproof; compiles with `tectonic --outdir build main.tex`. |
| `build/main.pdf` | PDF produced by `tectonic --outdir build main.tex`. |
| `reproduce.py` | Python 3 (standard library only, no `sympy`): counts by the hook-length formula and the weak-order DP for `n = 2..9` (plus the order-ideal DP for `n <= 6`), self-written trial-division factorisation, the table with primes exceeding `n`, the failed-rescue checks, `PASS`/`FAIL`, non-zero exit on failure. |
| `lean4/lean-toolchain` | Pins `leanprover/lean4:v4.33.1`. |
| `lean4/lakefile.toml` | Lake configuration; project `tlmc1110`, library `Main`, no dependencies. |
| `lean4/Main.lean` | Lean 4 formalisation, core Lean only (`import Std`, no Mathlib, no `sorry`, **no `native_decide`**). |
| `lean4/Check.lean` | `#print axioms` audit for every theorem. |
| `lean4/README.md` | Statement table, proof strategy, axiom audit, scope note. |

## Reproducing

Python (dependency-free, a few seconds):

```sh
python3 reproduce.py
```

It computes the counts by the hook-length formula and by the weak-order DP for
`n = 2..9` (order-ideal DP additionally for `n <= 6`), factorises them by a
self-written trial-division routine, prints the table with the set of primes
exceeding `n`, asserts that `n = 6` violates the bound with `11, 13 > 6`,
verifies `n = 6` is the smallest violation and that `n = 2..5` are smooth,
checks the failed-rescue readings (including the commutation-class counts
`62` for `n = 5` and `908` for `n = 6`), and exits `0` on `PASS`.

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

`lake build` exits `0`. The audit output (observed verbatim):

```
'Tlmc1110.reducedWordsW0S6_eq' does not depend on any axioms
'Tlmc1110.reducedWordsW0S6_factorisation' does not depend on any axioms
'Tlmc1110.eleven_dvd' does not depend on any axioms
'Tlmc1110.thirteen_dvd' does not depend on any axioms
'Tlmc1110.not_six_smooth' does not depend on any axioms
'Tlmc1110.conjecture_00000001110_false' does not depend on any axioms
```

Every theorem depends on **no axioms at all**: no `sorryAx` and, importantly,
no `Lean.ofReduceBool`. `native_decide` was **not** needed anywhere; all numeral
equalities are closed by the kernel `decide` on structurally recursive
definitions (a hand-written `fact`, `List.prod` of the explicit hook list, and
`Nat` division), so the trusted compiler is not invoked.

## Status against the submission rules

Rule 3 requires each submission to contain the LaTeX source, a PDF document,
and a Lean 4 project.

- **LaTeX source** — present (`main.tex`), a standalone `article` using only
  `geometry`, `amsmath`, `amssymb`, `amsthm`, `array`, `parskip`, `booktabs`;
  compiles with `tectonic --outdir build main.tex` with no errors.
- **PDF document** — present at `build/main.pdf` (non-empty, 79 KB).
- **Lean 4 project** — present under `lean4/`, with `lean-toolchain` pinned to
  `leanprover/lean4:v4.33.1`, `lakefile.toml` (project `tlmc1110`, library
  `Main`, no dependencies), `Main.lean`, `Check.lean` (`#print axioms`), and
  `lean4/README.md`. It formalises the hook-length evaluation
  `reducedWordsW0S6 = 292864`, its factorisation `= 2^11 * 11 * 13`, the
  divisibility facts `11 | reducedWordsW0S6` and `13 | reducedWordsW0S6`, the
  comparisons `6 < 11` and `6 < 13`, and the refutation
  `not_six_smooth : ¬ Bsmooth 6 reducedWordsW0S6`. It uses core Lean only, no
  Mathlib, no `sorry`, and no `native_decide`.
