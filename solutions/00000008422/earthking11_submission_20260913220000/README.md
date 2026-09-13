# Disproof of conjecture `00000008422`

**Verdict: FALSE.**

The conjecture is false. The decisive witness is `(v,k) = (22,3)`: the
conjecture's own criterion predicts all twenty values `λ ∈ {1,…,20}`, but the
necessary replication condition `r = λ(v-1)/(k-1) = 21λ/2` forces `λ` to be
even, so the ten odd values are unattainable even though predicted. That is
`10 > k² = 9` exceptions, which violates the conjecture's own clause "the
complement of the spectrum is a finite explicit exceptional set with at most
`k²` exceptions". Hence the conjecture fails under **both** readings: the
strict "if and only if / the spectrum is complete" reading and the
"at most `k²` exceptions" reading.

This submission also documents the smaller witness `(v,k) = (6,3)` (the case
proposed in the task), because it exposes the mechanism: the criterion predicts
`{1,2,3,4}` while the attainable set is `{2,4}`. **However, `(6,3)` alone is
not decisive**: it produces only `2 ≤ k² = 9` exceptions, which the filed
exception clause absorbs. We report this honestly below; the load-bearing
witness is `(22,3)`.

## The conjecture, quoted verbatim

From `conjectures/00000008422.md`:

> **English.** Definition: The lambda spectrum of block designs: the set of realizable lambda values for given (v,k). Conjecture: lambda is attainable if and only if lambda binom(v,t)/binom(k,t) is an integer (with t = k-1) and lambda is at most binom(v-2,k-2), so the spectrum is complete; the complement of the spectrum is a finite explicit exceptional set with at most k^2 exceptions. (complete characterization of design lambda spectrum)
>
> **中文。** 定义：区组设计的 λ 的谱为给定 (v,k) 时可实现的 λ 的集合。猜想：λ 可达当且仅当 λ·binom(v,t)/binom(k,t) 为整数（t=k−1）且 λ ≤ binom(v−2,k−2) 的谱完全；谱的补集为有限显式例外集合，例外个数不超过 k²。（设计 λ 谱完全刻画）

Two features of the wording drive the verification.

1. The criterion is stated as **"if and only if"** — the file claims both
   necessity and sufficiency — and reinforces it with **"so the spectrum is
   complete"**.
2. The file immediately adds a hedge: **"the complement of the spectrum is a
   finite explicit exceptional set with at most `k²` exceptions."** So the
   conjecture, read charitably, is: *the spectrum equals the criterion set up
   to at most `k²` exceptional (predicted-but-unattainable) values.*

A refutation must therefore defeat reading (2) as well, by exhibiting
**more than `k²`** predicted-but-unattainable values. `(6,3)` does not do this;
`(22,3)` does.

Here `t = k-1` is taken literally from the file, and `(v,k)` are unconstrained
parameters of the conjecture. A `2-(v,k,λ)` design has

```
b = λ·v(v-1) / (k(k-1))     (block count)
r = λ·(v-1) / (k-1)         (replication number)
```

## The criterion table

With `t = k-1`, the criterion set is
`C(v,k) = {λ ∈ ℤ_{>0} : λ·C(v,t) ≡ 0 mod C(k,t), λ ≤ C(v-2,k-2)}`.
"Predicted" counts the criterion set; "forced out" counts its members that
violate the *necessary* condition `(k-1) | λ(v-1)` (equivalently `r ∈ ℤ`), so
"forced out" is always a lower bound on the number of exceptions.

| `(v,k)` | `t` | `C(v,t)` | `C(k,t)` | ratio | bound `C(v-2,k-2)` | predicted | forced out | `k²` | exceeds budget |
|--------:|:---:|:--------:|:--------:|:-----:|:------------------:|:---------:|:----------:|:----:|:--------------:|
| (6,3)   | 2   | 15       | 3        | 5     | 4                  | 4         | 2          | 9    | no             |
| (7,3)   | 2   | 21       | 3        | 7     | 5                  | 5         | 0          | 9    | no             |
| (8,3)   | 2   | 28       | 3        | 9     | 6                  | 2         | 1          | 9    | no             |
| (10,3)  | 2   | 45       | 3        | 15    | 8                  | 8         | 4          | 9    | no             |
| **(22,3)** | 2 | 231    | 3        | 77    | 20                 | 20        | **10**     | 9    | **yes**        |
| (24,3)  | 2   | 276      | 3        | 92    | 22                 | 22        | **11**     | 9    | **yes**        |

At `(6,3)` the criterion reads `5λ`, integral for every `λ`; at `(22,3)` it
reads `77λ`, again integral for every `λ`. In both cases the criterion predicts
every value up to the `C(v-2,k-2)` bound.

An earlier verification of the proposed `(6,3)` refutation found that
`C(6,2)/C(3,2) = 15/3 = 5` is an integer for all `λ` and that the bound is
`C(4,1) = 4`, so the criterion predicts `{1,2,3,4}`; exhaustive search shows
the attainable set is `{2,4}`. That is a genuine failure of sufficiency, but it
is absorbed by the exception clause (`2 ≤ 9`). The `(22,3)` case is what
defeats the clause itself.

## The divisibility argument

**Lemma (replication identity).** In a `2-(v,k,λ)` design, for every point `p`
the number `r` of blocks through `p` satisfies

```
(k-1)·r = (v-1)·λ.
```

*Proof (double count).* Count flags `(B, q)` where `B` is a block through `p`
and `q ∈ B \ {p}`. By block: `r` blocks through `p`, each with `k-1` further
points, giving `(k-1)r`. By pair: each of the `v-1` points `q ≠ p` lies with
`p` in exactly `λ` blocks, giving `(v-1)λ`. Since `r ∈ ℤ`, also
`(k-1) | (v-1)λ`. ∎

For `k = 3` this is `2r = (v-1)λ`.

* `(6,3)`: `2r = 5λ`; since `5` is odd, `2 | λ`, so `λ ∈ {2,4}` (as `λ ≤ 4`).
  `λ = 1` and `λ = 3` are impossible — for *any* design, simple or with
  repeated blocks.
* `(22,3)`: `2r = 21λ`; since `21` is odd, `2 | λ`. The ten odd values in
  `{1,…,20}` are all impossible. `10 > 9 = k²`.

This is the load-bearing step and it uses only a necessary condition, so it
needs no enumeration of designs and no assumption of simplicity.

## Exhaustive search for `(6,3)`

A `2-(6,3,λ)` design uses 3-subsets of a 6-set; there are `C(6,3) = 20`
candidate blocks and `C(6,2) = 15` pairs. The target block count is
`b = 5λ`.

| `λ` | `b` | search space | designs found | attainable |
|:---:|:---:|:------------:|:-------------:|:----------:|
| 1   | 5   | `C(20,5) = 15504`   | **0** | no  |
| 2   | 10  | `C(20,10) = 184756` | 12    | yes |
| 3   | 15  | `C(20,15) = 15504`  | **0** | no  |
| 4   | 20  | `C(20,20) = 1`      | 1 (the complete design) | yes |

So the attainable set is `{2,4}`, against the criterion's `{1,2,3,4}`.
`reproduce.py` enumerates every subset of the stated search space (with early
exit on pair-count overflow) and also cross-checks with a pruned backtracking
search (`nodes = 13, 199, 71, 43` for `λ = 1,2,3,4`), agreeing on all counts.
The Lean project re-runs the same exhaustive check in the kernel: all
`C(20,5) = 15504` five-element sublists for `λ = 1`, and all 15504 complements
for `λ = 3` (a `2-(6,3,3)` design is the complement, inside the twenty triples,
of a `2-(6,3,1)` design because the complete design has `λ = 4`).

### Explicit design for `λ = 2` (ten blocks)

```
{0,1,2} {0,1,3} {0,2,4} {0,3,5} {0,4,5}
{1,2,5} {1,3,4} {1,4,5} {2,3,4} {2,3,5}
```

Every one of the 15 pairs is covered exactly twice; `b = 10`.

### Explicit design for `λ = 4` (twenty blocks)

The complete design — all `C(6,3) = 20` triples. Each pair lies in
`C(4,1) = 4` triples; `b = 20`.

## Why the exception clause does not save the conjecture

If one reads the file strictly ("if and only if … so the spectrum is
complete"), then `(6,3)` already refutes it: the criterion predicts
`{1,2,3,4}` but `{2,4}` is attainable. If one grants the file its hedge of
"at most `k²` exceptions", then `(6,3)` is *not* a counterexample
(`2 ≤ 9`), but `(22,3)` is:

```
predicted: {1,2,3,4,...,20}      (all twenty values; ratio 77 is an integer)
necessary: 2r = 21λ  ⇒  λ even
forced out: the ten odd values {1,3,5,...,19}
10 > 9 = k²
```

Because "forced out" is derived from a necessary condition, the count is a
lower bound that holds regardless of the full attainable set, and regardless of
whether designs are required to be simple or may repeat blocks. Either way the
conjecture, as worded, is false.

## Alternative readings tested

| Reading of the file | `(6,3)` refutes? | `(22,3)` refutes? |
|:--------------------|:----------------:|:-----------------:|
| Strict "iff", spectrum complete | **yes** (2 exceptions) | yes (10 exceptions) |
| Spectrum = criterion up to `≤ k²` exceptions | no (2 ≤ 9, absorbed) | **yes** (10 > 9) |
| Exceptions = attainable-but-unpredicted values, `≤ k²` | **yes** (criterion not necessary in the iff sense) | yes |
| `t = k` instead of `t = k-1` | **yes** — at `(6,3)`, `C(6,3)/C(3,3) = 20` is again integral for every `λ`, bound `4`, same predicted set `{1,2,3,4}` | **yes** — at `(22,3)`, `C(22,3)/C(3,3) = 1540`, bound `20`, same predicted set `{1,…,20}` |
| Designs required to be simple | yes (the `(6,3)` non-existence holds for simple designs) | yes (divisibility is necessary for simple designs too) |
| Criterion only *necessary* (sufficiency dropped) | no | no — but this discards the stated "if and only if" and the "spectrum is complete" clause |

Only the last reading survives `(22,3)`, and it does so by discarding the
central claim of the conjecture ("if and only if … so the spectrum is
complete"). Under every reading that keeps the "if and only if", the conjecture
is false.

## Files

| File | Description |
|:-----|:------------|
| `README.md` | This document: verdict, the bilingual quoted conjecture, criterion table, divisibility argument, exhaustive search, explicit designs, caveats, reproduction, rule-3 status. |
| `main.tex` | LaTeX source of the disproof. Standalone `article`; compiles with `tectonic --outdir build main.tex`. |
| `build/main.pdf` | PDF produced by `tectonic --outdir build main.tex` (non-empty). |
| `reproduce.py` | Python 3 (standard library only): exhaustive `(6,3)` search for `λ = 1..4`, explicit designs, divisibility checks, criterion table, and the decisive `(22,3)` exception count. Prints `PASS`/`FAIL`; exits non-zero on failure. |
| `lean4/lean-toolchain` | Pins `leanprover/lean4:v4.33.1`. |
| `lean4/lakefile.toml` | Lake configuration; package `tlmc8422`, library `Main`, no dependencies. |
| `lean4/lake-manifest.json` | Lake manifest generated by `lake build` (no packages). |
| `lean4/Main.lean` | Lean 4 formalisation, core Lean only (`import Std`, no Mathlib, no `sorry`, no `native_decide`). |
| `lean4/Check.lean` | `#print axioms` audit for every theorem. |
| `lean4/README.md` | Statement table, proof strategy, and scope note for the formalisation. |

## Reproducing

Python (dependency-free, runs in well under a second):

```sh
python3 reproduce.py
```

Expected tail:

```
PASS: all checks verified.
  The conjecture 00000008422 is FALSE.
```

LaTeX document:

```sh
tectonic --outdir build main.tex
```

Lean 4 project (the kernel-side exhaustive search for `(6,3)` takes about two
minutes):

```sh
cd lean4
lake build
lake env lean Check.lean
```

## Status against the submission rules

Rule 3 requires each submission to contain the LaTeX source, a PDF document,
and a Lean 4 project.

- **LaTeX source** — present (`main.tex`), a standalone `article` using only
  `geometry`, `amsmath`, `amssymb`, `amsthm`, `array`, `parskip`, `booktabs`;
  no CJK package is needed because the Chinese quotation lives in this README.
- **PDF document** — present at `build/main.pdf`, produced by
  `tectonic --outdir build main.tex` (≈75 KiB, non-empty).
- **Lean 4 project** — present under `lean4/` with `lean-toolchain`,
  `lakefile.toml`, `Main.lean`, `Check.lean`, and `README.md`. It formalises
  the `(6,3)` encoding, the explicit `λ = 2` and `λ = 4` designs, the
  exhaustive non-existence proofs for `λ = 1` and `λ = 3`, the criterion's
  predicted sets at `(6,3)` and `(22,3)`, the forced-out counts, the arithmetic
  parity lemmas (`parity_6_3`, `parity_22_3`, `no_odd_lambda_22_3`), and the
  packaged decisive statement `decisive_22_3`. It uses core Lean only and
  contains no `sorry`; `lake env lean Check.lean` reports no `sorryAx`.

## Caveats and scope

- The decisive argument at `(22,3)` uses only the *necessary* replication
  condition `(k-1) | λ(v-1)`, so it is unconditional: it does not enumerate
  designs and does not assume simplicity. It counts predicted-but-forced-out
  values, hence a lower bound on the true number of exceptions.
- The general counting identity `(k-1)r = (v-1)λ` is proved on paper in
  `main.tex`; Lean keeps it as an explicit hypothesis in `parity_6_3` and
  `parity_22_3` rather than formalising the list double-counting. This is the
  one step not machine-checked, and it is isolated and visible.
- The `(6,3)` data are fully machine-checked (Python exhaustive search and
  Lean kernel `decide`), but they are *not* decisive on their own because of
  the exception clause. The submission states this explicitly so the verdict
  does not rest on the weaker witness.
- No files outside this submission directory were modified. No deletion
  commands were used; the PDF is regenerated in place with
  `tectonic --outdir build`.
