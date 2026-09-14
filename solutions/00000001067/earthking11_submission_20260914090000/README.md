# Disproof of conjecture `00000001067`

**Verdict: FALSE.**

The conjecture claims that the maximal `B_2` set (= strong Sidon set) in `F_p`
has size `ceil(sqrt p) + O(1)` **and** that the `O(1)` term **equals 0** for
`p ≡ 3 (mod 4)` — an *exact* equality claim. The refutation is unconditional,
elementary and finitely verifiable: for

> **p = 19**, which satisfies **19 ≡ 3 (mod 4)**,

the largest strong Sidon set in `F_19` has size **4**, whereas
**ceil(sqrt 19) = 5**. The exact "O(1) term = 0" clause is therefore false.
It fails already at `p = 11`, and also at `p = 43, 47, 59`. It happens to hold
at `p = 7, 23, 31` — a plausible-but-false exact formula, not a typo.

## The conjecture, quoted verbatim (bilingual)

From `conjectures/00000001067.md`:

> **English.** Definition: A B_h set (unique h-fold sums). Conjecture: The
> maximal B₂ set in F_p has size ⌈√p⌉ + O(1), and the O(1) term equals 0 for
> p ≡ 3 mod 4 (an exact B₂ result).
>
> **中文。** 定义：B_h 集(和唯一)。猜想：F_p 的最大 B_2 集为 ⌈√p⌉ + O(1) 且
> O(1) 项 = 0 对 p ≡ 3 mod 4(B₂ 精确)。

The phrase "an exact B₂ result" fixes the reading of the last clause: the
`O(1)` term is asserted to **equal** `0`, so the conjecture claims the exact
identity

```
max{ |S| : S ⊆ F_p is a B_2 set } = ceil(sqrt p)   for every prime p ≡ 3 (mod 4).
```

## The convention: `B_2` means strong Sidon

A `B_h` set has all `h`-fold sums (unordered, repetitions allowed) distinct, so
a `B_2` set is a **strong Sidon set**:

> All sums `a + b` with `a, b ∈ S` and `a ≤ b` (repetition allowed) are
> pairwise distinct.

In particular `2a = b + c` with `b ≠ c` is forbidden. This is the standard
reading of "unique 2-fold sums". It is what the difference-count proof below
uses. The weaker reading (only sums of two *distinct* elements unique) is
treated separately under "Alternative readings" — it does not save the
conjecture either.

## The `p = 19` witness

`{0, 1, 3, 7} ⊆ F_19` is a strong Sidon 4-set. Its ten unordered sums
`a + b`, `a ≤ b`, are

| pair | `0+0` | `0+1` | `0+3` | `0+7` | `1+1` | `1+3` | `1+7` | `3+3` | `3+7` | `7+7` |
|:-----|:-----:|:-----:|:-----:|:-----:|:-----:|:-----:|:-----:|:-----:|:-----:|:-----:|
| sum  | 0 | 1 | 3 | 7 | 2 | 4 | 8 | 6 | 10 | 14 |

i.e. the sorted list **0, 1, 2, 3, 4, 6, 7, 8, 10, 14**, which is pairwise
distinct. The maximum is at least 4. The next section shows it is at most 4.

## The difference-count proof

**Lemma (difference bound).** Let `S ⊆ F_p` be a strong Sidon set of size `k`.
Then the `k(k−1)` ordered differences `a − b` with `a ≠ b` are pairwise
distinct and nonzero; hence `k(k−1) ≤ p − 1`.

**Proof.** Suppose `a − b = c − d` with `a ≠ b`, `c ≠ d`. Then `a + d = c + b`
is an equality of two allowed sums. If the multisets `{a, d}` and `{c, b}`
differ, this is a forbidden collision (violating strong Sidon). If they are
equal, then either `a = c, d = b` (giving `(a, b) = (c, d)`) or `a = b, d = c`
(excluded by `a ≠ b`). So distinct `(a, b)` give distinct differences; they are
nonzero because `a ≠ b`. As `F_p` has exactly `p − 1` nonzero elements,
`k(k−1) ≤ p − 1`. ∎

**At `p = 19`:** a 5-element strong Sidon set would need `5 · 4 = 20` distinct
nonzero differences, but `F_19` has only `18 = 19 − 1`. Hence no such set
exists, so the maximum is at most 4. Combined with the witness, the maximum is
**exactly 4**, while `ceil(sqrt 19) = 5`.

The smaller prime `p = 11` (also `≡ 3 mod 4`) is refuted the same way:
`ceil(sqrt 11) = 4`, but `4 · 3 = 12 > 10 = 11 − 1`, and `{0,1,3}` is a strong
Sidon 3-set, so the maximum is 3.

## The exhaustive `C(19,5)` check

Independently of the difference bound, one can enumerate all `C(19,5) = 11628`
five-element subsets of `F_19` and test the 15 unordered sums of each. **Every**
five-subset contains a repeated sum: there is no strong Sidon 5-set. So the
maximum is at most 4, confirming the difference-count conclusion by brute
force. `reproduce.py` performs exactly this enumeration (11628 subsets, 0 strong
Sidon among them). It also reports all 2129 strong Sidon subsets of `F_19`; the
maximum-cardinality ones have size 4, e.g. `{0,1,3,7}`.

## The full table

Maximum strong Sidon size in `F_p`, computed by exhaustive backtracking
(eight primes; all eight are `≡ 3 mod 4`):

| `p` | `p mod 4` | `ceil(sqrt p)` | max strong Sidon | exact claim holds? |
|----:|:---------:|:--------------:|:----------------:|:------------------:|
| 7  | 3 | 3 | 3 | yes |
| 11 | 3 | 4 | 3 | **NO** |
| 19 | 3 | 5 | 4 | **NO** |
| 23 | 3 | 5 | 5 | yes |
| 31 | 3 | 6 | 6 | yes |
| 43 | 3 | 7 | 6 | **NO** |
| 47 | 3 | 7 | 6 | **NO** |
| 59 | 3 | 8 | 7 | **NO** |

The exact formula holds at `p = 7, 23, 31` and fails at `p = 11, 19, 43, 47,
59`. For `p = 43, 47, 59` the difference bound alone does **not** forbid the
conjectured size (`7·6 = 42 = 43 − 1` at `p = 43`; `7·6 = 42 ≤ 46` at `p = 47`;
`8·7 = 56 ≤ 58` at `p = 59`); the exhaustive search rules it out, and at
`p = 43` the Bruck–Ryser–Chowla theorem does so independently.

## Cross-check at `p = 43`: Bruck–Ryser–Chowla

At `p = 43` a strong Sidon 7-set would satisfy `k(k−1) = 7·6 = 42 = 43 − 1`, so
by the difference bound its 42 differences would be *all* the nonzero residues
mod 43: a perfect `(43, 7, 1)` difference set. A `(v, k, λ)` difference set
with `k − λ = 6` yields a symmetric `2-(v, k, λ)` design, and a symmetric
`2-(n²+n+1, n+1, 1)` design is a projective plane of order `n`. Here
`43 = 6² + 6 + 1` and `7 = 6 + 1`, so a size-7 strong Sidon set in `F_43` would
produce a projective plane of order 6.

**Bruck–Ryser–Chowla:** if a projective plane of order `n ≡ 1, 2 (mod 4)`
exists then `n` is a sum of two squares. Now `6 ≡ 2 (mod 4)`, and 6 is not a
sum of two squares (`0,1,2,4,5` are representable below 6, but 6 is not). So no
projective plane of order 6 exists, hence no size-7 strong Sidon set in `F_43`
exists. This is consistent with the computed maximum 6 and independently
certifies the failure at `p = 43`.

## Alternative readings

### Weak Sidon — does not save the conjecture

**Weak Sidon:** the sums `a + b` with `a ≠ b` (distinct elements only) are
pairwise distinct. Repetitions `2a` are unconstrained, so this is genuinely
weaker. The weak maxima are:

| `p` | `ceil(sqrt p)` | max weak Sidon | holds? |
|----:|:--------------:|:--------------:|:------:|
| 7  | 3 | 4 | **NO** |
| 11 | 4 | 5 | **NO** |
| 19 | 5 | 6 | **NO** |
| 23 | 5 | 6 | **NO** |
| 31 | 6 | 7 | **NO** |
| 43 | 7 | 8 | **NO** |
| 47 | 7 | 8 | **NO** |
| 59 | 8 | 9 | **NO** |

The exact formula fails even harder: at `p = 19` the weak maximum is
`6 > 5 = ceil(sqrt 19)` (e.g. `{0,1,2,4,7,12}`), and at `p = 11` it is
`5 > 4 = ceil(sqrt 11)` (e.g. `{0,1,2,4,7}`).

**Important caveat:** the difference bound is a *strong-Sidon-only* fact. The
weak maximum set `{0,1,2,4,7,12}` in `F_19` has `6 · 5 = 30` ordered
differences but `F_19` has only 18 nonzero elements, so its differences are
certainly not distinct — the lemma must not be applied to weak Sidon sets. For
weak Sidon the correct counting bound is `C(k, 2) ≤ p` (the `C(k,2)` sums of
distinct pairs must lie in `F_p`).

### "Maximal" as inclusion-maximal — does not save the conjecture

If "maximal" is read as *inclusion-maximal* (not properly contained in another
strong Sidon set) rather than maximum cardinality: every inclusion-maximal
strong Sidon set in `F_19` has size **4** (there are 1140 of them, out of 2129
strong Sidon subsets), so nothing changes. This reading does not rescue the
`O(1) = 0` clause.

### Asymptotic weakening — the only reading that survives

The classical upper bound for strong Sidon sets in `F_p`, `|S| ≤ sqrt(p) + O(1)`
(immediate from `k(k−1) ≤ p−1`), makes the *asymptotic* part of the conjecture
true. What fails is precisely the **exact** `O(1) = 0` clause, i.e. the claim
that the maximum equals `ceil(sqrt p)` for `p ≡ 3 (mod 4)`. Replacing the exact
claim by `|S| = ceil(sqrt p) + O(1)` would be true but vacuous about the `O(1)`
term; only that substantially weakened version survives.

## Caveats

- The conjecture does not define "B_2 set" beyond "unique h-fold sums". We use
  the standard strong Sidon reading; the weak and inclusion-maximal readings
  are both tested above and both still refute the exact clause.
- The refutation is a concrete finite counterexample (`p = 19`); it does not
  need any asymptotic estimate. The check that `ceil(sqrt 19) = 5` is
  `4² = 16 < 19 ≤ 25 = 5²`.
- The `p = 11` counterexample is smaller; `p = 19` is the headline witness
  because the difference bound there is `5·4 = 20 > 18 = p−1`.
- The Lean development formalises the `p = 19` refutation over `Fin 19`; the
  general inequality `k(k−1) ≤ p−1` is proved in prose (`main.tex`) and
  verified computationally (`reproduce.py`), not quantified in Lean.

## Files

| File | Description |
|:-----|:------------|
| `README.md` | This document: verdict, bilingual quote, convention, witness, difference proof, exhaustive check, table, Bruck–Ryser–Chowla cross-check, alternative readings, caveats, reproducibility, rule-3 status. |
| `main.tex` | LaTeX source of the disproof (standalone `article`), compiles with `tectonic --outdir build main.tex`. |
| `build/main.pdf` | PDF produced by `tectonic --outdir build main.tex` (6 pages). |
| `reproduce.py` | Python 3 (standard library only): strong/weak maxima by exhaustive backtracking, difference bound, witness sums, all `C(19,5)` five-subsets, equivalence check, inclusion-maximal sets, Bruck–Ryser–Chowla check, `PASS`/`FAIL` with non-zero exit on failure. |
| `lean4/lean-toolchain` | Pins `leanprover/lean4:v4.33.1`. |
| `lean4/lakefile.toml` | Lake configuration; library `Main`, no dependencies. |
| `lean4/Main.lean` | Lean 4 formalisation, core Lean only (`import Std`, no Mathlib, no `sorry`). |
| `lean4/Check.lean` | `#print axioms` audit for every theorem. |
| `lean4/README.md` | Statement table, proof strategy, axiom audit, footprint/performance notes. |

## Reproducing

Python (standard library only, ~30 s):

```sh
python3 reproduce.py
```

It computes the strong and weak maxima for all eight primes by exhaustive
backtracking, verifies the difference bound on every maximum set, verifies the
witness `{0,1,3,7}` by listing its sums, enumerates all `C(19,5) = 11628`
five-subsets, checks the equivalence "strong Sidon ⇔ differences distinct" on
all subsets of `F_7`, `F_11` and all subsets of size ≤ 6 of `F_19`, `F_23`,
verifies every inclusion-maximal strong Sidon set in `F_19` has size 4, and
checks the Bruck–Ryser–Chowla exclusion of order 6. It prints `PASS` and exits
`0` exactly when every check holds (non-zero exit otherwise).

LaTeX document:

```sh
tectonic --outdir build main.tex
```

Lean 4 project (about 51 s for the first `lake build`):

```sh
cd lean4
lake build
lake env lean Check.lean
```

`lake build` exits `0`; `Check.lean` prints `#print axioms` for every theorem:
no `sorryAx`, no `Lean.ofReduceBool` (no `native_decide`), only the core axioms
`propext` and `Quot.sound`.

## Status against the submission rules

Rule 3 requires each submission to contain the LaTeX source, a PDF document,
and a Lean 4 project.

- **LaTeX source** — present (`main.tex`), a standalone `article` using only
  `geometry`, `amsmath`, `amssymb`, `amsthm`, `array`, `parskip`, `booktabs`;
  compiles with `tectonic main.tex` (verified: `tectonic --outdir build
  main.tex` exits 0 and writes `build/main.pdf`).
- **PDF document** — present at `build/main.pdf` (6 pages, non-empty).
- **Lean 4 project** — present under `lean4/`, with `lean-toolchain` pinned to
  `leanprover/lean4:v4.33.1`, `lakefile.toml` (library `Main`, no
  dependencies), `Main.lean` (core Lean only, no `sorry`), `Check.lean`
  (`#print axioms`), and `lean4/README.md`. `lake build` exits `0` and the
  audit reports only `propext` and `Quot.sound` — no `sorryAx`, no
  `native_decide` axiom.
