# Disproof of conjecture `00000001752`

**Verdict: FALSE.**

This submission disproves conjecture `00000001752` as stated, in the
Burnside-average reading that the conjecture file itself writes in parentheses.
The refutation is unconditional, elementary, and finite: for `S_3` acting
(sharply) 2-transitively on the 1-subsets of `{1,2,3}` the Burnside average of
the fixed-point counts is `1`, whereas the conjectured closed form gives
`1!·S(3,1)/6 = 1/6`, and `1 ≠ 1/6`.

## The conjecture

Quoted verbatim from `conjectures/00000001752.md`:

> **English.** Definition: The Mark values of primitive permutation characters
> of S_n are the averages of fixed points (by subset size). Conjecture: The Mark
> values in the 2-transitive case have a complete closed form:
> M_k = (k!·S(n,k))/|G| (given by the Burnside average of subset counts);
> agreeing case-by-case with the ATLAS.
>
> **中文。** 定义：S_n 的本原置换特征标的 Mark 值指其固定点的平均值(按子集大小)。
> 猜想：2-transitive 情形的 Mark 值的计数有完整闭式:M_k = (k!·S(n,k))/|G|
> (由子集计数的 Burnside 平均给出);与 ATLAS 逐例吻合。

The parenthetical identifies the right-hand side as *the Burnside average of
subset counts*, so we read the asserted equation literally as

```
(1/|S_n|) * sum_{g in S_n} #{ k-subsets of {1,...,n} fixed by g }
    =  k! * S(n,k) / n! ,
```

where `S(n,k)` is a Stirling number of the second kind and `|G| = n!` is the
order of `S_n`. This is the definite equation the file writes, and it is false.

## Scope: in scope vs out of scope (read this first)

Two readings of the conjecture must be kept apart, and we are explicit about
which one we refute.

- **In scope — the Burnside-average equation (what we disprove).** The
  right-hand side is exactly `k!·S(n,k)/|G|` with `|G| = n!`, as the file
  states in parentheses. Our decisive witness, `S_3` on 1-subsets, lies inside
  the strict 2-transitive case (indeed it is *sharply* 2-transitive). The
  refutation in the next section is therefore fully in scope.
- **Out of scope — non-2-transitive actions.** We mention `S_4` on 2-subsets
  only as an extra illustration that the identity fails; that action is **not**
  2-transitive (its ordered pairs of distinct 2-subsets split into intersecting
  and disjoint orbits), so it is **outside** the strict 2-transitive case. We
  flag it as such wherever it appears. An earlier draft led with this
  out-of-scope example; we do not, precisely to avoid that error.

We also state the honest caveat that the conjecture is auto-generated and
misdefines "Mark", so that under the strictest reading it is ill-typed rather
than false; see [Honest caveat](#honest-caveat-the-definition-of-mark-is-ill-posed).

## The decisive in-scope witness: `S_3` on 1-subsets

Let `n = 3`, `k = 1`, and let `G = S_3` act on the three 1-subsets
`{1}, {2}, {3}` of `{1,2,3}`. This is the natural action on three points, which
is sharply 2-transitive: `|G| = 3·2 = 6`. It is squarely inside the strict
2-transitive case.

Write `Fix_1(g)` for the number of 1-subsets fixed by `g`; the singleton `{i}`
is fixed by `g` iff `g(i) = i`. The six elements and their fixed-point counts:

| `g` | cycle type | `Fix_1(g)` |
|:----|:----------:|-----------:|
| `e`         | `1³`   | 3 |
| `(1 2)`     | `2·1`  | 1 |
| `(1 3)`     | `2·1`  | 1 |
| `(2 3)`     | `2·1`  | 1 |
| `(1 2 3)`   | `3`    | 0 |
| `(1 3 2)`   | `3`    | 0 |

So the fixed-point counts are

```
[ Fix_1(g) : g in S_3 ] = [3, 1, 1, 1, 0, 0],   sum = 3 + 1 + 1 + 1 + 0 + 0 = 6.
```

**Left-hand side (Burnside average).**

```
(1/|G|) * sum_{g in G} Fix_1(g) = 6/6 = 1.
```

This is not an accident of the computation: the action is transitive, and by
Burnside's lemma the average number of fixed points equals the number of
orbits, which is 1.

**Right-hand side (the conjectured closed form).** With `S(3,1) = 1`,
`1! = 1`, and `|G| = 3! = 6`:

```
k! * S(n,k) / |G| = 1! * 1 / 6 = 1/6.
```

**Conclusion.** The two sides are `1` and `1/6`:

```
6/6 = 1  ≠  1/6.
```

Because both fractions share the denominator `6`, this is the integer
inequality `6 ≠ 1`. Equivalently, cross-multiplying `1 = 1/1` against `1/6`, we
compare `1·6 = 6` with `1·1 = 1` and find `6 ≠ 1`. The conjectured equation
fails for an action that *is* 2-transitive. **This refutation is in scope.**

### The one coincidence: `S_3` on 2-subsets

For `n = 3`, `k = 2`, the 2-subsets are the complements of the singletons, so
`S_3` acts on them exactly as on the singletons: `Fix_2` is again
`[3,1,1,1,0,0]`, the Burnside average is again `1`, and
`2!·S(3,2)/6 = 2·3/6 = 1`. Here the two sides agree. This is the isolated
coincidence `(n,k) = (3,2)`; it does not rescue the conjecture, which fails at
`(3,1)`.

## The general 2-transitive range

**Theorem.** For `n ≥ 2` and `1 ≤ k ≤ n−1`, the action of `S_n` on the
`k`-subsets of `{1,…,n}` is 2-transitive if and only if `k = 1` or `k = n−1`.
(For `n = 3`, `k = 2 = n−1`, so the case `(S_3, 2)` is already covered; there
is no further exception.)

*Sketch.* `S_n` is transitive on `k`-subsets for every `k`, and 2-transitive on
1-subsets (the natural action) and on `(n−1)`-subsets (complements). For
`2 ≤ k ≤ n−2` and `n ≥ 4`, disjoint and intersecting pairs of distinct
`k`-subsets exist and lie in different orbits (intersection size is
preserved), so the action is not 2-transitive.

On this range the two sides have closed forms.

**Proposition.** For `n ≥ 2`,

```
(1/|S_n|) * sum_{g in S_n} Fix_k(g) = 1          for every 1 ≤ k ≤ n−1,
```

while the conjecture's right-hand side is

```
k!·S(n,k)/n! = 1/n!        for k = 1,
             = (n−1)/2     for k = n−1.
```

*Proof.* The left side is the number of orbits of `S_n` on `k`-subsets, which
is 1. For `k = 1`, `S(n,1) = 1`, so `1!·S(n,1)/n! = 1/n!`. For `k = n−1`,
`S(n,n−1) = C(n,2)`, so `(n−1)!·C(n,2)/n! = C(n,2)/n = (n−1)/2`. ∎

**Corollary (failure throughout the 2-transitive range).** For `n ≥ 2` the
conjecture's equation holds in the 2-transitive range only at the isolated
coincidence `(n,k) = (3,2)`. In particular:
- at `k = 1` the right side is `1/n! ≠ 1` for every `n ≥ 2`;
- at `k = n−1` the right side is `(n−1)/2 ≠ 1` for every `n ≥ 4`;
- the only other value, `k = n` (a single `k`-subset), is not 2-transitive and
  both sides equal `1` there.

So the claim fails at `(3,1)` and, in fact, almost everywhere in the
2-transitive range. (`reproduce.py` verifies this exhaustively for
`2 ≤ n ≤ 7` by counting orbits on ordered pairs of distinct `k`-subsets.)

## Non-integrality: the formula cannot be a Mark value

A Mark in the ATLAS sense is a permutation-character value, i.e. a number of
fixed points of a group element, hence a non-negative **integer**. The
conjectured right side is frequently **not** an integer, so it cannot be "the
Mark values":

| case | `k!·S(n,k)/n!` | integral? |
|:-----|:--------------:|:---------:|
| `S_3`, `k = 1` (in scope) | `1/6` | no |
| `S_5`, `k = 1` (in scope) | `1/120` | no |
| `S_4`, `k = 1` (in scope) | `1/24` | no |
| `S_4`, `k = 3` (in scope) | `3/2` | no |
| `S_6`, `k = 5` (in scope) | `5/2` | no |
| `S_5`, `k = 4` (in scope) | `2` | yes |
| `S_4`, `k = 2` (**out of scope**) | `7/12` | no |

In particular, at `k = 1` — in scope for every `n ≥ 2` — the value is `1/n!`,
a non-integer for every `n ≥ 2`. Meanwhile the quantity it is equated to, the
Burnside average, is `1` (an integer). So before any numerical comparison, a
fractional right-hand side cannot be a Mark. This is a secondary, independent
obstruction; the primary refutation is the exact mismatch at `(3,1)`.

## Honest caveat: the definition of "Mark" is ill-posed

We state this prominently and do not hide it. The conjecture is auto-generated
and its first sentence conflates two different objects:

1. the **permutation-character value** `π_k(g) = Fix_k(g)`, the number of
   `k`-subsets fixed by `g` — this is the classical Mark value, and it is an
   integer; and
2. the **average** `(1/|G|)·Σ_g Fix_k(g)`, which by Burnside equals the number
   of orbits (here `1`).

The first sentence says the Mark values *are the averages of fixed points*,
identifying (1) with (2); the parenthetical then says the right side is
*given by the Burnside average of subset counts*, which is (2). Therefore:

- **The equation we refute is definite and is the file's own.** Under the
  parenthetical reading, the asserted identity is
  `(1/|G|)·Σ_g Fix_k(g) = k!·S(n,k)/|G|`, and it is false — see the witness
  above. This reading is unconditional.
- **Under the strictest reading the statement is not well-posed.** If "`M_k` is
  an ATLAS Mark" is taken literally, then `M_k` is an integer character value,
  and equating it to a Burnside average (or to a fraction such as `1/6`,
  `7/12`, `1/24`) is a type error: an average is not a Mark. In that reading
  the conjecture is ill-typed rather than false, and we say so plainly rather
  than pretend otherwise.

Either way the conjecture as filed cannot stand: the definite
Burnside-average equation it writes is false, and the strict Mark reading is
not a well-posed statement. We claim no more than this.

## Files

| File | Description |
|:-----|:------------|
| `README.md` | This document: verdict, bilingual quote, scope distinction, the `(3,1)` witness, general range, non-integrality, honest caveat, file list, repro commands, rule-3 status. |
| `main.tex` | LaTeX source of the disproof (standalone `article`), compiles with `tectonic --outdir build main.tex`. |
| `build/main.pdf` | PDF produced by that command. |
| `reproduce.py` | Python 3, standard library only (no `sympy`/`numpy`): enumerates `S_3` from all 27 functions, computes `Fix_k` for `k = 1, 2`, Burnside averages as exact `Fraction`s, self-written Stirling routine and closed-form cross-check, the `1 ≠ 1/6` cross-multiplication (`6 ≠ 1`), and the 2-transitivity classification by orbit count on ordered distinct pairs; prints `PASS`/`FAIL`, non-zero exit on failure. |
| `lean4/lean-toolchain` | Pins `leanprover/lean4:v4.33.1`. |
| `lean4/lakefile.toml` | Lake config; library `tlmc1752`, no dependencies. |
| `lean4/Main.lean` | Lean 4 formalisation, core Lean only (`import Std`, no Mathlib, no `Finset`, no `sorry`, no `native_decide`). |
| `lean4/Check.lean` | `#print axioms` audit for every theorem. |
| `lean4/README.md` | Statement table, proof strategy, axiom audit, scope note. |

## Reproducing

Python (dependency-free, runs in well under a second):

```sh
python3 reproduce.py
```

It enumerates the 27 functions `{0,1,2} → {0,1,2}` and keeps the 6
bijections; computes `Fix_k` for `k = 1, 2` setwise; forms Burnside sums and
averages as exact `fractions.Fraction`s; cross-checks `k!·S(n,k)/n!` against a
self-written Stirling recurrence (`S(n,k) = k·S(n−1,k) + S(n−1,k−1)`); asserts
`1 ≠ 1/6` by cross-multiplication (`6 ≠ 1`); and classifies which `(n,k)`
actions with `2 ≤ n ≤ 7` are 2-transitive by counting orbits on ordered pairs
of distinct `k`-subsets. It exits `0` on `PASS`.

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

## Formalisation summary

`lean4/Main.lean` formalises the core of the `(3,1)` witness in core Lean.
Since `Nat.factorial` and `Finset` are absent from `import Std`, it hand-rolls
`fact` and `stirling2`, enumerates `S_3` as the `eraseDups.length == 3`
functions among all 27 on `Fin 3`, and computes `Fix_1` as
`List.countP (fun s => f s == s)`. Both sides share the denominator `|G| = 6`,
so the mismatch reduces to the `Nat` inequality `6 ≠ 1` (no `Rat`, and no
`decide` on rationals, which `decide` cannot reduce). The theorems:

```
theorem perms_length : perms.length = 6
theorem burnsideSum_eq : burnsideSum = 6
theorem formula_val : fact 1 * stirling2 3 1 = 1
theorem burnside_average_is_one : burnsideSum = perms.length
theorem mismatch : burnsideSum ≠ fact 1 * stirling2 3 1
theorem one_ne_one_sixth_cross : (1 : Nat) * 6 ≠ (1 : Nat) * 1
```

Observed audit (`lake env lean Check.lean`), no `sorryAx` anywhere:

```
'Tlmc1752.perms_length' depends on axioms: [propext]
'Tlmc1752.burnsideSum_eq' depends on axioms: [propext]
'Tlmc1752.formula_val' does not depend on any axioms
'Tlmc1752.burnside_average_is_one' depends on axioms: [propext]
'Tlmc1752.mismatch' depends on axioms: [propext]
'Tlmc1752.one_ne_one_sixth_cross' does not depend on any axioms
```

## Status against the submission rules

Rule 3 requires each submission to contain the LaTeX source, a PDF document,
and a Lean 4 project.

- **LaTeX source** — present (`main.tex`), a standalone `article` using only
  `geometry`, `amsmath`, `amssymb`, `amsthm`, `array`, `parskip`, `booktabs`;
  compiles with `tectonic --outdir build main.tex`.
- **PDF document** — present at `build/main.pdf` (non-empty, produced by that
  command).
- **Lean 4 project** — present under `lean4/`, with `lean-toolchain`,
  `lakefile.toml`, `Main.lean`, `Check.lean`, and a `README.md`. It formalises
  `perms_length`, `burnsideSum_eq`, `formula_val`, `burnside_average_is_one`,
  `mismatch`, and `one_ne_one_sixth_cross`. It uses core Lean only (no Mathlib)
  and contains no `sorry`; the audit reports no `sorryAx`.
