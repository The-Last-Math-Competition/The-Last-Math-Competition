# Disproof of conjecture `00000001097`

**Verdict: FALSE.**

This submission disproves conjecture `00000001097` as stated. The refutation is
unconditional and elementary. The mean root count of the trinomial
$x^d + ax + b$ over $\mathbb{F}_q$ is **exactly $1$** for every prime power $q$ and
every degree $d$; the conjecture's claimed "main term" is strictly larger than $1$
and is in fact the *second moment* $2 - 1/q$ in the case $\gcd(d-1,q-1)=1$; and the
conjectured variance is wrong by exactly $1$. At $q=5$, $d=2$ the conjecture asserts
both $9/5$ and $1$ for the same mean, so it is internally inconsistent.

## The conjecture

> **Definition:** The mean root count of the trinomial $x^d + ax + b$ over
> $\mathbb{F}_q$ is the expectation over uniform $(a,b) \in \mathbb{F}_q^2$.
> **Conjecture:** The mean equals $1 + (q-1)/q^{\gcd(d-1,q-1)}$ as the main term;
> when $\gcd(d-1,q-1) = 1$ the mean is exactly $1$, and the variance of the mean is
> $2 - 1/q$.

Original statement (English and Chinese) as filed in `conjectures/00000001097.md`:

> **English.** Definition: The mean root count of the trinomial x^d + ax + b over F_q
> is the expectation over uniform (a,b) ∈ F_q². Conjecture: The mean equals
> 1 + (q−1)/q^{gcd(d−1,q−1)} as the main term; when gcd(d−1,q−1) = 1 the mean is
> exactly 1, and the variance of the mean is 2 − 1/q.
>
> **中文。** 定义：三项多项式 x^d+ax+b 在 F_q 上的根数均值指对均匀 (a,b)∈F_q² 的期望。
> 猜想：该均值为 1+(q−1)/q^{gcd(d−1,q−1)} 的显式主项;当 gcd(d−1,q−1)=1 时均值恰为 1,
> 均值的方差为 2−1/q。

## Why it is false

Write $N(a,b) = \#\{x \in \mathbb{F}_q : x^d + ax + b = 0\}$ for the root count of a
single trinomial, so the mean is
$M(q,d) = \frac{1}{q^2}\sum_{a,b \in \mathbb{F}_q} N(a,b)$.

### 1. Exact value: the mean is exactly $1$, always

**Theorem.** For every prime power $q$ and every $d \ge 1$,
$$M(q,d) = 1.$$

*Proof.* Count triples. By definition,
$$q^2 \cdot M(q,d) = \#\{(a,b,x) \in \mathbb{F}_q^3 : x^d + ax + b = 0\}.$$
Fix $x \in \mathbb{F}_q$ and $a \in \mathbb{F}_q$. The equation $x^d + ax + b = 0$ is
linear in $b$ with coefficient $1$, so it has exactly one solution, namely
$$b = -x^d - ax.$$
Hence for each of the $q$ choices of $x$ and the $q$ choices of $a$ there is exactly
one admissible $b$: the number of triples is $q \cdot q = q^2$. Therefore
$M(q,d) = q^2/q^2 = 1$. $\square$

No hypothesis on $q$ or $d$ is used beyond $\mathbb{F}_q$ being a field, in which
$b \mapsto x^d + ax + b$ is a bijection of $\mathbb{F}_q$.

### 2. The claimed main term is therefore wrong

Since $q > 1$ implies $q - 1 > 0$ and $q^{g} > 0$ with $g = \gcd(d-1,q-1) \ge 1$, the
claimed quantity
$$1 + \frac{q-1}{q^{\gcd(d-1,q-1)}}$$
is **strictly greater than $1$**. By Theorem 1 the true mean is exactly $1$, so the
exact formula in the conjecture is false. For example
$1 + 4/5 = 9/5 \ne 1$ at $q=5$, $d=2$.

### 3. Internal contradiction at $q = 5$, $d = 2$

Take $q = 5$ and $d = 2$. Then
$$\gcd(d-1,\,q-1) = \gcd(1,4) = 1.$$
The conjecture then asserts, in the same sentence:

* the mean equals $1 + (5-1)/5^{1} = 1 + 4/5 = 9/5$; **and**
* because $\gcd(d-1,q-1)=1$, the mean is **exactly $1$**.

Since $9/5 \ne 1$, these two clauses contradict each other. The same happens for every
$q > 1$ with $\gcd(d-1,q-1)=1$ (e.g. $q = 7$, $d = 2$: $\gcd(1,6)=1$ and
$1 + 6/7 = 13/7 \ne 1$). The conjecture is thus internally inconsistent, independently
of which formula one regards as authoritative.

### 4. The variance clause is also false

Let $N = N(a,b)$ for uniform $(a,b)$. The exact second moment is
$$\mathbb{E}[N^2] = 2 - \frac{1}{q},$$
as computed below (this holds for every $d$). Since $\mathbb{E}[N] = 1$ by Theorem 1,
the exact variance is
$$\operatorname{Var}(N) = \mathbb{E}[N^2] - (\mathbb{E}[N])^2
= \left(2 - \frac{1}{q}\right) - 1 = 1 - \frac{1}{q},$$
not $2 - 1/q$. The conjectured number $2 - 1/q$ is exactly the second moment
$\mathbb{E}[N^2]$; the conjecture has mislabelled the second moment as the variance.
For $q = 3, 5, 11$ the true variances are $2/3$, $4/5$, $10/11$ respectively, all
strictly less than the claimed $5/3$, $9/5$, $21/11$.

**Computation of the second moment.** For fixed distinct $x \ne y \in \mathbb{F}_q$,
the system
$$x^d + ax + b = 0, \qquad y^d + ay + b = 0$$
is solved by subtracting: $(x^d - y^d) + a(x-y) = 0$, and since $x - y \ne 0$ is
invertible, this determines a unique $a = -(x^d - y^d)/(x - y)$, after which
$b = -x^d - ax$ is determined. So each of the $\binom{q}{2}$ unordered pairs of
distinct points is a common root pair for exactly one $(a,b)$. Summing $N^2$ over all
$(a,b)$ counts ordered pairs of roots, so
$$\sum_{a,b} N(a,b)^2 = \sum_{a,b} N(a,b) + 2\binom{q}{2} = q^2 + q(q-1) = q(2q-1),$$
using $\sum_{a,b} N(a,b) = q^2$ from Theorem 1. Dividing by $q^2$ gives
$\mathbb{E}[N^2] = (2q-1)/q = 2 - 1/q$. $\square$

## The strongest objection: "as the main term" might mean asymptotic

A charitable maintainer could reply that $1 + (q-1)/q^{\gcd(d-1,q-1)}$ is offered only
"as the main term", i.e. as an asymptotic leading term rather than an exact finite
value, so that the strict equality $M(q,d) = 1$ does not refute it. This reading does
not save the conjecture, for three independent reasons.

1. **The conjecture is a statement about finite $q$, and the correction is not
   negligible.** The formula is asserted for finite prime powers $q$ (the definition
   fixes a single $\mathbb{F}_q$), and "main term" language still commits the leading
   term to be correct up to an error term. Here the exact mean is the constant $1$: a
   quantity identically equal to $1$ has leading term $1$, full stop. The proposed
   correction $(q-1)/q^{g}$ is not an error term tending to $0$ in the relevant
   regime; when $g = 1$ it equals $(q-1)/q > 1/2$ for all $q \ge 2$, which is
   $O(1)$ and can never be absorbed into "lower order" terms. So even as an asymptotic
   claim, the asserted leading constant is wrong.
2. **Clause 3 is a flat contradiction that "main term" cannot reconcile.** The
   sentence simultaneously asserts the value $1 + (q-1)/q^{g}$ *and*, when $g=1$, that
   the mean "is exactly $1$". These are two clauses of one sentence; reading the first
   as a main term and the second as exact still yields $9/5$ versus $1$ at $q=5$,
   $d=2$. A phrase about asymptotics cannot make a number simultaneously equal to
   $9/5$ and to $1$.
3. **The variance clause is separately and unconditionally false.** Regardless of how
   one reads "main term", the claim "the variance is $2 - 1/q$" is a plain arithmetic
   assertion, and the exact variance is $1 - 1/q \ne 2 - 1/q$ for every $q > 1$. The
   claimed value is the second moment, not the variance.

Thus every clause of the conjecture fails: the exact mean is $1$, not
$1 + (q-1)/q^{g}$; the value $1 + (q-1)/q^{g}$ coincides with the second moment
$2 - 1/q$ when $g=1$, not with the mean; and the variance is $1 - 1/q$, not
$2 - 1/q$.

## Numerical summary

Exact values from `reproduce.py` (means are exact `Fraction`s):

| $q$ | $d$ | $g=\gcd(d-1,q-1)$ | true mean | claimed $1+(q-1)/q^g$ | $\mathbb{E}[N^2]$ | true variance $1-1/q$ | claimed variance $2-1/q$ |
|----:|----:|:-----------------:|:---------:|:---------------------:|:-----------------:|:---------------------:|:------------------------:|
| 5  | 2 | 1 | 1 | 9/5  | 9/5  | 4/5  | 9/5  |
| 5  | 3 | 2 | 1 | 29/25| 9/5  | 4/5  | 9/5  |
| 7  | 2 | 1 | 1 | 13/7 | 13/7 | 6/7  | 13/7 |
| 11 | 2 | 1 | 1 | 21/11| 21/11| 10/11| 21/11|
| 11 | 5 | 2 | 1 | 131/121 | 21/11 | 10/11 | 21/11 |
| 13 | 3 | 2 | 1 | 181/169 | 25/13 | 12/13 | 25/13 |

In every row the true mean is $1$, the claimed main term exceeds $1$, the true
variance is $1 - 1/q$, and the claimed "variance" equals the second moment.

## Files

| File | Description |
|:-----|:------------|
| `README.md` | This document: verdict, exact-value proof, internal contradiction, variance correction, and the "main term" objection with rebuttal. |
| `main.tex` | Standalone LaTeX source of the disproof. Compiles with `tectonic main.tex`. |
| `build/main.pdf` | PDF produced by `tectonic --outdir build main.tex` (tectonic 0.17.0); checked-in build artifact. |
| `reproduce.py` | Python 3 standard-library program: brute-forces $M(q,d)$, the claimed formula, the second moment and the variance for $q \in \{5,7,11,13\}$, $d \in \{2,3,5\}$, and prints a PASS/FAIL summary; `python3 reproduce.py` exits 0 and prints `PASS`. |
| `lean4/` | Lean 4 formalisation of the elementary core, core Lean only (no Mathlib), no `sorry`; built with `lake build` and axiom-checked with `lake env lean Check.lean`. |

## Reproducing

The numerical checks are dependency-free and run in seconds:

```sh
python3 reproduce.py
```

It prints, for every $(q,d)$ tested, the exact mean as a `Fraction`, the claimed
formula value, the exact second moment, and the exact variance, then asserts in each
case that the mean is $1$, that the claimed value is not $1$, that the second moment is
$2 - 1/q$, and that the variance is $1 - 1/q$. It ends with a `PASS`/`FAIL` summary and
exits non-zero on `FAIL`.

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

Rule 3 requires each submission to contain the LaTeX source code, a PDF document, and
a Lean 4 project.

- **LaTeX source** — present (`main.tex`), a standalone `article` using only
  `amsmath`, `amssymb`, `amsthm`, and `geometry`/`parskip`, designed to compile with
  `tectonic main.tex`.
- **PDF document** — `build/main.pdf`, produced by
  `tectonic --outdir build main.tex` (tectonic 0.17.0) and checked in; the source
  uses no external figures or non-standard packages.
- **Lean 4 project** — present under `lean4/`, with `lean-toolchain`, `lakefile.toml`,
  `Main.lean`, and `Check.lean`. It formalises the countable core of the disproof: the
  claimed main term at $q=5$, $d=2$ is $9/5$ and is not $1$; the explicit enumeration
  over `Fin 5` shows the exact mean is $1$; the arithmetic of the second moment and
  variance for $q=5$ is recorded; and the final theorem
  `conjecture_00000001097_false` collects the exact value together with the false
  claim. It is written in core Lean only (no Mathlib) and contains no `sorry`; it
  builds with `lake build` on `leanprover/lean4:v4.33.1` (exit 0, no errors), and
  `lake env lean Check.lean` reports dependencies on
  `[propext, Classical.choice, Quot.sound]` (some on none), with no `sorryAx` and
  no `Lean.ofReduceBool`.
- **PDF / Lean build note** — Both were produced and verified: `build/main.pdf` is
  the compiled PDF from `tectonic --outdir build main.tex` (tectonic 0.17.0), and
  the Lean project builds with `lake build` on the pinned toolchain
  `leanprover/lean4:v4.33.1` ("Build completed successfully", exit 0, no `sorry`).
  `Check.lean` prints the axioms of each theorem, confirming the absence of
  `sorryAx`, of `Lean.ofReduceBool`, and of Mathlib dependencies;
  `python3 reproduce.py` exits 0 and prints `PASS`.
