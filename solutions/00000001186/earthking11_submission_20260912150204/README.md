# Disproof of conjecture `00000001186`

**Verdict: FALSE.**

This submission disproves conjecture `00000001186` as stated, by exhibiting three
independent internal contradictions. The refutation is unconditional: it does not
depend on the classification of finite simple groups, nor on any deep group theory.

## The conjecture

> **Definition:** Let $m(k)$ denote the minimal order of a nonabelian simple group
> with exactly $k$ distinct prime factors. **Conjecture:** $m(3) = 60$ (A₅),
> $m(4) = 504$ (PSL₂(8)), $m(5) = 660$ (PSL₂(11)); and $m(k)/m(k-1) \le 4$ for all
> $k$, with equality at $k = 4$.

Original statement (English and Chinese) as filed in
`conjectures/00000001186.md`:

> **English.** Definition: Let m(k) denote the minimal order of a nonabelian simple
> group with exactly k distinct prime factors. Conjecture: m(3) = 60 (A₅), m(4) = 504
> (PSL₂(8)), m(5) = 660 (PSL₂(11)); and m(k)/m(k−1) ≤ 4 for all k, with equality at k = 4.
>
> **中文。** 定义：恰有 k 个不同素因子的非交换单群的最小阶记 m(k)。猜想：
> m(3)=60(A₅),m(4)=504(PSL₂(8)),m(5)=660(PSL₂(11)); 且序列 m(k)/m(k−1) ≤ 4 对一切 k,
> 等号在 k=4 时取得。

## Why it is false

The key observation is that "a group with exactly $k$ distinct prime factors" must,
by definition, have an order divisible by exactly $k$ distinct primes. The listed
orders do not match the indices they are assigned to.

### Contradiction 1: $504$ has three distinct prime factors, not four

$$504 = 2^3 \cdot 3^2 \cdot 7.$$

The distinct primes dividing $504$ are $2, 3, 7$ — exactly **three** of them. Every
group of order $504$ therefore has exactly $3$ distinct prime factors (the distinct
prime divisors of its order). Such a group can never have "exactly $4$ distinct
prime factors", so it cannot be the group whose minimal order defines $m(4)$.
Hence

$$m(4) \ne 504.$$

This is unconditional. It does not require knowing which group of order $504$ is
intended, nor whether any nonabelian simple group of order $504$ exists: *whatever*
group of order $504$ one takes, its order has only three distinct prime factors, and
the definition of $m(4)$ demands exactly four.

### Contradiction 2: $660$ has four distinct prime factors, not five

$$660 = 2^2 \cdot 3 \cdot 5 \cdot 11.$$

The distinct primes dividing $660$ are $2, 3, 5, 11$ — exactly **four** of them.
So no group of order $660$ has exactly $5$ distinct prime factors, and

$$m(5) \ne 660.$$

The value $660$ is in fact a natural candidate for $m(4)$, not for $m(5)$; it has
been mislabelled by one index.

### Contradiction 3: the ratio bound fails on the conjecture's own numbers

Using the conjecture's own listed values,

$$\frac{m(4)}{m(3)} = \frac{504}{60} = \frac{42}{5} = 8.4 > 4.$$

This directly contradicts the conjectured inequality $m(k)/m(k-1) \le 4$ for all
$k$, and it contradicts the assertion that equality holds at $k = 4$. The
contradiction is pure arithmetic on the numbers supplied in the statement itself,
independent of which "groups" those numbers name.

Each of the three contradictions suffices on its own to falsify the conjecture. They
are mutually independent in the sense that removing any one of them leaves the
conjecture false by the other two.

## Does the alternative reading "prime factors counted with multiplicity" rescue it?

A reader might propose reading "exactly $k$ distinct prime factors" as "the order
has exactly $k$ prime factors counted with multiplicity" (i.e. $\Omega(n) = k$).
This reading rescues nothing.

Under the multiplicity reading:

| $n$ | factorisation | $\omega(n)$ (distinct) | $\Omega(n)$ (with multiplicity) |
|----:|:--------------|:----------------------:|:-------------------------------:|
| $60$  | $2^2 \cdot 3 \cdot 5$        | 3 | **4** |
| $504$ | $2^3 \cdot 3^2 \cdot 7$      | 3 | **6** |
| $660$ | $2^2 \cdot 3 \cdot 5 \cdot 11$ | 4 | **5** |

- $60 = 2^2 \cdot 3 \cdot 5$ has $\Omega(60) = 2 + 1 + 1 = 4$, not $3$. Under the
  multiplicity reading, $m(3) = 60$ already fails, so the very first listed value is
  inconsistent.
- $504$ has $\Omega(504) = 3 + 2 + 1 = 6 \ne 4$.
- $660$ has $\Omega(660) = 2 + 1 + 1 + 1 = 5$. This is the only listed value that
  becomes consistent under the multiplicity reading — but it is assigned to
  $m(5)$, so it would make $660$ a candidate for $m(5)$, not for $m(4)$.

Thus switching to the multiplicity reading breaks the base case $m(3) = 60$ and
still leaves $m(4) = 504$ false. It introduces no reading of the definition under
which all the listed values are simultaneously correct, and the ratio bound
$504/60 = 8.4 > 4$ fails under either reading (it is a ratio of the listed numbers,
not of any count). The conjecture is false as stated regardless of this ambiguity.

## True values on the standard reading (context, not the refutation)

The core refutation above is the three contradictions and does not need the values
below. For context, on the standard reading ($\omega(n)$, the number of distinct
primes dividing the order), the true initial values are:

$$m(3) = 60 \;(\mathrm{A}_5), \qquad m(4) = 660 \;(\mathrm{PSL}_2(11)).$$

Indeed $660 = 2^2 \cdot 3 \cdot 5 \cdot 11$ has exactly four distinct prime divisors,
and every nonabelian simple group of order strictly less than $660$ has at most
three distinct prime divisors. The relevant orders occurring below $660$ are

$$60 = 2^2\cdot 3\cdot 5,\quad 168 = 2^3\cdot 3\cdot 7,\quad
360 = 2^3\cdot 3^2\cdot 5,\quad 504 = 2^3\cdot 3^2\cdot 7,$$

each with exactly three distinct prime divisors (and $|\mathrm{A}_5| = 60$,
$|\mathrm{PSL}_2(7)| = 168$, $|\mathrm{A}_6| = 360$, while $504$ is not the order of
any nonabelian simple group). So on the standard reading the statement's $m(4) = 504$
is simply wrong, and its $m(5) = 660$ is a one-index mislabel of the correct $m(4)$.
We emphasise that this paragraph is context only; the disproof rests solely on the
three contradictions, of which Contradiction 1 and Contradiction 2 require only the
factorisations $504 = 2^3\cdot3^2\cdot7$ and $660 = 2^2\cdot3\cdot5\cdot11$, and
Contradiction 3 requires only $504/60 = 8.4 > 4$.

## Files

| File | Description |
|:-----|:------------|
| `README.md` | This document: verdict, the three contradictions, discussion, reproduction instructions. |
| `main.tex` | LaTeX source of the disproof, with the factorisation table. Compiles standalone with `tectonic main.tex`. |
| `build/main.pdf` | PDF produced by `tectonic --outdir build main.tex` (tectonic 0.17.0); checked-in build artifact. |
| `reproduce.py` | Python 3 program that factors $60, 504, 660$, prints $\omega$ and $\Omega$, checks the three contradictions, and prints a PASS/FAIL summary; `python3 reproduce.py` exits 0 and prints `PASS`. |
| `lean4/` | Lean 4 formalisation of the arithmetic core, core Lean only (no Mathlib), no `sorry`; built with `lake build` and axiom-checked with `lake env lean Check.lean`. |

## Reproducing

The numerical checks are dependency-free and run in seconds:

```sh
python3 reproduce.py
```

It prints the factorisations of $60$, $504$, $660$ together with $\omega$ (distinct)
and $\Omega$ (with multiplicity), checks the three contradictions, and ends with a
`PASS`/`FAIL` summary. A `FAIL` (exit status non-zero) indicates that a claimed
contradiction did not verify.

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
  `amsmath`, `amssymb`, `amsthm`, and `array`, designed to compile with
  `tectonic main.tex`.
- **PDF document** — `build/main.pdf` is produced by
  `tectonic --outdir build main.tex` (tectonic 0.17.0) and checked in; the source
  builds without external figures or non-standard packages.
- **Lean 4 project** — present under `lean4/`, with `lean-toolchain`,
  `lakefile.toml`, `Main.lean`, and `Check.lean`. It formalises the arithmetic core of
  the disproof: $\omega(504) = 3$, $\omega(660) = 4$, the facts $\omega(504) \ne 4$ and
  $\omega(660) \ne 5$, the ratio fact $504/60 > 4$, and a final theorem
  `conjecture_00000001186_false` collecting the contradictions. It is written in core
  Lean only (no Mathlib) and contains no `sorry`; it builds with `lake build` on
  `leanprover/lean4:v4.33.1` (exit 0, no errors), and `lake env lean Check.lean`
  reports dependencies on `[propext]` only (some on none), with no `sorryAx`, no
  `Lean.ofReduceBool`, and no Mathlib dependency.
- **PDF build note** — `build/main.pdf` is the compiled PDF from
  `tectonic --outdir build main.tex` (tectonic 0.17.0), and the Lean project builds
  and checks on the pinned toolchain `leanprover/lean4:v4.33.1`:
  `lake build` completes successfully (exit 0, no errors, no `sorry`) and
  `lake env lean Check.lean` prints the axioms of each theorem, confirming the
  absence of `sorryAx`, of `Lean.ofReduceBool`, and of Mathlib dependencies.
  `python3 reproduce.py` exits 0 and prints `PASS`.
