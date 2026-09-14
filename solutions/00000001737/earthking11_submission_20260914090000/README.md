# Disproof of conjecture `00000001737`

**Verdict: FALSE.**

This submission disproves conjecture `00000001737` as stated. The refutation is
unconditional, completely elementary, and does not depend on any unproved
hypothesis: for the two-element prime set `S = {2,3}`, the projective line minus
three points `P¹ ∖ {0,1,∞}` has **21** `S`-integral points, not at most `12`.
Since `21 > 12`, the conjectured maximum of `12` is false.

The submission is a **lower-bound witness**: it proves `max ≥ 21 > 12`. It does
*not* compute the exact maximum over all two-element prime sets (that requires
the `S`-unit theorem / linear forms in logarithms). A lower bound that already
exceeds `12` is all that is needed to refute an upper bound of `12`.

## The conjecture

Quoted verbatim from `conjectures/00000001737.md`:

> **English.** Conjecture: The maximal possible number of S-integral points of
> P¹ ∖ {0,1,∞} with S of two primes is 12; a tightening of Evertse's general
> bound, with the extremum exhausted by explicit hyperelliptic covers.
>
> **中文。** 猜想：ℙ¹∖\{0,1,∞\} 的 S-整点(S={2 个素\}) 的最大可能解数为
> 12;Evertse 的一般界的紧化,极值由显式超椭圆覆盖穷举。

## The definitional point (the naive reading is degenerate)

Let `S = {p₁,p₂}` be a set of two primes and `Z_S = Z[1/p₁,1/p₂]` the ring of
`S`-integers. The scheme `P¹ ∖ {0,1,∞}` over `Z` is
`Spec Z[x, 1/x, 1/(1−x)]`. An `S`-integral point is a `Z`-morphism
`Spec Z_S → P¹ ∖ {0,1,∞}`, i.e. a rational `x` with

```
x ∈ Z_S^×   and   1 − x ∈ Z_S^× ,
```

equivalently `x`, `1/x`, `1/(1−x)` all have no prime outside `S` in numerator or
denominator. Note that `1/x` integral forces `v_p(x) = 0` for every `p ∉ S`.

**Why the definition matters.** The one-sentence version "a point is `S`-integral
if it is not one of `0, 1, ∞` and is integral outside `S`" is degenerate: it
would already be infinite, because `Z_S` is infinite and every `x ∈ Z_S` with
`x ≠ 0,1` would qualify. The integrality must be imposed at the whole divisor
`{0,1,∞}`, which is exactly the condition that `x` **and** `1 − x` are
`S`-units. Under this (standard, and the only finite) definition, writing
`y = 1 − x` gives the classical **`S`-unit equation**

```
x + y = 1 ,   x, y S-units.
```

Mahler (1933) proved finiteness; effective bounds go back to Győry (1979).
The count of solutions in `x` is the number of `S`-integral points.

## The decisive witness: `S = {2, 3}` has exactly 21 points

There are exactly 21 `S`-integral points for `S = {2,3}`, namely

```
−8, −3, −2, −1, −1/2, −1/3, −1/8, 1/9, 1/4, 1/3, 1/2, 2/3, 3/4,
8/9, 9/8, 4/3, 3/2, 2, 3, 4, 9.
```

Each has `x` and `1 − x` of the form `±2^a 3^b`; the pairs `(x, 1−x)` are

```
(−8,9)  (−3,4)  (−2,3)  (−1,2)  (−1/2,3/2)  (−1/3,4/3)  (−1/8,9/8)
(1/9,8/9) (1/4,3/4) (1/3,2/3) (1/2,1/2) (2/3,1/3) (3/4,1/4) (8/9,1/9)
(9/8,−1/8) (4/3,−1/3) (3/2,−1/2) (2,−1) (3,−2) (4,−3) (9,−8)
```

so every entry is a unit of `Z[1/6]`, i.e. an `S`-unit. The 21 rationals are
pairwise distinct. Therefore

```
#{S-integral points of P¹ ∖ {0,1,∞}} for S = {2,3} = 21 > 12 ,
```

and the conjectured maximum is refuted.

**How they are verified.** `reproduce.py` (Python 3 stdlib only) enumerates all
`x = ±2^a 3^b` with exponent bound `B` and tests `x ≠ 0,1` and `1 − x` an
`S`-unit using exact `fractions.Fraction` arithmetic. It then:

- reports the full 21-element list and its length;
- checks the count is **stable across exponent bounds**
  `B ∈ {5,10,20,40,60,80,100,120,150}` (all give 21), so the enumeration is
  saturated — this is also why the count is exactly 21, not merely `≥ 21`;
- checks all 21 are pairwise distinct by explicit cross-multiplication
  `p₁q₂ ≠ p₂q₁`, and that each has a unique representation `±2^a 3^b`;
- checks `21 > 12`;
- computes the counts for all two-element prime sets `p < q ≤ 23`.

The exact same computation was reproduced independently during preparation, and
the list matches OEIS A362567 exactly (below).

## OEIS A362567

The sequence **A362567**, "Number of rational solutions to the `S`-unit equation
`x + y = 1`, where `S = {prime(i) : 1 ≤ i ≤ n}`", has data beginning

```
a(0)=0, a(1)=3, a(2)=21, a(3)=99, ...
```

(offset 0). Its `a(2) = 21` is exactly our count for `S = {2,3}`, and its
EXAMPLE section lists precisely the 21 solutions exhibited above. This provides
an independent literature confirmation that the true value is 21, not 12. (The
sequence also records Mahler 1933 for finiteness and Győry 1979 for effective
bounds.)

## Max over all two-element prime sets

Exact counts for every `S = {p,q}` with `p < q ≤ 23`:

| `S` | count |
|:----|------:|
| `{2,3}` | **21** |
| `{2,5}`, `{2,7}`, `{2,17}` | 9 |
| `{2,11}`, `{2,13}`, `{2,19}`, `{2,23}` | 3 |
| any `{p,q}` with both `p,q` odd | 0 |

Observations:

- the maximum over these sets is `21`, attained at `S = {2,3}`;
- the only counts that occur are `0, 3, 9, 21`; **no two-element prime set has
  exactly `12`**;
- two odd primes give `0` points.

## Comparison with Evertse's bound

Evertse's general bound for the `S`-unit equation is **exponential** in `|S|`;
the commonly quoted form is

```
N(S) ≤ 3·7^(2|S|+3) .
```

For `|S| = 2` this is `3·7⁷ = 3·823543 = 2 470 629`, which is not `12` (nor
`12`-ish in any sense). For `|S| = 1` it is `3·7⁵ = 50409`; the true value is
`a(1) = 3`. So:

- `12` is **not** Evertse's bound for `|S| = 2` — that bound is `2 470 629`;
- `12` is not Evertse's bound for any small `|S|` either, and is not a standard
  bound in this circle of ideas at all;
- the claim "a tightening of Evertse's general bound to 12" is therefore false
  both as a *maximum* (the maximum for `|S| = 2` is `21`) and as an *upper
  bound* (Evertse's is exponential). The genuine exact values `3, 21, 99` are
  far below Evertse's bound; closing that gap is the hard part of `S`-unit
  computations, and has nothing to do with `12`.

## The "explicit hyperelliptic covers" clause is a non-sequitur

`P¹ ∖ {0,1,∞}` has **genus 0**: removing points from the projective line does
not change its genus, and genus-0 curves are not hyperelliptic in the relevant
sense. There is no hyperelliptic curve (of genus ≥ 1), no cover, and no
hyperelliptic-covering argument anywhere in the problem. The `S`-unit equation
`x + y = 1` lives on the torus `G_m²`; its finiteness comes from Mahler's
theorem and its effective resolution from linear forms in logarithms / lattice
reduction, not from hyperelliptic covers. The extremal two-element set
`S = {2,3}` is found by direct enumeration of `S`-units. We record the clause as
mathematically unrelated to the claim, and it does not rescue the conjecture.

## Framing: lower bound, not exact maximum

The logical shape is stated precisely to avoid overclaiming.

- We prove **existence** of 21 pairwise-distinct `S`-integral points for
  `S = {2,3}`; hence the maximum over two-element prime sets is `≥ 21`.
- Since `21 > 12`, the conjectured maximum of `12` is refuted. Nothing more is
  needed for the disproof.
- We do **not** claim to compute the exact maximum over all two-element prime
  sets. We do show the count for `S = {2,3}` is exactly `21` (saturated
  enumeration) and give exact counts for `p < q ≤ 23`, whose maximum is `21`.
  Proving no larger `S` does better requires the `S`-unit theorem and is out of
  scope here.
- Exact values for general `|S|` are the deep computations behind A362567; we
  only use `a(2) = 21` as a literature cross-check.

## Files

| File | Description |
|:-----|:------------|
| `README.md` | This document: verdict, bilingual quote, definitional point, the 21 points, OEIS citation, max table, Evertse comparison, hyperelliptic remark, framing, reproducibility, rule-3 status. |
| `main.tex` | LaTeX source of the disproof (standalone `article`), compiles with `tectonic main.tex`. |
| `build/main.pdf` | PDF produced by `tectonic --outdir build main.tex`. |
| `reproduce.py` | Python 3 (standard library only, no `sympy`): exact `Fraction` enumeration of `±2^a 3^b`, the full 21-element list, saturation checks, distinctness, counts for all prime pairs `p < q ≤ 23`, `PASS`/`FAIL`, non-zero exit on failure. |
| `lean4/lean-toolchain` | Pins `leanprover/lean4:v4.33.1`. |
| `lean4/lakefile.toml` | Lake configuration; library `Main`, no dependencies. |
| `lean4/Main.lean` | Lean 4 formalisation, core Lean only (`import Std`, no Mathlib, no `sorry`). |
| `lean4/Check.lean` | `#print axioms` audit for every theorem. |
| `lean4/README.md` | Statement table, proof strategy, scope note. |

## Reproducing

Python (dependency-free, about 10 seconds):

```sh
python3 reproduce.py
```

It prints the 21-element list, the saturation table, the pair-count table, and
the checks; it prints `PASS` and exits `0` exactly when every check holds.

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

`lake build` exits `0`; `Check.lean` prints `#print axioms` for every theorem
and reports no `sorryAx` (only `propext` and `Quot.sound`; the concrete
computations depend on no axioms at all).

## Status against the submission rules

Rule 3 requires each submission to contain the LaTeX source, a PDF document,
and a Lean 4 project.

- **LaTeX source** — present (`main.tex`), a standalone `article` using only
  `geometry`, `amsmath`, `amssymb`, `amsthm`, `array`, `parskip`, `booktabs`;
  compiles with `tectonic main.tex`.
- **PDF document** — present at `build/main.pdf` (5 pages, non-empty).
- **Lean 4 project** — present under `lean4/`, with `lean-toolchain`,
  `lakefile.toml`, `Main.lean`, `Check.lean`, and a `README.md`. It formalises
  the soundness of the smoothness test (`isSmooth_sound`), the faithfulness of
  the `S`-integrality predicate (`sIntegral_sound`), the integrality and
  pairwise distinctness of the 21 witnesses (`all_integral`, `all_distinct`),
  and the main statement
  `conjecture_00000001737_false : pts.length = 21 ∧ … ∧ 12 < pts.length`,
  together with the packaged lower-bound form `more_than_twelve_points` and the
  negated count bound `not_max_le_twelve`. It uses core Lean only (no Mathlib)
  and contains no `sorry`; the audit reports no `sorryAx`.
