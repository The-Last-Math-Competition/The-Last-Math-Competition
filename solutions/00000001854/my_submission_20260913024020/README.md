# Disproof of TLMC Conjecture 00000001854

**Verdict: FALSE.**

## Conjecture (as stated)

> Definition: Counting random matrices over F_q.
> Conjecture: `#{M ∈ Mat_n(F_q) : char poly squarefree} = q^{n²}·∏(1 − q^{−i²})`
> is an exact closed form (squarefree char-poly counting).

## Counterexample (n = 1, minimal dimension)

Every matrix in `Mat_1(F_q)` is `[a]` for some `a ∈ F_q`, and its characteristic
polynomial is `X − a`. A degree-one polynomial over a field has derivative `1`,
so `gcd(X − a, (X − a)') = gcd(X − a, 1) = 1`: the characteristic polynomial of
every 1×1 matrix is squarefree. Hence the true count is

```
#{M ∈ Mat_1(F_q) : char poly squarefree} = |F_q| = q.
```

The conjectured formula (product read over `i = 1..n`, i.e. the single factor
`1 − q^{−1}`) gives

```
q^{1}·(1 − q^{−1}) = q − 1 ≠ q.
```

Explicit values, confirmed by brute-force enumeration in `reproduce.py`:

| q   | true count (enumerated) | formula (reading A: i = 1..n) |
|-----|-------------------------|-------------------------------|
| 2   | 2                       | 1                             |
| 3   | 3                       | 2                             |
| 4   | 4 (F_4 = F_2[ω], ω²=ω+1)| 3                             |
| 5   | 5                       | 4                             |

Every prime power q ≥ 2 is a counterexample; the "exact closed form" already
fails at the smallest possible dimension.

## Second corroboration (n = 2, q = 2)

Full enumeration of all 16 matrices of `Mat_2(F_2)` (char poly `det(XI − M)`
computed with polynomial arithmetic over F_2, squarefreeness via
`gcd(f, f')`): the count is **8**, while the formula gives

```
2^{4}·(1 − 2^{−1})(1 − 2^{−4}) = 16 · (1/2) · (15/16) = 15/2,
```

which is not even an integer — impossible for an exact count of a finite set.

## Boundary of the refutation

The conjecture does not specify the index range of the product
`∏(1 − q^{−i²})`. The refutation above targets the **literal "exact" assertion**
and covers both natural readings:

* **Reading A** (product over `i = 1..n`, matching the degree): fails at n = 1
  (`q − 1 ≠ q`) and at n = 2, q = 2 (a non-integer `15/2` vs. the integer 8).
* **Reading B** (infinite product): at n = 1 the right-hand side is
  `q · ∏_{i≥1}(1 − q^{−i²}) < q` because every factor lies in `(0, 1)`, while
  the left-hand side is exactly `q`. Computed exactly with rationals:
  q = 2 gives ≈ 0.9357, q = 3 ≈ 1.9752, q = 4 ≈ 2.9883, q = 5 ≈ 3.9936 —
  never equal to the true count q.

If the product was intended relative to some other measure (e.g. a density
normalized by `q^{−n²}`), the statement as written is ambiguous rather than
exact; we refute the statement in the literal form quoted above. For
reference, the classical closed form for the *number of monic squarefree
polynomials* of degree n over F_q is `q^n − q^{n−1}` (for n ≥ 2), which is a
statement about polynomials, not matrices, and does not match the conjectured
expression either.

## Contents

* `reproduce.py` — self-contained brute-force check (Python ≥ 3.8, no
  dependencies). Implements F_q for prime q and F_4, polynomial arithmetic
  (division / gcd / derivative) over these fields, enumerates all matrices, and
  asserts every inequality reported above:
  `python3 reproduce.py`
* `main.tex`, `build/main.pdf` — formal write-up.
* `lean4/` — Lean 4 project (toolchain `leanprover/lean4:v4.33.1`, **no
  dependencies, zero axioms, zero `sorry`**) formalizing the `n = 1, q = 2`
  numeric refutation: the enumerated count `2` and the formula value `1`
  (exact fraction over `Nat`) are both computed by `rfl` and proved distinct
  by `decide` + exact cross-multiplication.

## Honesty note on the Lean formalization

Lean 4 core has no `Polynomial` library (that lives in Mathlib, which this
project deliberately does not depend on), and core `Rat` operations do not
reduce inside the Lean kernel. The Lean proof therefore formalizes the
*numeric* content of the counterexample — the count `2` at n = 1, q = 2, the
formula value `1` (encoded as an exact fraction over kernel-computable natural
number arithmetic), and their inequality (via exact cross-multiplication) —
with all quantities computed by `rfl`/`decide`. The mathematical reason every
1×1 matrix has squarefree characteristic polynomial (degree one ⇒ derivative 1
⇒ `gcd(f, f') = 1`) is argued in the documents (`README.md`, `main.tex`) and in
comments in `lean4/Main.lean`. The Python enumeration in `reproduce.py`
independently verifies the squarefreeness claim generically via `gcd(f, f')`
for q = 2, 3, 4, 5.

## Verdict

The conjecture is **false**: the proposed expression is not an exact closed
form for the number of matrices with squarefree characteristic polynomial.
