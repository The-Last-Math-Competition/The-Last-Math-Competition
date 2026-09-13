# Submission for conjecture 00000001096 — verdict: FALSE

**Conjecture (00000001096).** The VC dimension of polynomial functions of
degree ≤ d over F_q^n is exactly n·d (for d < q).

**Verdict.** FALSE. Counterexample with n = 2, d = 2, q = 5 (note d = 2 < q = 5).

## Which definition is used

"VC dimension" is classically defined for **binary** function classes. Since
conjecture 00000001096 concerns F_q-valued functions, it must intend a
generalised notion. We use the standard, natural one:

> An m-point set S is **shattered** by a class H of F_q-valued functions when
> the evaluation map H → F_q^m is **surjective** onto F_q^m, i.e. when all
> q^m labellings of S are realisable by some member of H. The VC dimension is
> the largest size of a shattered set.

Under this definition the conjecture fails, as shown below. (With the classical
binary definition the statement is not even well typed, so this generalisation
is forced.)

## The counterexample

n = 2, d = 2, q = 5. The monomials of total degree ≤ 2 in two variables are

    1, x, y, x², xy, y²

— six functions, spanning a 6-dimensional space. The conjecture predicts
n·d = 4.

Take the six points

    (0,0), (0,1), (0,2), (1,0), (1,1), (2,0).

Their 6×6 evaluation matrix M (rows = points, columns = monomials) over F_5 is

    1 0 0 0 0 0
    1 0 1 0 0 1
    1 0 2 0 0 4
    1 1 0 1 0 0
    1 1 1 1 1 1
    1 2 0 4 0 0

Its determinant is ≡ 1 (mod 5) ≠ 0, so M is invertible over F_5. Hence the
evaluation map F_5^6 → F_5^6 on these points is bijective and **all 5^6 = 15625
labellings are realisable**: the six points are shattered. Therefore

    VC dim ≥ 6 > 4 = n·d,

contradicting the conjecture. In fact the six monomials span a 6-dimensional
space, so no 7-point set can be shattered (dimension count); thus the VC
dimension is exactly 6 here.

Even excluding the constant function, the five monomials x, y, x², xy, y²
shatter the five points (0,1), (0,2), (1,0), (1,1), (2,0): the corresponding
5×5 minor also has determinant ≡ 1 (mod 5). So the failure is not an artefact
of counting the constant monomial.

The root cause: the conjecture counts n·d, but degree-≤d polynomials span the
monomials with a_1 + … + a_n ≤ d, of dimension C(n+d, n) = C(4,2) = 6 for
n = d = 2.

## Contents

| Path | Description |
| --- | --- |
| `main.tex`, `build/main.pdf` | Standalone article with the generalised VC definition, the evaluation matrix, the determinant computation, and the shattering conclusion. |
| `reproduce.py` | Standard-library-only verification: builds M, computes det mod 5 = 1, confirms rank 6, inverts M over F_5, and verifies all 5^6 labellings are realisable. Prints `PASS`, exits 0. |
| `lean4/` | Lean 4 formalisation (core Lean + `Std` only; no Mathlib, no `sorry`, no `axiom`, no `native_decide`). |

## How to reproduce

    python3 reproduce.py                 # prints PASS, exit 0
    cd lean4 && lake build               # exit 0
    cd lean4 && lake env lean Check.lean # prints #print axioms

PDF:

    tectonic --outdir build main.tex     # writes build/main.pdf

(tectonic requires `build/` to exist; create it with `mkdir -p build` first on
versions that do not create it automatically.)

## Lean formalisation

See `lean4/README.md` for exactly what is formalised and what is documented
only in prose.
