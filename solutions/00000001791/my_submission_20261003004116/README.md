# Disproof of conjecture `00000001791`

**Verdict: FALSE — at d = 3 the polynomial x² + y³ has lct = 5/6,
which lies in neither layer of the claimed set {1/m : m = 1,2,3} ∪
{n + 1/m}.**

## The conjecture (verbatim from `conjectures/00000001791.md`)

> Definition: The jump set of lct is the set of jump positions of lct
> values of multivariate polynomials. Conjecture: The union of lct
> values over polynomial families of degree ≤ d is a discrete layer
> {1/m : m = 1,…,d} ∪ {n+1/m}; the explicit layers of the jump set are
> given by the Sano–Némethi Newton upper bound.

## The counterexample (d = 3)

f(x, y) = x² + y³ has total degree 3. Its log canonical threshold at
the origin is the classical value for the weighted-homogeneous
isolated singularity (weights wt(x) = 3, wt(y) = 2; Saito's theorem —
lct = (sum of weights)/(common weight)):

    lct₀(f) = 3/6 + 2/6 = 5/6.

Membership check against the claimed layer set, in the
positive-denominator cross-multiplied form (5/6 ≠ n + 1/m ⟺ 6nm + 6 ≠
5m):

* **Layer {1/m : m = 1,2,3}:** 5m ≠ 6 for m = 1, 2, 3 (5, 10, 15 ≠ 6) —
  kernel-certified.
* **Layer {n + 1/m}:** for every n ≥ 1 and m = 1, 2, 3,
  **5m < 6nm + 6** — kernel-certified as a fully general statement
  (5m ≤ 5m+6 ≤ 6m+6 ≤ 6nm+6, the last by m ≤ nm); so 5/6 < n + 1/m and
  equality never holds. For n = 0 this reduces to the previous bullet.

So 5/6 — an lct value realized within degree 3 — is outside the claimed
discrete layer, and the "explicit layers" characterization fails.

## Verification

* `reproduce.py` — computes lct values of the x^a + y^b family from the
  closed weighted-homogeneous formula 1/a + 1/b (a,b = 2..9), and
  cross-checks that 5/6 (a,b = 2,3) is absent from {1/m : m ≤ 3} ∪
  {n + 1/m} by exact Fraction arithmetic, i.e. the same
  cross-multiplication the Lean kernel certifies.
* Lean 4 (core, v4.33.1) — `lean4/`: both layer exclusions are
  kernel-certified theorems, uniform in n; all 4 audited theorems
  report `does not depend on any axioms`. The value lct(x²+y³) = 1/2 +
  1/3 = 5/6 is the classical weighted-homogeneous threshold (Saito),
  cited.

## Boundary

Only d = 3 is needed to refute the displayed characterization; behavior
at larger d and the Sano–Némethi upper-bound clause are not addressed.
