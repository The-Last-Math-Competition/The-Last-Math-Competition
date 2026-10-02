# Disproof of conjecture `00000003631`

**Verdict: FALSE — the quadratic system X(x, y) = (x, y) has FIVE
pairwise-distinct invariant lines through the origin (in fact
infinitely many): the maximal count is not four.**

## The conjecture (verbatim from `conjectures/00000003631.md`)

> Definition: Invariant lines of quadratic systems: the algebraic-curve
> side. Conjecture: The count of invariant lines: the maximal number of
> invariant lines of quadratic systems is four, realized as complete
> grids.

## The counterexample: the radial field X = (x, y)

P = x, Q = y: both components of degree 1 ≤ 2, so X is a quadratic
system in the standard degree-at-most-2 sense. Its flow is radial
scaling (x, y) ↦ eᵗ(x, y), which maps every line through the origin to
itself: the origin is a star point.

By the first-order invariance criterion, a line l = 0 with linear form
l = αx + βy is invariant for X = (P, Q) iff X(l) = P·∂ₓl + Q·∂ᵧl is a
scalar multiple of l. For X = (x, y): ∂ₓl = α, ∂ᵧl = β, so
X(l) = x·α + y·β = l — quotient 1, for EVERY line through the origin.

Kernel-certified for FIVE pairwise-distinct lines of this one system:
**y, y − x, y − 2x, y + x, x** — the operator computed structurally
(differentiate; multiply by x and by y; add). Five > 4.

The conjecture's statement carries no general-position, irreducibility,
or nondegeneracy hypothesis that would exclude the star point (the
classical "four invariant lines" results — e.g. the literature on
quadratic vector fields — concern configurations in general position /
with finitely many invariant lines). As stated, the maximum is false.

## Verification

* `reproduce.py` — sympy-verifies the invariance identities
  X(l) = l · 1 for the five lines (and further slopes k = 3, 4, 1/2),
  and confirms pairwise distinctness.
* Lean 4 (core, v4.33.1) — `lean4/`: linear forms as signed coefficient
  pairs; the operator X computed structurally (differentiate, scale,
  add); the five invariance identities, pairwise distinctness, and
  5 > 4. All 7 audited theorems report `does not depend on any axioms`.

## Boundary

Only the "maximal number is four" clause is refuted; the complete-grid
realization clause and genuinely general-position statements are not
addressed.
