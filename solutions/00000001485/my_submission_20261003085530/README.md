# Disproof of conjecture `00000001485`

**Verdict: FALSE — the Arnold cat map A = [[2,1],[1,1]] is a hyperbolic
toral automorphism; suspending it preserves the periodic-orbit counts,
and its zeta function is the rational function
ζ(z) = (1−z)²/(1−3z+z²) with poles at (3±√5)/2 ≈ {0.382, 2.618}.
The radius of convergence is (3−√5)/2 ≈ 0.382 < 1 (NOT 1), and the
singular set {0.382, 2.618} contains no root of unity: both clauses of
the conjecture fail for this hyperbolic suspension.**

## The conjecture (verbatim from `conjectures/00000001485.md`)

> Definition: The zeta function of a suspension of an invertible map
> is the generating function ζ(z) = ∏(1−z^p)^{-1} of its periodic
> counts.  Conjecture: For every hyperbolic suspension, ζ has radius
> of convergence 1, and its singular set on the unit circle is
> exactly the set of roots of unity (a complete characterization of
> periodic structure); no hyperbolic suspension has radius of
> convergence > 1.

## The refutation

The Arnold cat map A = [[2,1],[1,1]] is hyperbolic: eigenvalues
λ₁ = (3+√5)/2 ≈ 2.618 and λ₂ = (3−√5)/2 ≈ 0.382 (λ₁λ₂ = 1,
λ₁+λ₂ = 3).  A suspension of A has the same periodic-orbit counts as
A itself, so ζ(z) = exp(Σ_k N_k z^k / k) with N_k = #Fix(A^k) =
|det(A^k − I)| = λ₁^k + λ₂^k − 2 = L_{2k} − 2 (even Lucas):

    N₁ = 1, N₂ = 5, N₃ = 16, N₄ = 45, N₅ = 121, N₆ = 320.

The zeta function is therefore the rational function

    ζ(z) = (1−z)² / ((1−λ₁z)(1−λ₂z)) = (1−z)² / (1−3z+z²),

with poles at z = 1/λ₁ = (3−√5)/2 ≈ 0.382 and z = 1/λ₂ ≈ 2.618.
The radius of convergence is the distance to the nearest pole:
**r = (3−√5)/2 ≈ 0.382 < 1** — the "radius = 1" clause fails.  The
singular set {0.382, 2.618} contains no root of unity (0.382 is a
real number strictly inside the unit circle; 2.618 strictly outside):
the "singular set = roots of unity" clause also fails.  (Note also
that the radius is not > 1, so the last clause happens to hold for
this example — but the conjecture as a whole requires BOTH radius = 1
AND singular set = roots of unity for EVERY hyperbolic suspension.)

## Verification

* `reproduce.py` — matrix powers of A giving N_k = |det(A^k − I)| for
  k ≤ 6; the pole positions 1/λ₁, 1/λ₂; the zeta series
  exp(Σ N_k z^k/k) at z = 0.3 vs the closed form (matching to 10
  digits); the radius comparison.
* Lean 4 (core, v4.33.1), `lean4/` — the scaled even-Lucas recurrence
  w(0) = 4, w(1) = 6, w(n+2) = 3w(n+1) − w(n) with the periodic counts
  N_k = w(k)/2 − 2 = 1, 5, 16, 45 (decided on ground values); the
  ring ℤ[√5] (pairs (a,b) = a+b·√5 with multiplication
  (ac+5bd, ad+bc)) with the root certificate (3,−1)² = (14,−6),
  (14,−6) + (4,0) = (18,−6) (z² − 3z + 1 = 0 for z = (3,−1)/2), the
  conjugate root, and the pole position 0 < (3−√5)/2 < 1 (positivity
  in ℤ[√5] by the sign form).  All 7 audited theorems report `does
  not depend on any axioms`.

## Boundary

The kernel certifies the periodic counts, the closed-form root
certificate in ℤ[√5], and the pole position.  The
suspension-invariance of the zeta function and the identification of
the radius of convergence with the nearest-pole distance are
classical, cited in prose and re-verified numerically by the script.
Both clauses of the conjecture fail for this hyperbolic suspension.
