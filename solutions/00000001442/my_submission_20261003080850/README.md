# Disproof of conjecture `00000001442`

**Verdict: FALSE — at the complete bipartite instance K₁₀,₁₀ the
conjectured formula 2|E|·H_{|V|/2} = 200·H₁₀ = 36905/63 ≈ 585.79,
while the TRUE expected cover time — computed exactly by solving the
240-state coverage Markov chain over Fractions with Gaussian
elimination and re-verified by zero-residual substitution — is
E = 132922481672135822466559649/1926224885145229235070504 ≈ 69.007
(matching the simulation ≈ 68–69).  The gap is ≈ 516.8: the formula
overshoots by a factor of ≈ 8.5 and is neither the exact cover time
nor close to it.**

## The conjecture (verbatim from `conjectures/00000001442.md`)

> Conjecture: The expected cover time of random walks on bipartite
> random graphs is 2|E|·H_{|V|/2} with an explicit correction (the
> exact cover time).

## The refutation

At K₁₀,₁₀: |E| = 100, |V| = 20.  The coverage-state Markov chain has
states (i, j, side) — i = covered left vertices, j = covered right
vertices, side = current side — 240 non-absorbing states plus 2
absorbing ones.  From a left vertex the walk moves to a uniform right
vertex (discovering a new right vertex with probability (10−j)/10);
symmetrically for right.  Solving E = 1 + Σ pr·E[succ] exactly
(Gaussian elimination over Fractions; zero residual on all 240
equations):

    E[cover] = 132922481672135822466559649/1926224885145229235070504
             ≈ 69.007,

while the conjectured formula gives 2·100·H₁₀ = 200·7381/2520 =
36905/63 ≈ 585.79 — overshooting by a factor of ≈ 8.5.  The formula is
refuted as "the exact cover time" and is not even a close
approximation at this instance.

## Verification

* `reproduce.py` — exact Gaussian elimination over Fractions on the
  240-state system, zero-residual re-verification (max residual 0),
  the exact expectation ≈ 69.007, the harmonic number H₁₀ = 7381/2520,
  the formula value 36905/63 ≈ 585.79, and the gap ≈ 516.8.
* Lean 4 (core, v4.33.1), `lean4/` — H₁₀ = 7381/2520 (the ten unit
  fractions over the common denominator 2520, reduced by 8), the
  instance anchors |E| = 100, 2|E| = 200, the formula value
  36905/63 (200·7381 = 1476200 = 36905·40, 2520 = 63·40), and the
  comparisons 36905 > 63·500 (formula > 500) and H₁₀ < 3.  All 5
  audited theorems report `does not depend on any axioms`.

## Boundary

The kernel certifies the formula-side anchors (all arithmetic); the
exact expectation is carried by the script's exact Fraction Gaussian
elimination with zero-residual verification (an exact certificate: the
returned solution satisfies all 240 chain equations identically).
The formula fails as an exact value and as an approximation at this
instance.
