# Disproof of conjecture `00000001937`

**Verdict: FALSE — for the arithmetic linear group G = ℤ the subgroup
zeta function is the Riemann zeta function ζ(s) = Σ 1/n^s (a_n = 1:
exactly one subgroup nℤ of each index n), whose abscissa of
convergence is 1.  The conjecture's formula gives
dim G/(dim G + 1) = 1/2 at dim G = 1.  1 ≠ 1/2: the abscissa of
convergence is not determined by the algebraic dimension.**

## The conjecture (verbatim from `conjectures/00000001937.md`)

> Definition: The subgroup growth zeta function is the Dirichlet
> series of subgroup-index counts.  Conjecture: The abscissa of
> convergence of the zeta function of an arithmetic linear group is
> dim G/(dim G + 1) (an explicit rational), uniquely determined by the
> algebraic dimension of the group.

## The refutation

For G = ℤ: the subgroups of index n are exactly the nℤ (one per n),
so a_n = 1 identically and

    ζ_ℤ(s) = Σ_{n≥1} 1/n^s = the Riemann zeta function,

with abscissa of convergence 1 (the harmonic series diverges at
s = 1; convergence holds for s > 1 — classical).  The conjecture's
formula at dim G = 1 gives 1/(1+1) = 1/2 ≠ 1: refuted at the very
first arithmetic linear group.  (For comparison, G = ℤ^d with d ≥ 2
has a_n growing polynomially with abscissa d — also not d/(d+1).)

## Verification

* `reproduce.py` — the subgroup-uniqueness fact; harmonic partial
  sums H_20000 > 10 (divergence at s = 1); convergence spot-checks
  for s = 3/2, 2, 3; and the formula-vs-abscissa mismatch 1/2 ≠ 1.
* Lean 4 (core, v4.33.1), `lean4/` — the formula value vs the true
  abscissa at dim G = 1 (1 ≠ 2 scaled by 2), the harmonic anchor
  H_4 = 25/12 > 2 (partial sums already exceed 2 at n = 4), and the
  instance anchors.  All 3 audited theorems report `does not depend
  on any axioms`.

## Boundary

The kernel certifies the arithmetic core (formula value 1/2, the
harmonic anchor, the scaled comparison).  The subgroup classification
nℤ of ℤ and the Riemann-zeta abscissa (divergence at s = 1) are
classical and cited in prose.  The conjecture is refuted at dim G = 1.
