# Disproof of conjecture `00000003152`

**Verdict: FALSE — the claimed lower bound μ(A·B) ≥ exp(μ(A) + μ(B))
exceeds the trivial probability upper bound μ(A·B) ≤ 1 whenever
μ(A) + μ(B) > 0: the inequality is unsatisfiable.**

## The conjecture (verbatim from `conjectures/00000003152.md`)

> Definition: Subset product measures on Lie groups: the Brunn–Minkowski
> type. Conjecture: The BM inequality for groups: the lower bound of the
> Haar measure of product sets is exponential in the sum of measures,
> with equality exactly on cosets of subgroups.

## The refutation

μ is a normalized Haar measure — a probability measure — so for ALL
subsets, **μ(A·B) ≤ 1** (classical: the whole group has measure 1). The
claimed lower bound is exp(μ(A) + μ(B)), and by the classical convexity
inequality exp(t) ≥ 1 + t:

    exp(μ(A) + μ(B)) > 1   whenever μ(A) + μ(B) > 0.

So for ANY pair of sets with μ(A) + μ(B) > 0 — e.g. μ(A) = μ(B) = 1/10,
whose claimed bound is exp(1/5) > 1 + 1/5 = 6/5 — the claimed lower
bound exceeds 1 while μ(A·B) ≤ 1: the claimed inequality cannot hold.
The claimed "BM inequality for groups" is not a weakening of
Brunn–Minkowski; it is an impossible statement. (The genuine
multiplicative BM inequality for groups, e.g. μ(A·B) ≥ √(μ(A)μ(B)) /
μ(AB·A)... or the Petridis-type bounds, has a completely different
shape.)

## Verification

* `reproduce.py` — exact-fraction anchor: with μ(A) = μ(B) = 1/10 the
  claimed bound exp(1/5) ≈ 1.2214 > 1 (Taylor-verified to high
  precision), while the probability upper bound is 1; also sweeps all
  measure pairs (i/100, j/100) with i + j > 0 — the claimed bound
  exceeds 1 in every case.
* Lean 4 (core, v4.33.1) — `lean4/`: the general statement (for
  numerator sum s > 0 over any denominator D: D + s > D, so the bound
  scale exceeds 1) and the 1/10 + 1/10 anchor. All 3 audited theorems
  report `does not depend on any axioms`. The probability fact
  μ(A·B) ≤ 1 and exp(t) ≥ 1 + t are classical and cited.

## Boundary

Only the displayed exponential lower bound is refuted; the equality
clause (cosets) and genuine multiplicative BM-type inequalities are not
addressed.
