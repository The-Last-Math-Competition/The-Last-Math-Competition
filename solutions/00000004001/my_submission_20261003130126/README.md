# Disproof of conjecture `00000004001`

**Verdict: FALSE — both clauses. At the certified instance d = 1
the n-th Brownian signature level is the scalar S_n = X₁ⁿ/n! (the
ordered/Stratonovich iterated integral), so E‖Sⁿ‖² =
(2n)!/(2ⁿ(n!)³) — at n = 2 this is **3/4**, while the conjecture's
formula gives n!·C(d+n−1, n) = 2!·C(2,2) = **2**: an overestimate
by 8/3 (Monte Carlo confirms 0.755).  The formulas agree only at
n = 0, 1.  The generating-function clause fails independently: the
true coefficients aₙ = (2n)!/(2ⁿ(n!)³) have ratio
aₙ₊₁/aₙ = (2n+1)/(n+1)² → 0 — Bessel-type decay, not C-finite —
so no rational generating function exists.**

## The conjecture (verbatim from `conjectures/00000004001.md`)

> Definition: The path signature S(X) is the tensor series of
> iterated integrals over all multi-indices. Conjecture: The
> expected squared norm of the n-th level of the Brownian signature
> is the explicit combinatorial expression E‖Sⁿ‖² = n!·binom(d+n−1,n),
> and its generating function in n is rational.

## The refutation

For scalar Brownian motion (d = 1) the iterated integrals collapse:
S_n = ∫_{t₁<…<tₙ} dW^{⊗n} = X₁ⁿ/n! (Stratonovich chain rule;
Monte Carlo: E[S₂²] = 0.755 ≈ 3/4 over 400k samples).  Hence

    E‖Sⁿ‖² = E[X₁^{2n}]/(n!)² = (2n)!/(2ⁿ(n!)³),

using the Gaussian moment E[X^{2n}] = (2n)!/(2ⁿn!).  The
conjecture's formula at d = 1 reads n!·C(n, n) = n!.  The values:

| n | true (d=1) | claimed n! |
|---|---|---|
| 1 | 1 | 1 |
| 2 | 3/4 | 2 |
| 3 | 5/12 | 6 |
| 4 | 35/192 | 24 |

— agreement only at n = 0, 1, then an overestimate growing without
bound (factor 8/3 at n = 2, 14.4 at n = 3, 131 at n = 4).  The
generating function of the true coefficients is not rational: the
ratio aₙ₊₁/aₙ = (2n+1)/(n+1)² → 0 (Bessel-type decay), whereas
coefficients of rational generating functions satisfy a linear
recurrence with polynomial-exponential growth (C-finite sequences).

## Verification

* `reproduce.py` — exact table (n = 0..6) of true vs claimed; the
  Monte Carlo confirmation E[S₂²] = 0.755 ≈ 3/4; the ratio law
  aₙ₊₁/aₙ = (2n+1)/(n+1)² verified exactly for n = 1..5.
* Lean 4 (core, v4.33.1), `lean4/` — `claimed_value` (2 = 2),
  `gaussian_moment` (4! = 24 = 4·3·2, 2³ = 8, 24/8 = 3, 3 < 8 —
  the scaled true-value computation), `true_below_claimed`
  (3 < 8), `agree_only_early` (both give 1 at n = 1),
  `ratio_decay` (5 < 9, i.e. (2n+1)/(n+1)² < 1 at n = 2),
  `conjecture_refuted`.  All 6 audited theorems report
  `does not depend on any axioms`.

## Boundary

The kernel certifies the scaled value comparison at (d, n) = (1, 2)
and the ratio-decay anchor; the scalar signature identification
S_n = X₁ⁿ/n!, the Gaussian moments, and the C-finiteness obstruction
are classical, cited in prose and confirmed by the script's exact
table and Monte Carlo.  Both the formula and the rationality clause
are refuted at d = 1.
