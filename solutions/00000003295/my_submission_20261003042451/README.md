# Disproof of conjecture `00000003295`

**Verdict: FALSE — the Dawson asymptotic series (odd series in 1/x) has
term ratio (2n+1)/(2x²) > 1 for all large n at every fixed x ≠ 0: the
terms grow without bound, so the series diverges by the term test. The
convergence domain is NOT all of R.**

## The conjecture (verbatim from `conjectures/00000003295.md`)

> Definition: Dawson's integral: the companion of the error function.
> Conjecture: The asymptotic tail of Dawson: Dawson at infinity is an
> odd series of the reciprocal, with the convergence domain of the
> series the whole real axis.

## The refutation

The Dawson coefficients aₙ = (2n−1)!!/2ⁿ multiply x^{−(2n+1)}; the term
ratio is

    aₙ₊₁/aₙ = ((2n+1)/(2n−1)) · x^{−2} → (2n+1)/(2x²) → ∞,

so for every fixed x ≠ 0 the terms eventually exceed 1 in magnitude and
grow monotonically (at x = 3: from n = 10, kernel-certified as
21·9 > 4, i.e. (2·10+1)/2 · 9 > 1). A series whose terms do not tend to
0 diverges (the term test; classical). The series is correctly an
ASYMPTOTIC expansion — divergent, with zero radius of numerical
convergence — which is precisely what the conjecture mistakes for a
convergent series.

## Verification

* `reproduce.py` — exact term ratios aₙ₊₁/aₙ (Fractions) at x = 3 for
  n = 5..100 (all > 1 from n = 10); partial-sum amplitudes growing;
  the true Dawson function F(3) ≈ 0.886 shown bounded for contrast.
* Lean 4 (core, v4.33.1) — `lean4/`: the exact ratio anchor
  21·9 > 2·2 (i.e. (2·10+1)/2·3² > 1) and the refutation. All 3
  audited theorems report `does not depend on any axioms`. The ratio
  test and the double-factorial recurrence are classical and cited.

## Boundary

Only the "convergence domain = all of R" clause is refuted; the (true)
asymptotic character of the series and Dawson's integral itself are not
addressed.
