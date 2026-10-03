# Disproof of conjecture `00000002118`

**Verdict: FALSE — the exact Quicksort moment recurrences give
kappa₃(50) = 22084.8 ≈ 442·50, with kappa₃(n)/n GROWING (0.35 → 6.40 →
48.2 → 441.7 for n = 5 → 50): the third cumulant is Θ(n³), not the
claimed linear form 2n − 6 log n + C.  The claimed linear main
coefficient 2 is refuted at n = 50 (442 ≠ 2, and 442 > 100 =
2·50).**

## The conjecture (verbatim from `conjectures/00000002118.md`)

> Definition: The Quicksort cost Q_n is the number of comparisons.
> Conjecture: The third cumulant is κ₃(n) = 2n − 6 log n + C (with
> explicit constant C); the linear main coefficient of κ₃ is 2.

## The refutation

Quicksort splits at a uniform position J ∈ {0,…,n−1}:
C_n = (n−1) + C_J + C_{n−1−J}, with independent subproblems.  The
moment recurrences (E[C³] via E[C_J³] + E[C_{n−1−J}³] +
3E[C_J]E[C_{n−1−J}²] + 3E[C_J²]E[C_{n−1−J}³], etc.) solved exactly
over Fractions give

    kappa₃(50) = 22084.80 ≈ 442·50,

with the ratio kappa₃(n)/n GROWING: 0.35 (n=5), 6.40 (n=10),
48.2 (n=20), 133.9 (n=30), 264.9 (n=40), 441.7 (n=50).  The true third
cumulant is Θ(n³), so the claimed linear form 2n − 6 log n + C (main
coefficient 2) is wrong by two orders of magnitude at n = 50, and the
gap grows with n.

## Verification

* `reproduce.py` — the exact Fraction moment recurrences up to n = 54,
  the κ₃ values and ratios at the table above, the growth check
  (ratios strictly increasing), and the instance anchor κ₃(50) ≈
  22085 ∈ (22000, 22100) with ratio 441.7 ± 0.2.
* Lean 4 (core, v4.33.1), `lean4/` — the claimed main-coefficient
  anchor 2·50 = 100, the measured rounded ratio 442 ≠ 2, the
  comparison 442 > 100 (main-order refutation), and 442 > 3·50 (even
  coefficient 3 fails).  All 4 audited theorems report `does not
  depend on any axioms`.

## Boundary

The kernel certifies the claimed-coefficient anchor and the rounded
measured-ratio contrast (442 ≠ 2, 442 > 100); the exact κ₃ values are
carried by the script's Fraction-exact moment recurrences.  The
conjecture's linear-main-coefficient claim is refuted at n = 50.
