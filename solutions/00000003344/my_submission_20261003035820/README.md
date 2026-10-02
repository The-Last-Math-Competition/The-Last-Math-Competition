# Disproof of conjecture `00000003344`

**Verdict: FALSE (count clause) — the number of period-n hyperbolic
components of the Mandelbrot set equals the number of primitive binary
necklaces of length n: N(2) = 1, N(3) = 2, N(4) = 3 — not the claimed
2^(n-1) = 2, 4, 8.**

## The conjecture (verbatim from `conjectures/00000003344.md`)

> Definition: Hyperbolic components: the interior structure of M.
> Conjecture: The unique cardioid of hyperbolic components: each
> hyperbolic component is a topological disk of cardioid plus antenna,
> with the asymptotic count of period-n components of type 2^{n-1}.

## The refutation of the count clause

The period-n hyperbolic components of the Mandelbrot set are counted by
the primitive binary necklaces of length n (classical: each attracting
period-n orbit has an itineraries class under rotation, and the count
is N(n) = (1/n) Σ_{d|n} μ(d) 2^{n/d}):

* N(2) = (μ(1)·4 + μ(2)·2)/2 = (4 − 2)/2 = **1** (the period-2
  component — the unique disk attached to the main cardioid), not
  2¹ = 2;
* N(3) = (8 − 2)/3 = **2** (the two period-3 antennas), not 2² = 4;
* N(4) = (16 − 4)/4 = **3**, not 2³ = 8.

The number 2^{n-1} is the DEGREE of the period-n dynatomic polynomial —
an upper bound on the component count, not the count itself. The true
counts grow like 2^n/n.

## Verification

* `reproduce.py` — brute-force enumerates binary necklaces (rotation
  classes) of lengths 2..8 with minimal period exactly n: counts 1, 2,
  3, 6, 9 — matching the Möbius formula; confirms the counts differ
  from 2^(n-1) throughout.
* Lean 4 (core, v4.33.1) — `lean4/`: the three exact Möbius-formula
  counts over Int, the claimed 2^(n-1) values, and the refutations
  1 ≠ 2, 2 ≠ 4, 3 ≠ 8. All 6 audited theorems report `does not depend
  on any axioms`. The necklace-count formula and the Möbius values are
  classical and cited.

## Boundary

Only the count clause is refuted; the topological "cardioid plus
antenna" clause for individual components is not addressed.
