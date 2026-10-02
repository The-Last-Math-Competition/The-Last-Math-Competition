# Disproof of conjecture `00000001857`

**Verdict: FALSE (internally inconsistent) — the conjecture's own closed
form evaluates to ≈ 0.2168, strictly below 1/2, while the conjecture
claims the numerical limit is 1.175… > 1: the closed form and the
claimed value are mutually exclusive.**

## The conjecture (verbatim from `conjectures/00000001857.md`)

> Definition: The spanning-tree count τ(G) of a random d = 3 regular
> graph. Conjecture: τ(G) is asymptotically c₃^n (an exponential
> constant) with c₃ = ((√3−1)/2)²·exp(∫log(3−2cos θ)dθ/4π) (a
> McKay-type formula); the numerical limit is 1.175…, and the closed
> form is computable.

## The refutation

1. **The integral is classical**: for a > b > 0,
   (1/2π)∫₀^{2π} log(a − b cos t)dt = log((a + √(a²−b²))/2). With
   a = 3, b = 2: (1/2π)∫ log(3−2cos) = log((3+√5)/2), so the
   conjecture's exp(∫…dθ/4π) = exp(½·log((3+√5)/2)) = √((3+√5)/2) ≈
   1.618 < 2 (kernel anchor: √5 < 5, i.e. 25 > 20).
2. **The prefactor** ((√3−1)/2)² = (2−√3)/2 < 1/4 (kernel anchor:
   √3 > 3/2, i.e. 9 > 4).
3. **Hence the closed form is below (1/4)·2 = 1/2 < 1**, while the
   conjecture's own claimed numerical limit is 1.175… > 1: writing
   c₂ = 2000·(closed form), the bounds give c₂ < 1000 but the claim
   gives c₂ = 2350 — 2350 < 1000 is absurd (kernel-certified).

The closed form evaluates to ≈ 0.2168 (numerically confirmed in
`reproduce.py`, including the integral by quadrature). For reference,
the true McKay-type constant for random 3-regular graphs is ≈ 1.216 —
the claimed 1.175 is off versus the literature as well; the internal
contradiction above suffices for the refutation.

## Verification

* `reproduce.py` — numerical quadrature of ∫log(3−2cos θ)dθ/(4π)
  (2·10⁶-point rule, matching the classical identity log((3+√5)/2)/2
  to 12 digits), the closed-form evaluation ≈ 0.21678, the comparison
  against 1.175 and against the literature value ≈ 1.216.
* Lean 4 (core, v4.33.1) — `lean4/`: the rational anchors (9 > 4,
  25 > 20, 1000 < 1175, 1 < 2) and the internal-inconsistency
  theorem. All 6 audited theorems report `does not depend on any
  axioms`. The integral identity, exp–log rules, and the square
  expansion ((√3−1)/2)² = (2−√3)/2 are classical and cited.

## Boundary

Only the displayed closed form + numerical-limit pair is refuted (they
are mutually inconsistent); the true asymptotic constant of τ(G) for
random 3-regular graphs is not determined here.
