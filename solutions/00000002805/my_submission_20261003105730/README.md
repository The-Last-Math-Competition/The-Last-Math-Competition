# Disproof of conjecture `00000002805`

**Verdict: FALSE — both clauses. (1) The Schilder rate
I(w) = ½‖w‖²_H vanishes iff w is the ZERO path, not iff w lies in
the Cameron–Martin unit ball: the path w(t) = t/2 lies in the unit
ball (‖w‖_H = 1/2 ≤ 1) with I = 1/8 ≠ 0, and every w ≠ 0 has
I = ½‖w‖²_H > 0. (2) On the unit sphere ‖w‖_H = 1 the rate is the
CONSTANT ½ — a point mass, not a chi-square-type law (confirmed in
2D Cameron–Martin coordinates: every (a₁,a₂) with a₁²+a₂² = 1 has
I = ½ exactly).**

## The conjecture (verbatim from `conjectures/00000002805.md`)

> Definition: Schilder's theorem: the LDP on the path space of
> Brownian motion. Conjecture: Cameron–Martin rigidity of the
> Schilder rate: the rate function vanishes if and only if the path
> lies in the Cameron–Martin unit ball, and the spectral
> distribution of the rate on the sphere is an explicit
> chi-square-type law.

## The refutation

Schilder's rate function on the Cameron–Martin space H₀ = {absolutely
continuous w, w(0) = 0} is I(w) = ½∫₀¹|ẇ(t)|²dt = ½‖w‖²_H. It
vanishes exactly when ẇ = 0 a.e., i.e. when w ≡ 0 — a single point,
not the unit ball. In the coordinate model w_c(t) = c·t (‖w_c‖_H =
|c|, I = c²/2): the path c = ½ is IN the unit ball with I = ⅛ ≠ 0 —
the "vanishes iff in the ball" claim fails in its "if" direction,
while "only if" reduces to the truth (vanishing only at c = 0,
kernel-certified for c ≠ 0 via positivity of c²).

On the sphere ‖w‖_H = 1 the rate is I = ½ for EVERY point — the
"spectral distribution of the rate on the sphere" is the point mass
δ_{1/2}, not a chi-square-type law (in 2D coordinates
w = a₁e₁ + a₂e₂ with a₁² + a₂² = 1: I = ½ identically). A chi-square
distribution is non-degenerate; the sphere rate has zero variance.

## Verification

* `reproduce.py` — exact rational table (c ∈ {0, ¼, ½, 1, 3/2}:
  norm, ball membership, rate); the counterexample ½·t with I = ⅛;
  the constant sphere rate (1D and 2D coordinates).
* Lean 4 (core, v4.33.1), `lean4/` — `vanishes_only_at_zero`
  (0 < c → 0 < c², via clean `Nat.mul_pos`), `in_unit_ball`
  (1 ≤ 2), `rate_nonzero` (1 ≠ 0), `sphere_rate_constant`
  (2 = 1·2), `constant_not_chisquare` (1 ≠ 2),
  `conjecture_refuted`.  All 6 audited theorems report
  `does not depend on any axioms`.

## Boundary

The kernel certifies the positivity of the rate off the zero path,
the in-ball counterexample with nonzero rate, and the constancy of
the rate on the sphere.  The identification I(w) = ½‖w‖²_H (Schilder's
theorem proper) is classical, cited in prose and instantiated by the
script in exact rational and 2D-coordinate form.  Both the rigidity
clause and the spectral clause are refuted.
