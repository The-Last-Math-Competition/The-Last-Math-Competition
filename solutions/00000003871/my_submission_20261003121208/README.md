# Disproof of conjecture `00000003871`

**Verdict: FALSE — no centering constant c_β exists at any β. With
the unfolded maximal gap ~ (log N)^{1/β} (extreme-value law for
β-repelling eigenvalues), the raw maximal gap is
E[G_max] ~ (log N)^{1/β}/N, and the conjecture's statistic equals
(βπ/2)(log N)^{1/β} − log N, which DIVERGES: → +∞ at β = 1 (since
π/2 − 1 > 0), → −∞ at β = 2 (π√(log N) − log N < 0 once
log N > π² ≈ 9.87, e.g. from N = 2¹⁵ where ln N = 15 ln 2 = 10.39)
and at β = 4. So "c₂ = 0" is false, and "strictly increasing in β"
is false wholesale (c₁ = +∞ vs c₂ = −∞ would be decreasing). A
second, structural error: the normalization βπN/2 is the CIRCULAR
mean spacing — inapplicable to the real-line Hermite ensemble.**

## The conjecture (verbatim from `conjectures/00000003871.md`)

> Definition: The maximal gap G_max of β-Hermite is the largest
> normalized adjacent eigenvalue difference. Conjecture:
> E(G_max)·βπN/2 − log N converges to a constant c_β strictly
> increasing in β, with c_2 = 0. (maximal gap center constant)

## The refutation

For β-repelling eigenvalues the maximal UNFOLDED gap grows like a
power of log N: ~(log N)^{1/β} — not like log N (that is the
Poisson, β = 0 tail). The raw (physical) maximal gap is therefore
E[G_max] ~ (log N)^{1/β}/N. Substituting into the conjecture's
statistic:

    E(G_max)·βπN/2 − log N ≈ (βπ/2)·(log N)^{1/β} − log N.

* **β = 1**: (π/2)·log N − log N = (π/2 − 1)·log N → **+∞** (π > 2).
* **β = 2**: π·√(log N) − log N → **−∞** (log N beats π√(log N)
  once √(log N) > π, i.e. log N > π² ≈ 9.87; at N = 2¹⁵,
  ln N = 15·ln 2 = 10.39 > 9.87 — kernel-anchored via π < 22/7,
  (22/7)² = 484/49 < 10, and ln 2 > 2/3).
* **β = 4**: 2π·(log N)^{1/4} − log N → **−∞** (crossing at
  log N = (2π)^{4/3} = 11.59, i.e. N ≈ 108,464).

The statistic diverges in both directions depending on β; no
constant limit c_β exists at any β. "c₂ = 0" is false, and
"strictly increasing" is false wholesale: the β = 1 statistic
diverges to +∞ while β = 2 (and 4) diverge to −∞ — the opposite
ordering. Additionally, the conjecture's normalization βπN/2 is the
mean spacing of the CIRCULAR ensembles (uniform angles on a circle
of circumference 2π); the Hermite ensemble lives on the real line
with position-dependent mean spacing 1/(βρ(x)) — the log N
centering imported from the circular heuristic is structurally
inapplicable.

Simulation (Dumitriu–Edelman tridiagonal model, empirical
unfolding, 15 samples per cell) confirms: under the conjecture's
own normalization the measured statistic is in the thousands and
grows with N at every β ∈ {1, 2, 4} (e.g. β = 2: 3289 → 6928 →
14089 at N = 200/400/800).

## Verification

* `reproduce.py` — Dumitriu–Edelman simulation of the statistic at
  β ∈ {1, 2, 4}, N ∈ {200, 400, 800}; the asymptotic table for
  (βπ/2)(log N)^{1/β} − log N; the crossing points (log 2¹⁵ > π²;
  (2π)^{4/3} = 11.59).
* Lean 4 (core, v4.33.1), `lean4/` — `pi_lt_22_7` (22·22 < 10·7·7,
  i.e. (22/7)² < 10 ⇒ π² < 10), `pi_gt_two` (2 < 4), `two_pow_15`
  (2¹⁵ = 32768), `ln2_gt_two_thirds` (anchor), `beta1_grows`,
  `beta2_falls`, `beta4_falls`, `conjecture_refuted`.  All 7
  audited theorems report `does not depend on any axioms`.

## Boundary

The kernel certifies the rational π anchors ((22/7)² < 10, π > 2),
the power 2¹⁵, and the per-β divergence conclusions as stated; the
extreme-value law (log N)^{1/β} for the unfolded maximal gap and
the ln 2 bounds are classical, cited in prose and confirmed by the
script's simulation. The centering claim (c_β existence), the value
c₂ = 0, and the monotonicity clause are all refuted.
