# Disproof of conjecture `00000003856`

**Verdict: FALSE — the CUE maximal gap obeys (N/2π)·G_max ≈
√(log N) (eigenangle repulsion, sine-kernel statistics), NOT the
Poisson √-free law log N; consequently the conjecture's statistic
πN·G_max − log N drifts without bound (41.8 → 45.3 → 46.1 at
N = 400/800/1600, sd ≈ 3.4 constant), far from any O(1) Gumbel
limit — the claimed Gumbel(scale 1/2) puts mass exp(−88) < 10⁻³⁸ <
2⁻¹²⁶ above 44 while the statistic exceeds 44 at about half of all
samples. The scale clause fails independently: the observed spread
≈ 3.4 matches neither Gumbel scale 1/2 (sd 0.641) nor scale 1
(sd 1.282).**

## The conjecture (verbatim from `conjectures/00000003856.md`)

> Definition: CβE denotes the circular β-ensemble; G_max denotes the
> maximal angular gap. Conjecture: πN·G_max − log N converges in
> distribution to Gumbel, with Gumbel scale parameter exactly 1/β.

## The refutation

A Gumbel limit for a maximal gap comes from the Poisson (exponential)
tail: N·P(gap > x·2π/N) ≈ e^{−x} gives the centering x ≈ log N. But
CUE eigenangles REPEL — the gap density near its upper end decays
quadratically, and the maximal gap satisfies the empirical law

    (N / 2π) · G_max ≈ √(log N),   coefficient 1.00 ± 0.01,

measured at N = 400/800/1600: values 2.423/2.635/2.710 against
√(log N) = 2.448/2.585/2.716 (exact Haar CUE sampling, Mezzadri QR
convention). With that law, the conjecture's statistic

    πN·G_max − log N = 2π²·(N G_max/2π) − log N ≈ 2π²√(log N) − log N

grows without bound (means 41.83 ± 3.80, 45.32 ± 3.75, 46.11 ± 3.13),
and the claimed limit Gumbel(scale 1/2) assigns P(X ≥ 44) = e^{−88} <
10⁻³⁸ < 2⁻¹²⁶ to a region the statistic visits at ~half of all
samples — convergence in distribution is impossible. The scale
clause ("exactly 1/β") fails independently: the observed spread
(sd ≈ 3.4, non-vanishing) is far from both Gumbel scale 1/2
(sd = π/(2√6) ≈ 0.641) and scale 1 (sd = π/√6 ≈ 1.282).

## Verification

* `reproduce.py` — exact CUE sampling (20 per N); the √(log N) law
  with coefficient ≈ 1 at three sizes; the divergent statistic; the
  tail-chain e^{−88} < 10⁻³⁸ < 2⁻¹²⁶; the sd comparison.
* Lean 4 (core, v4.33.1), `lean4/` — `tail_bound_core` (880 > 874,
  i.e. 38 ln 10 < 88 via ln 10 < 23/10), `ten38_gt_two126`
  (2¹²⁶ < 10³⁸, exact 39-digit comparison), `tiny_beyond_tiny`,
  `scale_half` (2 = 1·2), `sd_mismatch` (641 ≠ 3400 ≠ 1282 scaled),
  `conjecture_refuted`.  All 6 audited theorems report
  `does not depend on any axioms`.

## Boundary

The kernel certifies the exact integer chain e^{−88} < 10⁻³⁸ < 2⁻¹²⁶
and the scale mismatch anchors; the empirical law (N/2π)G_max ≈
√(log N), the drift of the statistic, and the sd comparison are
exact CUE simulations in the script (Mezzadri convention).  The
Gumbel-limit claim (log N centering) and its exact-scale clause are
both refuted at β = 2; no claim is made about other centerings or
about the fine limit law of the maximal gap.
