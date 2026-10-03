# Disproof of conjecture `00000002196`

**Verdict: FALSE — the claimed second-order Dedekind asymptotics
log M(n) = (log 2 − (log n)⁻¹(loglog n + c)²)·C(n,⌊n/2⌋)·(1+o(1)) with
c = −3/2 has a second-order correction −(log n)⁻¹(loglog n + c)² that
is ≤ 0 for EVERY n and EVERY constant c (a negated square over a
positive logarithm), while the TRUE second-order gap is POSITIVE: at
the certified instance n = 9, M(9) = 286386577668298411128469151667598498812366
(Van Hirtum et al. 2023) satisfies 2¹³⁷ < M(9) < 2¹³⁸, so
floor(log₂ M(9)) = 137 while C(9,4) = 126 — the actual gap is
137 − 126 = 11 > 0 (relative correction +11.7 in log₂ units), a sign
the formula can never produce.**

## The conjecture (verbatim from `conjectures/00000002196.md`)

> The second coefficient of the asymptotic expansion is explicit:
> log M(n) = (log 2 − (log n)⁻¹ (loglog n + c)²) C{n}{floor(n/2)} ·
> (1+o(1)), with c = −3/2.

## The refutation

Read at fixed n (any log base > 1), the conjecture's factor is
(log 2)·(1 − θ) with θ = (log n)⁻¹·(loglog n + c)² ≥ 0: the second-order
correction relative to the leading term (log 2)·C(n,⌊n/2⌋) is a
**negated square divided by a positive logarithm**, hence ≤ 0 for
**every** n and **every** choice of the constant c — including the
claimed c = −3/2, at which it is in fact strictly negative (at n = 9:
log₂ 9 ≈ 3.170 > 3 > 3/2, so the offset loglog 9 − 3/2 ≈ 0.164 > 0 and
the correction is −0.0085 in log₂ units).

The truth points the other way.  The 9th Dedekind number was computed
in 2023 (Van Hirtum–De Causmaecker–Gossow et al., FPGA supercomputing;
independently confirmed by Jäkel):

    M(9) = 286386577668298411128469151667598498812366

It satisfies 2¹³⁷ < M(9) < 2¹³⁸ (138-bit number), so
floor(log₂ M(9)) = 137, while the central binomial coefficient
C(9,4) = 126.  The actual second-order gap is therefore
137 − 126 = **+11 > 0** (log₂ M(9) = 137.717, relative correction
+11.72), whereas the conjecture's formula — with its c = −3/2 —
predicts log₂ M(9) ≈ (1 − (1.664−1.5)²/3.170)·126 ≈ 125.99, i.e. a
*nonpositive* correction of −0.01 and an M(9) smaller by a factor of
2^11.7 ≈ 3400.  No choice of c repairs the sign: the formula's
correction is a negated square and can never be positive, while the
true correction is positive (classical Korshunov asymptotics have a
second-order term of order +C(n,n/2)·loglog n/log n).

## Verification

* `reproduce.py` — exact integer checks (2¹³⁷ < M(9) < 2¹³⁸,
  bit-length 138 ⇒ floor(log₂ M(9)) = 137, C(9,4) = 126, gap 11 > 0);
  the formula's correction evaluated in log₂ and ln readings at
  n = 9, c = −3/2 (both strictly negative); a sign sweep over
  c ∈ {−10, −3/2, 0, 5, 100} confirming the correction is ≤ 0 always.
* Lean 4 (core, v4.33.1), `lean4/` — `M9_bounds` (2¹³⁷ < M(9) < 2¹³⁸,
  ground `decide` on the published 42-digit value), `log2M9`
  (Nat.log2 M(9) = 137), `C94` (C(9,4) = 126 via the Pascal recursion),
  `gap_positive` (126 < 137), `correction_numerator_nonneg`
  (the squared offset is a square, ≥ 0 — the sign mechanism), and the
  strict instance facts `log2_9_gt_3`, `offset_strictly_positive`,
  `denominator_positive`.  All 9 audited theorems report
  `does not depend on any axioms`.

## Boundary

The kernel certifies the instance anchors (M(9)'s binary size, C(9,4),
the positive gap) and the sign mechanism (negated square over positive
denominator, never positive; strictly negative at n = 9 for c = −3/2).
The value M(9) itself is the published 2023 computation (Van Hirtum et
al.), ground into the kernel as a literal and cross-checked by the
script's exact integer arithmetic; the real-log reading of the formula
is carried in prose and by the script.  The refutation of the stated
expansion is complete: both its sign and its constant are wrong.
