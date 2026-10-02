# Disproof of conjecture `00000001135`

**Verdict: FALSE — for a reduced word s₁…s_k the Bott–Samelson variety
is an iterated ℙ¹-bundle, so P(t) = (1+t²)^k (classical, projective
bundle formula); this P is NOT divisible by (1+t)^{⌊k/2⌋} for any
k ≥ 1 (evaluation at t = −1: 0 = 2^k), the strictly-increasing
clause fails already at k = 2 (P = 1 + 0·t + 2t² + 0t³ + t⁴ has zero
coefficients), and the note's own quotient for k = 6,
(1+t)³(1−t)⁶ = 1 − 3t + 0t² + 8t³ − 6t⁴ − 6t⁵ + 8t⁶ + 0t⁷ − 3t⁸ + t⁹,
has internal zeros. All three clauses fail.**

## The conjecture (verbatim from `conjectures/00000001135.md`)

> Definition: P(t) = Σ b_{2i} t^i is the Betti-number generating
> function of the Bott–Samelson variety BS(s₁,…,s_k). Conjecture: The
> coefficients of P(t) are strictly increasing up to the middle level,
> and P(t) is divisible by (1+t)^{⌊k/2⌋} with monic quotient; the
> quotient's coefficients have no internal zeros when s₁…s_k is a
> reduced word.

## The refutation

For a reduced word the Bott–Samelson variety is an iterated ℙ¹-bundle
(classical): each of the k fibers contributes b₀ = 1, b₂ = 1 by the
projective bundle formula, so

    P(t) = (1 + t²)^k.

1. **Divisibility clause fails (kernel-certified).** If
   (1+t)·Q(t) = (1+t²)², evaluating at t = −1 gives
   0·Q(−1) = (1+1)² = 4, i.e. 0 = 4 — absurd. The kernel certifies
   this for arbitrary polynomial-function Q (core Int arithmetic; the
   factorization is written with the linear factor on the right so
   that only the clean `Int.mul_zero` is needed). The general-k form
   fails identically: P(−1) = 2^k ≠ 0 for all k ≥ 1 (script, with
   synthetic-division remainders 4, 16, 64 at k = 2, 4, 6).
2. **Strict increase fails.** P = (1+t²)² = 1 + 0·t + 2t² + 0t³ + t⁴:
   the degree-1 and degree-3 coefficients vanish.
3. **No-internal-zeros fails.** The note's own quotient for k = 6,
   (1+t)³(1−t)⁶, has coefficients 1, −3, 0, 8, −6, −6, 8, 0, −3, 1 —
   internal zeros at t² and t⁷ (script-verified exactly).

## Verification

* `reproduce.py` — polynomial multiplication over ℤ: P(−1) = 2^k for
  k ≤ 6; synthetic division of (1+t²)^k by (1+t) with nonzero
  remainders 4/16/64 at k = 2/4/6; the exact k = 6 quotient
  coefficient list with internal zeros; the k = 2 coefficient zeros.
* Lean 4 (core, v4.33.1), `lean4/` — the divisibility refutation for
  the k = 2 reduced-word instance (evaluation argument at t = −1,
  using only the clean `Int.mul_zero`), and the arithmetic anchors
  (−1)² = 1, 1 + (−1) = 0, (1+1)² = 4. All 3 audited theorems report
  `does not depend on any axioms`.

## Boundary

The kernel certifies the divisibility failure for the k = 2 reduced
word (evaluation argument) — the general-k failure is the same
computation (P(−1) = 2^k, script for k ≤ 6). The reduced-word
iterated-ℙ¹-bundle structure and the projective bundle formula are
classical, cited in prose. All three clauses of the conjecture fail.
