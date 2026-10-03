# Disproof of conjecture `00000003883`

**Verdict: FALSE — the claimed value min(a,b) lies outside the
admissible range of the F-pure threshold.  By the Takagi–Watanabe
theorem fpt(I) ≤ lct(I) for every ideal in a regular ring; for
I = (x^a, y^b) the log canonical threshold is lct = 1/a + 1/b < 1,
so fpt ≤ 1/a + 1/b < 1 < 2 ≤ min(a,b) whenever min(a,b) ≥ 2: the
conjecture's main clause ("fpt = min(a,b) when p ∤ min(a,b)")
asserts a value above the ceiling exactly in its own no-correction
case (v_p(min) = 0).  The valuation-only correction clause cannot
repair this: min(a,b) − lct(a,b) = 7/6, 13/10, 301/202 for
(2,3), (2,5), (2,101) — three different values all at valuation 0,
so no correction "depending only on the p-adic valuation" fits.
Certified instance: (a,b) = (2,3): claimed fpt = 2, true
fpt ≤ lct = 1/2 + 1/3 = 5/6 (kernel-anchored as 5 < 2·6 and
5 < 6).**

## The conjecture (verbatim from `conjectures/00000003883.md`)

> Definition: The F-pure threshold fpt(I) is the supremum of
> critical parameters at which no jump of the truncated test ideal
> occurs. Conjecture: For the binomial ideal (x^a, y^b) with
> gcd(a,b)=1, fpt = min(a,b) when p does not divide min(a,b);
> otherwise fpt = min(a,b) minus an explicit correction term
> depending only on the p-adic valuation of min(a,b).

## The refutation

The F-pure threshold is bounded by the log canonical threshold
(Takagi–Watanabe: fpt(I) ≤ lct(I) in regular rings), and for the
monomial ideal (x^a, y^b) the lct is the classical exponent sum
lct = 1/a + 1/b (a simple pole computation; also the Newton
polygon vertex).  Hence

    fpt((x^a, y^b)) ≤ 1/a + 1/b < 1 < 2 ≤ min(a,b)   (min ≥ 2):

the conjecture's main clause asserts fpt = min(a,b) ≥ 2 — outside
the admissible range — in precisely the case it designates as
correction-free (p ∤ min(a,b) means v_p(min) = 0).  The correction
clause is unsalvageable: if the correction depended only on
v_p(min(a,b)), then all p ∤ min cases (valuation 0) would share one
correction constant c, forcing min(a,b) − fpt = c across all pairs
with min ≥ 2; but the true deficit min(a,b) − lct(a,b) = 7/6, 13/10,
301/202 at (2,3), (2,5), (2,101) — three distinct values at the same
valuation 0 (script-verified).  At the certified instance (2,3):
claimed 2 vs true ≤ 5/6 (and in fact fpt = 5/6 for p ≥ 5, equality
with lct by TW's F-pure vs log-canonical comparison at large
characteristic).

## Verification

* `reproduce.py` — lct = 5/6 at (2,3) for p = 5, 7, 11, 13, 101;
  the general violation lct < 1 < min(a,b) for five gcd-1 pairs;
  the valuation-0 correction inconsistency (three distinct deficits).
* Lean 4 (core, v4.33.1), `lean4/` — `claimed_value` (min = 2),
  `fpt_ceiling` (the unit ceiling), `claimed_exceeds_ceiling`
  (2·6 > 6), `true_value_scaled` (5 = 3 + 2, the scaled lct 5/6),
  `true_below_claimed` (5 < 12), `true_below_one` (5 < 6),
  `conjecture_refuted`.  All 7 audited theorems report
  `does not depend on any axioms`.

## Boundary

The kernel certifies the scaled comparisons at the certified
instance (claimed value 2, ceiling 1, true value 5/6, both
strict inequalities).  The theorems used — fpt ≤ lct (Takagi–Watanabe)
and lct(x^a, y^b) = 1/a + 1/b (classical) — are cited in prose;
the valuation-0 inconsistency is computed exactly by the script.
The main clause and the correction clause are both refuted.
