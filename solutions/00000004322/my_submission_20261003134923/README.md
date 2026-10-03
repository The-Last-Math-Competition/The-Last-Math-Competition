# Disproof of conjecture `00000004322`

**Verdict: FALSE — both clauses. The Artin–Hasse series
AH_p(x) = exp(∑_k x^{p^k}/p^k) is p-INTEGRAL BY DESIGN
(Dieudonné–Dwork): every coefficient has v_p = 0.  Verified exactly
to n = 300 for p = 2, 3, 5 via the recurrence n·Eₙ =
∑_{p^k ≤ n} E_{n−p^k}: the observed count of coefficients with
v_p ≥ 1 among the first 4 (p = 2) resp. first 6 (p = 3) is ZERO,
not the geometric prediction of 2 each.  The "unique exception at
exponent p−1" fails doubly: a_{p−1} is p-integral like everything
else (no denominator to be exceptional about) and is not even
unique in value — a₁ = a₂ = 1 (p = 2), a₂ = a₃ = 1/2 (p = 3).**

## The conjecture (verbatim from `conjectures/00000004322.md`)

> Definition: The Artin–Hasse power series is the corrected
> exponential series of the p-canonical lift. Conjecture: The
> p-power distribution of the denominators of its coefficients is
> the geometric law with parameter 1/p, and the exceptional
> coefficient occurs uniquely at the exponent p−1. (AH denominator
> geometric law and unique exception)

## The refutation

The defining property of the Artin–Hasse series is precisely its
p-integrality: AH_p(x) ∈ Zₚ[[x]] (this is the content of the
Dieudonné–Dwork lemma, the "corrected exponential" of the
conjecture's own definition).  The recurrence follows from
differentiating the exponent: d/dx ∑_k x^{p^k}/p^k = ∑_k x^{p^k−1}
has p-integral (indeed unit) coefficients, giving

    n·Eₙ = ∑_{p^k ≤ n} E_{n−p^k},  E₀ = 1,

and induction shows every Eₙ is p-integral.  Exact computation to
n = 300 for p = 2, 3, 5 confirms: **zero coefficients with v_p ≥ 1**
— while the claimed geometric law with parameter 1/p predicts 2 of
the first 4 (p = 2) and 2 of the first 6 (p = 3) to have v_p ≥ 1.
The first coefficients are:

    p = 2: 1, 1, 1, 2/3, 2/3, 7/15, …
    p = 3: 1, 1, 1/2, 1/2, 3/8, 7/40, …

The "unique exception at exponent p − 1" is doubly false: a_{p−1}
carries no p-denominator (nothing to be exceptional about), and its
value is not unique — a₁ = a₂ = 1 for p = 2, a₂ = a₃ = 1/2 for
p = 3.

## Verification

* `reproduce.py` — exact rational recurrence to n = 300 (p = 2, 3,
  5): all v_p = 0; the prediction-vs-observed counts; the
  non-uniqueness equalities.
* Lean 4 (core, v4.33.1), `lean4/` — `p2_first`, `p2_E3`
  (3·2/3 = 2), `p2_count_zero` (0 ≠ 2), `p2_no_unique_exception`,
  `p3_half_half`, `p3_count_zero`, `conjecture_refuted`.  All 7
  audited theorems report `does not depend on any axioms`.

## Boundary

The kernel certifies the first coefficients' integrality, the
zero-count refutations, and the non-uniqueness equalities; the
recurrence and the Dieudonné–Dwork p-integrality are classical,
cited in prose and verified by the script's exact computation to
n = 300.  Both the distribution law and the unique-exception claim
are refuted.
