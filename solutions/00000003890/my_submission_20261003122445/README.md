# Disproof of conjecture `00000003890`

**Verdict: FALSE (first clause) — the F-jumping set of a fixed ideal
is NOT always finite.  For the fixed ideal I = (x) in k[x], the test
ideal is tau(x^c) = (x^{⌈c⌉}) — a unit staircase in the parameter c
— so the exponent (and hence the test ideal) jumps at EVERY positive
integer: the F-jumping set of this one fixed ideal is {1, 2, 3, …},
infinite and unbounded.  (The second clause — density of unions for
sequences of ideals — is consistent with this, but the conjunction
"finite for each fixed ideal" is what fails.)**

## The conjecture (verbatim from `conjectures/00000003890.md`)

> Definition: The F-jumping number set of a fixed ideal is the set
> of all jump parameters of its test ideal. Conjecture: The jumping
> set of a fixed ideal is always finite; but there exist sequences
> of ideals on a fixed ring whose unions of jumping sets are dense
> in (0,1).

## The refutation

In the one-variable polynomial ring k[x] (F_p included), the test
ideal of the parameter x^c has the closed form

    tau(x^c) = (x^{⌈c⌉}),

a classical consequence of the Frobenius-power structure of the
principal ideal (x) (I^{[p^e]} = (x^{p^e})).  The exponent function
⌈c⌉ is a unit staircase: it equals n on the interval (n−1, n] and
increments by exactly 1 at each positive integer.  Concretely,
between the parameters c = m + 1/2 and c′ = m + 3/2 (straddling the
integer m + 1), the exponents are m + 1 and m + 2 — kernel-certified
by the multiplication-only bounds 2m < 2(m+1) ≤ 2(m+1)+1 and
2(m+1)+1 < 2(m+2) ≤ 2(m+2)+1, with the strict separation m+1 < m+2.
Every positive integer is therefore a jumping number of the single
fixed ideal (x): the jumping set is {1, 2, 3, …}, which is infinite
and unbounded — for every N the parameters up to N + 1/2 exhibit
N + 1 distinct test ideals (x), (x²), …, (x^{N+1}) of the one fixed
ideal.  "Always finite" is false.

## Verification

* `reproduce.py` — the staircase structure of ⌈k/2⌉ (unit
  increments, 19 steps over 20 half-integers); the jump enumeration
  1..20; the linear growth of distinct test ideals.
* Lean 4 (core, v4.33.1), `lean4/` — `exponent_left`/`exponent_left'`
  (the ceiling bounds 2m < 2(m+1) < 2(m+1)+1),
  `exponent_right`/`exponent_right'` (2(m+1) < 2(m+2) < 2(m+2)+1),
  `exponents_separated` (m+1 < m+2), `unbounded` (N < N+1),
  `conjecture_refuted`.  All 7 audited theorems report
  `does not depend on any axioms`.

## Boundary

The kernel certifies the multiplication-only ceiling
characterizations and the strict separation of consecutive
exponents; the closed form tau(x^c) = (x^{⌈c⌉}) in k[x] is
classical, cited in prose and mirrored by the script's staircase
enumeration.  The finiteness clause is refuted outright; no claim
is made about the density clause beyond its consistency with the
infinite-jumping-set picture.
