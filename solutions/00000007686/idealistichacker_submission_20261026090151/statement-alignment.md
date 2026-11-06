# Statement Alignment: 00000007686

## Frozen Source and Result

Official commit b355e42906e6eaf52bc7e9d005e0ef02d8aa7400; source Git blob
337d3e5e4d97e64cec5d370fa8a3b157ebd77c6f; raw UTF-8 SHA-256
003e63085c8cff598037a2b4e93e4b0e26e6bcaebce73ba7b0df89c32b29d95c.
Both complete source languages are retained verbatim in source.md.

Both define the q-analogue as the coefficient sum of [2n choose n]_q and
assert eventual periodicity in the stated quotient. The negated necessary
clause is exactly existence of a positive additive period T and onset N
such that all n>=N have equal quotient classes at n and n+T.
The family witness is p=3,a=1,k=1. We do not need an interpretation or value
for the asserted explicit minimum period or the final classical comparison.

## Actual Object-to-Theorem Map

| Source object or clause | Actual formal object and theorem | Paper |
|---|---|---|
| Gaussian polynomial | Polynomial Nat, q-Pascal recursion `gaussian`; above-diagonal zero, diagonal one and `gaussian_characterization_unique` | Section2 |
| Coefficient sum | Polynomial finite sum `coefficientSum`; `coefficientSum_eq_eval` | Section2 |
| Source sequence p_q(n) | `coefficientSequence n`, proved equal to actual `Nat.centralBinom n` for all n | Section2 |
| Literal eventual periodicity | `EventuallyPeriodic` has positive T, arbitrary onset N and all n>=N; strict monotonicity and its closed negation | Sections1-2 |
| Natural q=1 quotient | `generatedAtOne` is the least RingCon from X~1; `generatedAtOne_eq_kernel` proves equality with eval-one's kernel | Section3 |
| Constant embedding of the scalar sequence | `constantClass`, `constantClass_eq_iff`, `constantClass_not_eventuallyPeriodic` | Section3 |
| Possible background coefficient modulus | Actual `(ZMod 3)[X]/Ideal.span{X-C1}`, `modularClass_eq_iff` converts equality to natural remainders | Section3 |
| Universal modular obstruction | Three actual Lucas recurrences, all powers of 3, full zero intervals, `centralBinom_mod_three_period_obstruction` for every T>0,N | Section4 |
| Source-defined sequence in modular quotient | `modularClass_not_eventuallyPeriodic`; no hidden modulus or monotonicity premise | Sections3-4 |
| Retaining the polynomial rather than its sum | `reducedGaussian_eval_one`, equality of actual quotient classes and `reducedGaussianClass_not_eventuallyPeriodic` | Section3 |
| Shared necessary-clause negation | `source_k_one_not_periodic` combines natural-presentation and modulo-three quotient negations | Sections1,3-4 |

## Boundaries That Must Not Be Dropped

Nat[X] is a semiring: the printed subtraction is not a ring polynomial in
that semiring. We explicitly use the standard presentation X~1 at k=1 and
prove its generated congruence equals the evaluation kernel. We separately
formalize the genuine modulo-three ring quotient, so the background's
plausible omitted p^a does not rescue the necessary periodicity clause.
The paper discusses ring completion separately; no formal ring-completion
theorem or meaning for a literally undefined Nat ideal is advertised.
Truncated natural subtraction imposing q=0 would be a different repair.

The standard Gaussian recursion is the actual Lean definition and is uniquely
characterized, not an assertion that a named sequence is centralBinom. The
paper independently derives its conventional rational-function product.
That full product identity is not advertised as a separate Lean theorem.

The ordinary partition function p(n) cannot replace the explicit coefficient
sum. Its recursive background structure is not eventual fixed-period
structure. We do not claim nonperiodicity for p=2, every modulus, ordinary
partition numbers or coefficient-by-coefficient periods with varying onsets.

The source starts with natural n and a prime p. No n cutoff, finite maximum,
randomness, convergence assumption, period bound or desired nonperiodicity
is inserted. At p=3,a=1,k=1 all parameter premises are satisfied. The Lean
obstruction quantifies over all natural onsets and positive periods, so
finite experiments are not used to refute an unbounded assertion.

All 33 public theorem types and axiom closures are audited. Actual pinned
dependency caches and the installed compiler remain explicit trust inputs;
full dependency rebuilding and cross-platform results are not claimed.
No organizer metadata or conjecture is changed. A separate AI frozen-package
review is not human endorsement or upstream acceptance.
