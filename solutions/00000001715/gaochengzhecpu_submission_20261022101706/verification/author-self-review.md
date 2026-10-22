# Conjecture 1715 self-review

Verdict: PASS for the stated decay-component disproof; parent review and fresh publication validation remain pending.

Developed by a delegated AI agent with a self-review; the coordinating agent reviews it separately. No external independent review is claimed.

1. **Source correspondence.** Read both source languages. Both explicitly describe c_k = (1-e(k alpha))^-1 itself as a decaying sequence. Standard e(t) is exp(2 pi i t). No convention change is used. The source's remaining LLT assertions are underspecified and are neither defined nor claimed refuted separately.
2. **Nonzero denominators.** Proved for every irrational real alpha and every positive integer k using the genuine complex-exponential kernel. The Lean reciprocal-at-zero convention is never exploited: denominator_ne_zero proves actual nonvanishing.
3. **Quantifiers and indexing.** coefficient alpha n uses k=n+1 and therefore covers exactly all positive frequencies. The proof is uniform in irrational alpha. The explicit sqrt_two_counterexample includes Mathlib's irrationality proof, preventing any vacuous implication.
4. **Hand proof.** Unit complex numbers have |1-z|<=2; reciprocal modulus is >=1/2. Norm continuity excludes convergence to zero. These are the same objects and argument proved in Lean; no surrogate numerical table or solver assumption appears.
5. **Scope attack.** The products fhat(k)*c_k might decay for smooth f despite nondecay of c_k. The paper explicitly states this limitation. If the organizers intended only those products to decay, this result does not refute that alternative formulation. It addresses the literal explicit coefficient claim in both languages.
6. **Formalization.** DecayAssertion is the source's necessary decay component, not falsely advertised as the full LLT. coefficient_not_tendsto_zero proves failure for every irrational alpha. Main theorem is disprove_decay_assertion : not DecayAssertion.
7. **Proof trust.** No sorry, admit, native_decide, new axiom, or opaque declaration. Strict Lean check 04 passed with warnings as errors; all four audited theorems list only propext, Classical.choice, Quot.sound. Earlier failed checks are retained and must not be mistaken for final evidence.
8. **Publication boundary.** No GitHub writes, staging, release manifests, or shared scripts were touched. Parent will perform a fresh build, PDF compilation, visual QA and adversarial review. This self-review is not a substitute for those checks.

## Actual author checks

- Check 01: direct strict Lean command, exit 1. Two elaboration errors: unknown le_inv0 spelling and wrong order-limit inequality lemma. Original output preserved in 1715-strict-01.log (copied verbatim from tool output after it had completed; it was not redirected at invocation).
- Check 02: strict Lean command, exit 1; reciprocal bound fixed, order-limit lemma still wrong. Redirected log 1715-strict-02.log.
- Check 03: strict Lean command, exit 1; specifying filter did not fix wrong lemma. Redirected log 1715-strict-03.log.
- Check 04: strict Lean command, exit 0; ge_of_tendsto handles the lower bound. Redirected log 1715-strict-04.log. Four axiom lists all clean.
- Project build: lake build, exit 0, Build completed successfully. Redirected log 1715-build.log. No source changes after strict check 04.

## Examined and rejected candidates

- 1212: standard two-row Chomp losing positions are (n+1,n), but source's density ambient space and shifted Zeckendorf phrase are ambiguous; rejected rather than relying on a preferred reading.
- 2783: claimed universal Banach-Mazur bound sqrt(n) is false, but a complete formal lower bound against every invertible linear map would be substantial; not started.
- 2735: stacked-sphere upper-bound extremality is false, but the full simplicial-sphere/polytope link is expensive to formalize; not started.
- Other sampled candidates were not selected because genuinely open, heavily specialized, or insufficiently specified; no theorem is claimed for them.
