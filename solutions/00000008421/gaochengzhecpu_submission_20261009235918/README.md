# Conjecture 00000008421: a bounded correction to the covering bound

For every t >= 2, C(t+2,t+1,t)=t+1, whereas the counting bound is (t+2)/2. The relative correction is t/(t+2)<1. It therefore cannot satisfy any eventual positive lower bound c log t. This disproves the claimed Theta(log t) correction with strictly interior parameters n>k>t>=2.

## Scope and formal correspondence

The source imposes no additional parameter-growth regime. The counterexample is an infinite family with all parameters increasing; it does not use the k=t or k=n boundaries. The conclusion concerns the conjecture as stated and does not purport to address a different theorem with extra growth restrictions.

The Lean predicate Covers uses actual families of finite subsets, with both block sizes and coverage checked. Every block is proved to be the complement of a unique vertex. A lower bound holds for every possible family, and an explicit covering family attains it. coveringNumber is the infimum of the actual achievable family cardinalities; coveringNumber_exact gives its exact value. countingBound_exact computes the real ratio of the actual binomial coefficients. excess_exact and no_eventual_log_lower_bound disprove the necessary positive logarithmic lower estimate with explicit quantification over the constant and cutoff. The final theorem is conjecture8421_false. The Lean parameter n is the paper's t, and the vertex type has n+2 elements.

## Files and reproduction

- main.tex and main.pdf contain the argument and formal correspondence.
- SOURCE.md preserves the exact bilingual statement; verification/SOURCE_PROVENANCE.json records its commit and SHA-256.
- lean/ is a portable Lean 4.19.0 project pinned to Mathlib commit c44e0c8ee63ca166450922a373c7409c5d26b00b.
- verification/ contains actual build logs, dependency audit, PDF checks, and review records.

Inside lean/, run `lake build` and `lake env lean -DwarningAsError=true Main.lean`. On a new machine, `lake exe cache get` retrieves the official pinned dependency artifacts. From the submission directory, `tectonic main.tex` reproduces the PDF. No auxiliary numerical script is required.

Only official pinned dependency artifacts are reused; the submission's own proof is rebuilt in a fresh directory. There are no proof placeholders, added axioms, or native computation shortcuts. Review consists of author checks plus delegated internal adversarial review, with no external independent review claimed.
