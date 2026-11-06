# Solution Review — Conjecture 00000001546 (PR 1147)

**Submission:** lizaixi01 — `lizaixi01_submission_20261023060816`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000001546; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.33.0` and Mathlib revision `db584cd6d46c92f209a44c0f1c829460d327499d`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** Literal: the maximum number of bisector lines is n·e^{O(√log n)}, and no polynomial upper bound exists. The submission reads 'polynomial upper bound' as O(n^d) for some fixed natural exponent d, and treats the O inside the exponential both as an eventual h=O(√log n) and as the envelope n·e^{C√log n}.

**Decisive results.** For C∈ℝ and x≥1, nonnegativity of (√log x−C/2)^2 gives C√log x≤log x+C^2/4, hence x·e^{C√log x}≤e^{C^2/4}·x^2. Thus the asserted upper growth n·e^{O(√log n)} is actually O(n^2): a polynomial upper bound with d=2. Lean proves this directly for the envelope, for h=O(√log n) inside the exponential, and for natural-valued counts with a one-sided bound. It then proves for every real-valued f (and every natural-valued count) that the upper-growth clause and NoPolynomialUpperBound are incompatible. This negates the source's necessary conjunction; no actual geometric count is assigned.

**Report correspondence.** The report matches Lean: real_exponent_bound, real_envelope_bound, envelope_bigO, exponent_bigO_implies_quadratic, source_clauses_incompatible, envelope_clauses_incompatible and natural_count_clauses_incompatible. The report explicitly says it does not assign a geometric counting value, does not resolve the geometry, and does not deny the compatible lower bound. No stronger prose claim.

## Disposition

APPROVED — merged as PR 1147. The submission gives a complete, formalised disproof of conjecture 00000001546.
