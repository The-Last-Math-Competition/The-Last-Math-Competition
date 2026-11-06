# Solution Review — Conjecture 00000005399 (PR 1215)

**Submission:** LibertychaserUS — `LibertychaserUS_submission_20261027065051`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000005399; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.33.1` and Mathlib revision `0df444a360eaa60ab8c11dca51a86af692955474`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** `check.py` exited 0.

## Semantic audit

**Conjecture as filed.** The filed statement says the expected first return time is the reciprocal of the measure plus a correction term equal to the negative first power of the mixing rate, exactly. The submission reads this as: for every finite irreducible Markov chain, state x, and stationary probability π, E_x[T_x^+] = 1/π(x) + c/gap(P) for some nonzero constant c, with gap the spectral gap 1 − max{|λ| : λ an eigenvalue ≠ 1}. The uniform variant uses one c for all chains.

**Decisive results.** The theorem is the negation of the universal claim. The explicit chain P0 = [[1/2,1/4,1/4],[1/3,1/3,1/3],[1/5,2/5,2/5]] is stochastic and irreducible (all entries positive); π0=(8/23,15/46,15/46) is stationary; h=(0,7/2,4) satisfies the first-step hitting-time equations and gives E_0[T_0^+]=23/8=1/π0(0). The characteristic polynomial is t(t−1)(t−7/30), so the spectral gap is 23/30 ≠ 0. The claimed formula would give 23/8 = 23/8 + c/(23/30), forcing c=0, contradicting c≠0. Thus the counterexample satisfies the literal hypotheses and falsifies the claim. The `ExpReturn` predicate is weaker than uniqueness of hitting times, but the specific witness is the true hitting-time vector and the refutation instantiates the actual expectation r=23/8.

**Report correspondence.** The report's main theorem is exactly `¬ ClaimedFormula`, and the report's Proposition gives the same π0, h, gap, and contradiction. The report transparently notes that if c=0 were allowed the formula would reduce to Kac's lemma (true), so the verdict depends on the nonzero-correction reading. The Lean theorem matches this reading.

## Disposition

APPROVED — merged as PR 1215. The submission gives a complete, formalised disproof of conjecture 00000005399.
