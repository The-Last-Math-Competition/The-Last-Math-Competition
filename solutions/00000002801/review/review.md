# Solution Review — Conjecture 00000002801 (PR 1078)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261022101351`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000002801; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.19.0` and Mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** The filed statement says that for irreducible chains the LDP rate function I has a unique zero and that the Hessian of I at that zero is a constant multiple of the Fisher information, the constant being the reciprocal of the spectral gap. The submission reads 'irreducible' literally (no aperiodicity or positivity hypothesis) and uses the deterministic alternating two-state chain P=[[0,1],[1,0]].

**Decisive results.** The Lean development constructs the actual two-state PMF transition kernel, the full path law, the empirical occupation vector, and the actual pushforward empirical law. It proves P is irreducible in the literal positive-step reachability sense and that the empirical law obeys the full open-set/closed-set LDP with rate I(π)=0 and I(x)=∞ for x≠π; it proves the zero is unique and the rate is good. Because I is infinite on every other point of the interior simplex, no real-valued function agrees with I on any neighbourhood of π, so no ordinary real Hessian exists at the zero. This directly falsifies the filed Hessian assertion for a chain satisfying the literal irreducibility hypothesis. The unique-zero clause is not contradicted; the counterexample targets the second conjunct.

**Report correspondence.** The report and Lean agree: the report explicitly states the chain is periodic, that the rate is zero at π and infinite elsewhere, that the zero is unique, and that no ordinary real Hessian exists. The report does not claim a spectral-gap or Fisher normalization. No stronger prose claim was found.

## Disposition

APPROVED — merged as PR 1078. The submission gives a complete, formalised disproof of conjecture 00000002801.
