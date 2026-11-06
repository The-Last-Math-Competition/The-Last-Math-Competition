# Solution Review — Conjecture 00000000806 (PR 1059)

**Submission:** Jackmeson1 — `Jackmeson1_submission_20261019095655`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000000806; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.33.1` and Mathlib revision `0df444a360eaa60ab8c11dca51a86af692955474`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** The conjecture asserts that sup R is attained by the union of two equal-volume disjoint disks with value 3/4, where R=(lambda2-lambda1)/lambda1 and eigenvalues are counted with multiplicity.

**Decisive results.** Lean defines the Sobolev/test space, Dirichlet energy, Rayleigh quotient and eigenvalues by Courant-Fischer min-max over actual open planar domains. For two disjoint congruent disks the spectrum is the union of the two identical disk spectra with multiplicity, so lambda1=lambda2 and R=0, not 3/4. This directly falsifies the asserted attaining configuration and value.

**Report correspondence.** The report and Lean agree; the proof.tex discusses the distinct-eigenvalue convention but the formal theorem uses the standard multiplicity convention stated in the README.

## Disposition

APPROVED — merged as PR 1059. The submission gives a complete, formalised disproof of conjecture 00000000806.
