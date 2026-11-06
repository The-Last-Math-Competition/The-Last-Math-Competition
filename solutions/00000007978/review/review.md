# Solution Review — Conjecture 00000007978 (PR 1173)

**Submission:** Galaxy-0 — `Galaxy-0_submission_20261023200300`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000007978; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.31.0`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** The filed clause says C_PIR(t)=1/(1+t^{-1}) for t-server PIR capacity, with no number-of-messages parameter. The submission reads the standard replicated PIR model with K independent messages and shows the formula fails already at t=1, K=3: download-all achieves rate 1/3, and a zero-error converse forces D≥B³.

**Decisive results.** For one server and three messages, privacy forces a common query; correctness for all three indices then makes the answer map injective on all B³ databases, so D≥B³ and rate ≤1/3, attained by downloading all messages. The filed formula gives 1/2 at t=1, a contradiction. The Lean constructs the finite scheme model, proves the privacy/correctness injection, the exact alphabet bound, and the download-all scheme; it also proves a uniform rate gap below 1/2 for small error.

**Report correspondence.** Report and Lean agree on the finite model, the exact t=1,K=3 capacity calculation, and the fact that the general entropy/Fano extension is prose. The report explicitly says a K=2 restriction would make the formula true and that this counterexample targets the unrestricted posted statement.

## Disposition

APPROVED — merged as PR 1173. The submission gives a complete, formalised disproof of conjecture 00000007978.
