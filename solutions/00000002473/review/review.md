# Solution Review — Conjecture 00000002473 (PR 1126)

**Submission:** lizaixi01 — `lizaixi01_submission_20261023004129`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000002473; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.33.0` and Mathlib revision `db584cd6d46c92f209a44c0f1c829460d327499d`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** The filed statement includes the clause that rank and crank agree outside the exceptional Ramanujan classes n≡4 mod5, 5 mod7, 6 mod11. The submission takes n=2 and the standard rank/crank definitions.

**Decisive results.** The two partitions of 2 are (2) with rank 1, crank 2 and (1,1) with rank -1, crank -2. n=2 is outside all three exceptional classes (two_nonexceptional). no_pointwise_agreement_outside negates pointwise agreement; no_distribution_agreement_outside negates full distribution equality; no_residue_agreement_outside negates agreement of the mod 5,7,11 residue distributions at residue 1. This directly refutes the explicit English agreement clause. The hypotheses are satisfiable (n=2).

**Report correspondence.** The report states the same n=2 example and the three negations; the Lean theorems match. No stronger prose claim.

## Disposition

APPROVED — merged as PR 1126. The submission gives a complete, formalised disproof of conjecture 00000002473.
