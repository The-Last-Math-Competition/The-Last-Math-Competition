# Solution Review — Conjecture 00000002571 (PR 1124)

**Submission:** lizaixi01 — `lizaixi01_submission_20261022234908`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000002571; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.33.0` and Mathlib revision `db584cd6d46c92f209a44c0f1c829460d327499d`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** The filed statement claims the explicit inequality D(f) ≤ 16(log rank M_f)^2 for all f, and that exponent 2 is minimal. The submission reads the inequality literally with no rank floor or additive constant and takes rank-one matrices.

**Decisive results.** For XOR with the sign matrix and AND with the 0/1 matrix, Lean proves rank=1 and D=1. Hence D=1 > 16·(log₂1)²=0, so the explicitly quantified inequality D(f)≤16 log²rank fails. The filed statement is a conjunction whose first conjunct is this inequality; refuting it refutes the filed statement. The report honestly notes that the separate exponent-minimality clause is not addressed.

**Report correspondence.** The report and Lean agree; the report explicitly says it does not refute the usual asymptotic log-rank conjecture or a version with a low-rank regularization, and does not address the optimal-exponent assertion.

## Disposition

APPROVED — merged as PR 1124. The submission gives a complete, formalised disproof of conjecture 00000002571.
