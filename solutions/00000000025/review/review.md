# Solution Review — Conjecture 00000000025 (PR 1187)

**Submission:** lizaixi01 — `lizaixi01_submission_20261024115618`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000000025; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.33.0` and Mathlib revision `db584cd6d46c92f209a44c0f1c829460d327499d`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** Literal reading of the printed 'if and only if': for each associated character of the same Galois extension, an exceptional window zero exists iff the character is real; combined with the printed pairwise exclusion for two non-overlapping irreducible characters.

**Decisive results.** The theorem constructs K = Q(ζ8), two distinct primitive real characters χ_A and χ_B of conductor 8, proves their Galois representations irreducible, inequivalent and orthogonal, and proves the window is nonempty for every c > 0. The printed iff would give both real characters a window zero, while the printed exclusion forbids two non-overlapping characters from both having one. The resulting `¬(PrintedRealIff ∧ PrintedExclusion)` is a universal logical incompatibility; the report explicitly says it does not decide actual Siegel-zero existence. The hypotheses are satisfiable (the two characters exist) and the conclusion is the negation of the printed conjunction.

**Report correspondence.** The report states the same reading, the same two characters, the same window predicate, and the same incompatibility; it explicitly disclaims the standard necessity-only theorem and actual Siegel-zero existence. Lean and report agree.

## Disposition

APPROVED — merged as PR 1187. The submission gives a complete, formalised disproof of conjecture 00000000025.
