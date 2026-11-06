# Solution Review — Conjecture 00000000567 (PR 1183)

**Submission:** lizaixi01 — `lizaixi01_submission_20261024094156`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000000567; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.33.0` and Mathlib revision `db584cd6d46c92f209a44c0f1c829460d327499d`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** Literal first clause: for the idempotent completion of the ordinary finite-dimensional representation category of the no-arrow Dynkin quiver A1, count maximal Ext-orthogonal objects (standard additive maximal-rigid / two-sided cluster-tilting conventions) and compare with ∏(e_i+h+1)/(e_i+1).

**Decisive results.** The theorem constructs the actual Karoubi envelope of Rep(A1) over C and proves every nonzero object is maximal rigid. The full isomorphism quotient is infinite (injection from N via standard (n+1)), while the basic quotient has cardinality 1. The A1 Coxeter data give h = 2, e_1 = 1 and predicted product 2. Since neither 1 nor infinity equals 2, the printed formula fails under either counting convention. The hypotheses are satisfiable and the conclusion is the negation of the printed formula for this Dynkin quiver.

**Report correspondence.** The report states the same two counts, the same maximal-rigid and two-sided Ext definitions, and the same product 2. It explicitly disclaims the derived orbit cluster category and the preprojective clause. Lean and report agree.

## Disposition

APPROVED — merged as PR 1183. The submission gives a complete, formalised disproof of conjecture 00000000567.
