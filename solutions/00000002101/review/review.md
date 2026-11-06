# Solution Review — Conjecture 00000002101 (PR 1185)

**Submission:** lizaixi01 — `lizaixi01_submission_20261024103051`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000002101; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.33.0` and Mathlib revision `db584cd6d46c92f209a44c0f1c829460d327499d`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** Literal reading: the parenthetical specifies the Stokes constant's value as φ^{1/2}, where φ is the usual golden ratio (1 + √5)/2, while the main clause says the constant is a unit of Q(√5). The conjunction of the value and field-unit conditions is refuted.

**Decisive results.** The theorem constructs the actual quadratic field Q(ω), ω^2 = 5, its real and complex embeddings, and the golden element g = (1 + ω)/2 with native norm -1. If x^2 = g in the field, then N(x)^2 = N(g) = -1, impossible over Q. Hence no square root of φ lies in Q(√5), and both the positive real value √φ and its negative are excluded. Therefore no scalar can simultaneously have value φ^{1/2} and be a unit of Q(√5); this is a pointwise impossibility and exactly the negation of the printed value/unit conjunction.

**Report correspondence.** The report proves the same norm obstruction and the same real/complex branches, and explicitly states that it does not construct or assign a Stokes constant or refute the standalone field-unit claim. Lean and report agree.

## Disposition

APPROVED — merged as PR 1185. The submission gives a complete, formalised disproof of conjecture 00000002101.
