# Solution Review — Conjecture 00000005688 (PR 1197)

**Submission:** lizaixi01 — `lizaixi01_submission_20261024230811`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000005688; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.33.0` and Mathlib revision `db584cd6d46c92f209a44c0f1c829460d327499d`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** Literal: every multifusion category (semisimple with non-simple unit) has unit length 2. The submission reads multifusion as a finite semisimple complex-linear rigid monoidal category with non-simple unit, following EGNO 4.1.1, and takes Fun(Discrete(Fin 3), Vec).

**Decisive results.** The category is a genuine finite semisimple complex-linear rigid monoidal category; its unit is (C,C,C), a biproduct of three pairwise nonisomorphic simples. The theorem proves the unit has a composition series of length 3 and no complete series of length 2. Thus the universal length-2 clause fails. The category is decomposable, which the printed definition and EGNO 4.1.1 allow.

**Report correspondence.** The report theorem matches the Lean `printed_unit_length_two_false`; the report explicitly notes the category is decomposable and that indecomposability is a separate EGNO assumption. No stronger claim about the dimension table or global-dimension clause.

## Disposition

APPROVED — merged as PR 1197. The submission gives a complete, formalised disproof of conjecture 00000005688.
