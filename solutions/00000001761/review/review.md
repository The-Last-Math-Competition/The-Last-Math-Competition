# Solution Review — Conjecture 00000001761 (PR 1179)

**Submission:** lizaixi01 — `lizaixi01_submission_20261024070027`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000001761; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.33.0` and Mathlib revision `db584cd6d46c92f209a44c0f1c829460d327499d`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** Literal reading: James's conjecture asserts semisimplicity of Specht modules whenever the standard block p-weight is at most p/2; the first counterexample, if any, is asserted to have p<2n and n≥16. The submission uses p=3, n=3, λ=(2,1), with the usual p-restricted partition and block weight.

**Decisive results.** The theorem negates both the semisimplicity assertion and the n≥16 lower bound. The Young diagram (2,1) is 3-restricted, has empty 3-core and rim-hook weight 1, so 2·1≤3; the actual Specht module S^{(2,1)} over F_3 is proved to be the augmentation submodule of F_3^3, containing the invariant constant line with no invariant complement, hence it is not semisimple both as a representation and as an F_3[S_3]-module. The example has n=3<16. All objects are actual tableaux, tabloids, polytabloids and core/weight computations.

**Report correspondence.** Report and Lean agree: both prove the weight-one, empty-core, non-semisimple S^{(2,1)} example with n=3<16. The report explicitly distinguishes this from the customary decomposition-matrix James conjecture and from the p≥2n range; no stronger claim is made.

## Disposition

APPROVED — merged as PR 1179. The submission gives a complete, formalised disproof of conjecture 00000001761.
