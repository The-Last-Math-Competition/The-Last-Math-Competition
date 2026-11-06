# Solution Review — Conjecture 00000006640 (PR 1110)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261022114433`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000006640; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.19.0` and Mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** Definition: Static solution sets and the time-symmetric spectrum are two layers. Conjecture: There exist two systems with the same static solution set but different time spectra, and the separation is realized by an explicit master-equation pair with the same statics but different dynamics. (same static-different master-equation separation) 定义：静态解集与时间对称谱指两层。猜想：存在两系统的静态解集相同而时间谱不同,分离由同静态异动力学的显式主方程对实现。（静态同-时间谱异主方程分离）

**Decisive results.** Lean constructs two symmetric two-state master-equation generators with the same full static kernel and the same stationary vector but different spectra and propagators, and verifies the master-equation and semigroup laws. The theorem `conjecture_6640_true : SeparationClaim` establishes the filed explicit separation.

**Report correspondence.** The report, README and Lean sources were read. The report states the same construction and the same decisive conclusion; the Lean declaration matches the report's main theorem. The LaTeX source recompiled cleanly, and the build log reports only propext, Classical.choice and Quot.sound.

## Disposition

APPROVED — merged as PR 1110. The submission gives a complete, formalised proof of conjecture 00000006640.
