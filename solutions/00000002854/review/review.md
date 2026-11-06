# Solution Review — Conjecture 00000002854 (PR 1086)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261022104017`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000002854; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.19.0` and Mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** Definition: Structural equation models (SEM): the algebraic side of causal inference. Conjecture: The algebraic criterion of SEM identifiability: global identifiability holds if and only if the rank deficit of the Jacobian at the generic point is zero, and the deficit is explicitly compensated by additional moment conditions on instrumental variables. (SEM algebraic identifiability criterion) 定义：结构方程模型（SEM）：因果推断的代数侧。猜想：SEM 的可辨识性的代数判据：全局可辨识当且仅当 Jacobi 行列式在泛型点的秩亏损为零且亏损的补偿由工具变量的额外矩条件显式填补。（SEM 代数可辨识判据）

**Decisive results.** The genuine single-factor SEM Y = lambda H + E, with independent standard Gaussian latent factor and error and both variances fixed at one, has observed covariance lambda^2 + 1. Its Jacobian is 2 lambda and has full rank outside the proper algebraic set {0}, but every nonzero lambda is observationally indistinguishable from -lambda. Equal complete observed Gaussian laws are also formally proved. The decisive Lean declaration is `disprove_rank_criterion`, whose statement is: ¬ RankCriterion := by. Read against the filed statement, this establishes the negation of the printed clause identified in the README.

**Report correspondence.** The report, README and Lean sources were read. The report states the same construction and the same decisive conclusion; the Lean declaration matches the report's main theorem. The LaTeX source recompiled cleanly, and the build log reports only propext, Classical.choice and Quot.sound.

## Disposition

APPROVED — merged as PR 1086. The submission gives a complete, formalised disproof of conjecture 00000002854.
