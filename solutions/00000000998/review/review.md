# Solution Review — Conjecture 00000000998 (PR 1071)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261022085427`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000000998; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.19.0` and Mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** `verify.py` exited 0.

## Semantic audit

**Conjecture as filed.** Definition: The completely bounded norm (cb). Conjecture: The supremum of the ratio of the cb norm to the operator norm over the observable algebra of three qubits equals √2 (the cb ratio). 定义：完全有界范数(cb)。猜想：三量子比特的可观测量代数的 cb 范数与算子范数比值的上确界 = √2(cb 比)。

**Decisive results.** On the actual three-qubit observable algebra M8(C), the complex-linear transpose map has ordinary induced norm one and a genuinely finite completely bounded norm between eight and 64. An explicit 64-by-64 swap matrix has Euclidean operator norm one, while its blockwise transpose has an actual nonzero Euclidean eigenvector of eigenvalue eight. Thus the cb/ordinary ratio is at least eight, exceeding sqrt(2). The decisive Lean declaration is `not_claimed_supremum`, whose statement is: ¬IsLUB cbRatios (Real.sqrt 2) := by. Read against the filed statement, this establishes the negation of the printed clause identified in the README.

**Report correspondence.** The report, README and Lean sources were read. The report states the same construction and the same decisive conclusion; the Lean declaration matches the report's main theorem. The LaTeX source recompiled cleanly, and the build log reports only propext, Classical.choice and Quot.sound.

## Disposition

APPROVED — merged as PR 1071. The submission gives a complete, formalised disproof of conjecture 00000000998.
