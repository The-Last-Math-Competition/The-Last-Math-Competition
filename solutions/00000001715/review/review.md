# Solution Review — Conjecture 00000001715 (PR 1079)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261022101706`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000001715; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.19.0` and Mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** Definition: The local limit theorem (LLT) for rotations concerns the asymptotic distribution of pointwise counting functions. Conjecture: The LLT has an explicit period-1 correction: the correction term is given by the Fourier coefficients of f through the decaying sequence c_k = (1−e(kα))^{-1}; the correction is nonzero if and only if f has nontrivial low-frequency content. 定义：旋转的局部极限定理(LLT)指逐点计数函数的渐近分布。猜想：LLT 修正为周期 1 的显式函数:修正项由 f 的 Fourier 系数经 c_k = (1−e(kα))^{-1} 的衰减序列给出;修正项非零当且仅当 f 有不平凡的低频成分。

**Decisive results.** For every irrational alpha and every positive frequency k, the actual coefficient c_k = (1 - exp(2 pi i k alpha))^(-1) is well defined and has modulus at least 1/2. It therefore cannot tend to zero; alpha = sqrt(2) gives an explicit counterexample to the source's stated decay assertion. The decisive Lean declaration is `disprove_decay_assertion`, whose statement is: ¬ DecayAssertion := by. Read against the filed statement, this establishes the negation of the printed clause identified in the README.

**Report correspondence.** The report, README and Lean sources were read. The report states the same construction and the same decisive conclusion; the Lean declaration matches the report's main theorem. The LaTeX source recompiled cleanly, and the build log reports only propext, Classical.choice and Quot.sound.

## Disposition

APPROVED — merged as PR 1079. The submission gives a complete, formalised disproof of conjecture 00000001715.
