# Solution Review — Conjecture 00000009778 (PR 1112)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261022115051`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000009778; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.19.0` and Mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** `verify.py` exited 0.

## Semantic audit

**Conjecture as filed.** Definition: Singular values of the Volterra operator: the compact operator with interval-indicator integration kernel. Conjecture: The complete asymptotic expansion of Volterra singular values exists: the leading term is 1/(pi n) with corrections an odd-power series; each coefficient of the series is an explicit rational combination of Bernoulli numbers. (Volterra singular value full expansion) 定义：Volterra 算子的奇异值：积分核为区间示性的紧算子。猜想：Volterra 算子奇异值的完全渐近展开存在：主项为 1/(πn) 且修正项为奇次幂级数；级数的每个系数为 Bernoulli 数的显式有理组合。（Volterra 奇异值全展开）

**Decisive results.** The actual L2(0,1) Volterra singular values are s_n=1/[pi(n-1/2)], so n^2(s_n-1/(pi*n)) tends to 1/(2*pi), not zero. This excludes the necessary third-order condition for the claimed odd-only Poincare expansion and survives every integer change of starting index. The decisive Lean declaration is `gram_spectrum_refutes_odd_expansion`, whose statement is: theorem gram_spectrum_refutes_odd_expansion (s : ℕ → ℝ) (hnonneg : ∀ n, 1 ≤ n → 0 ≤ s n) (hgram : ∀ n, 1 ≤ n → (s n)^2 = 4 / (((2*(n : ℝ)-1)^2) * Real.pi^2)) : ¬ OddExpansionThroughThree s := by. Read against the filed statement, this establishes the negation of the printed clause identified in the README.

**Report correspondence.** The report, README and Lean sources were read. The report states the same construction and the same decisive conclusion; the Lean declaration matches the report's main theorem. The LaTeX source recompiled cleanly, and the build log reports only propext, Classical.choice and Quot.sound.

## Disposition

APPROVED — merged as PR 1112. The submission gives a complete, formalised disproof of conjecture 00000009778.
