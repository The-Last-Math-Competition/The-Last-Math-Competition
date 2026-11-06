# Solution Review — Conjecture 00000007991 (PR 1074)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261022095240`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000007991; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.19.0` and Mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** Definition: The optimal exponent alpha(p) of C^{1,alpha} regularity of solutions of the p-Laplace equation div(|grad u|^{p-2} grad u) = 0. Conjecture: The exact value of alpha(p) is the explicit expression min((p-1)/(2p-2 + p lambda_0), 1/(p-1)) with lambda_0 an explicit eigenvalue; alpha(p) returns to 1 at p = 2 (the harmonic limit); the slope limits of the graph of alpha(p) at the two endpoints p to infinity and p to 1 are -infinity and +infinity (endpoint cusps); and alpha(p) is a strictly decreasing continuous function of p on the segment p > 2. (p-Laplace optimal Holder exponent) 定义：p-Laplace 方程 div(|∇u|^{p-2}∇u)=0 的解的 C^{1,α} 正则性的最优指数 α(p)。猜想：α(p) 的精确值为 min((p-1)/(2p-2 + p·λ₀), 1/(p-1)) 型显式式（λ₀ 为某显式特征值）；且 α(p) 在 p=2 回到 1（调和极限）；α(p) 的图像在 p→∞ 与 p→1 两个端点的斜率极限为 -∞ 与 +∞（端点尖性）；α(p) 为 p 的严格递减连续函数（在 p>2 段）。

**Decisive results.** Every eventually lower-bounded real function is incompatible with an ordinary derivative tending to minus infinity at plus infinity. An optimal Holder regularity exponent is nonnegative, so the source's stated infinity-endpoint slope is impossible. The decisive Lean declaration is `proposed_formula_cusp_impossible`, whose statement is: theorem proposed_formula_cusp_impossible {ell : ℝ} (hα : 0 ≤ proposedFormula ell 3) : ¬ Tendsto (deriv (proposedFormula ell)) atTop atBot := by. Read against the filed statement, this establishes the negation of the printed clause identified in the README.

**Report correspondence.** The report, README and Lean sources were read. The report states the same construction and the same decisive conclusion; the Lean declaration matches the report's main theorem. The LaTeX source recompiled cleanly, and the build log reports only propext, Classical.choice and Quot.sound.

## Disposition

APPROVED — merged as PR 1074. The submission gives a complete, formalised disproof of conjecture 00000007991.
