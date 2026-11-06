# Solution Review — Conjecture 00000000470 (PR 1082)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261022102708`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000000470; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.19.0` and Mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** `verify.py` exited 0.

## Semantic audit

**Conjecture as filed.** Definition: The random weighted tree polynomial τ_p(G) = Σ_T p^{w(T)}, over spanning trees T of G, where w(T) is a sum of independent random edge weights. Conjecture: For vertex-transitive graph families, the arguments of the complex conjugate roots of p become asymptotically uniformly distributed over the interval from 0 to 2π, and the Kolmogorov distance between the empirical argument measure and the uniform measure is O(v^{-1/2}), where v is the vertex count. 定义：随机加权树多项式 τ_p(G)=Σ_{T}p^{w(T)},T 取遍 G 的生成树,w(T) 为独立随机边权之和。猜想：对顶点传递图族,p 的共轭复根的辐角渐近均匀分布于从 0 到 2π 的区间,且辐角经验测度与均匀测度的 Kolmogorov 距离为 O(v^{-1/2}),v 为顶点数。

**Decisive results.** For actual cycles with independent fair edge weights 1 or 2, the genuine spanning-tree polynomial has exactly one nonzero negative root on an event of probability tending to one. Its nonempty empirical angular measure stays at Kolmogorov distance at least 1/2 from uniformity. The decisive Lean declaration is `all_failure_not_tends_zero`, whose statement is: ¬ Tendsto (fun n : ℕ => eventProbability n (fun σ => 0 < (treePolynomial n σ).roots.card ∧ (1/2 : ℝ) ≤ KS (treePolynomial n σ).roots)) atTop (𝓝 0) := by. Read against the filed statement, this establishes the negation of the printed clause identified in the README.

**Report correspondence.** The report, README and Lean sources were read. The report states the same construction and the same decisive conclusion; the Lean declaration matches the report's main theorem. The LaTeX source recompiled cleanly, and the build log reports only propext, Classical.choice and Quot.sound.

## Disposition

APPROVED — merged as PR 1082. The submission gives a complete, formalised disproof of conjecture 00000000470.
