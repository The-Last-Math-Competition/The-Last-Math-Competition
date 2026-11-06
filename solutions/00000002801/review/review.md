# Solution Review — Conjecture 00000002801 (PR 1078)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261022101351`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000002801; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.19.0` and Mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** Definition: The large deviation principle (LDP): a rate function I controls the exponential decay of tail probabilities. Conjecture: The optimal lower bound for the rate function of the LDP of empirical measures of Markov chains: for irreducible chains the zero of I is unique, and the Hessian of I at the zero is a constant multiple of the Fisher information; the constant is the reciprocal of the spectral gap. (chain empirical-measure rate Hessian) 定义：大偏差原理（LDP）：速率函数 I 控制尾概率的指数衰减。猜想：马尔可夫链的经验测度的 LDP 的速率函数的最优下界：不可约链的 I 的零点唯一且 I 的 Hessian 在零点为 Fisher 信息的常数倍；常数为谱隙的倒数。（链经验测度速率 Hessian）

**Decisive results.** The actual two-state deterministic alternating chain is irreducible. Its full empirical-measure distributions obey a good LDP with unique-zero rate I(pi)=0 and I=+infinity everywhere else, so the rate has no ordinary real Hessian at its stationary zero. The decisive Lean declaration is `no_local_real_rate`, whose statement is: ¬ ∃ δ : ℝ, 0<δ ∧ ∃ f : ℝ → ℝ, ∀ t : ℝ, |t|<δ → |t|<1/2 → rate (probabilityLine t) = (f t : EReal) := by. Read against the filed statement, this establishes the negation of the printed clause identified in the README.

**Report correspondence.** The report, README and Lean sources were read. The report states the same construction and the same decisive conclusion; the Lean declaration matches the report's main theorem. The LaTeX source recompiled cleanly, and the build log reports only propext, Classical.choice and Quot.sound.

## Disposition

APPROVED — merged as PR 1078. The submission gives a complete, formalised disproof of conjecture 00000002801.
