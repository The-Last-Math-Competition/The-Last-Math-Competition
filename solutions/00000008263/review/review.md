# Solution Review — Conjecture 00000008263 (PR 1090)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261022105135`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000008263; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.19.0` and Mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** Definition: The collapse threshold of particle filters (sequential Monte Carlo): the collapse rate coll_rate of the effective sample size N_eff. Conjecture: coll_rate (per-step effective particle decay) is the explicit 1 - kappa^2 (kappa the incremental information, a kappa-squared decay law); the optimal resampling (systematic versus multinomial) halves the variance (a variance halving law); and the constant in the particle-count law for the consensus of particle counts (L^2 error of the filtering distribution equal to c/N) is half of Var(weight) times the dimension (a Var-dimension half law). (particle collapse kappa-squared variance halving) 定义：粒子滤波（sequential Monte Carlo）的粒子数塌缩的阈值：有效样本数 N_eff 的塌缩率 coll_rate。猜想：coll_rate（每步的有效粒子衰减）= 1-κ² 的显式（κ 为增量信息，κ² 衰减律）；且重采样的最优（系统重采样 vs 多项式）的方差的减半（方差减半律）；粒子数的共识（滤波分布的 L² 误差 = c/N 的粒子数定律）的常数 c = Var(权重)·维度的半数（Var-维度半数律）。

**Decisive results.** Four positive weights (1/8,3/8,1/8,3/8), observable (1,0,1,0), and the standard systematic ordering yield variance 1/16 versus multinomial variance 3/64. Both expectations are 1/4, so systematic resampling is strictly worse. This refutes both exact and at-most variance halving. Lean uses the actual inverse-CDF algorithm, all real phase outputs via a generic ordered-field proof, finite probability laws with normalization, and the product categorical multinomial law on all 256 outcomes. It computes the actual centered variances and negates the necessary halving claim over every rational observable on this legal input population. The elementary identification of continuous uniform phase probabilities with the two equal-length phase strata is paper-only and explicit. The known variance-ordering failure is credited to Douc, Cappe, Moulines (2005), https://arxiv.org/abs/cs/0507025. Run `lake e The decisive Lean declaration is `conjecture8263_false`, whose statement is: ¬ HalvingClaim := by. Read against the filed statement, this establishes the negation of the printed clause identified in the README.

**Report correspondence.** The report, README and Lean sources were read. The report states the same construction and the same decisive conclusion; the Lean declaration matches the report's main theorem. The LaTeX source recompiled cleanly, and the build log reports only propext, Classical.choice and Quot.sound.

## Disposition

APPROVED — merged as PR 1090. The submission gives a complete, formalised disproof of conjecture 00000008263.
