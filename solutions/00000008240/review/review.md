# Solution Review — Conjecture 00000008240 (PR 1092)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261022105459`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000008240; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.19.0` and Mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** Definition: The critical discounting of cooperation in repeated games: the explicit formula folk_delta for the critical discount factor of the folk theorem. Conjecture: folk_delta (the critical discount for cooperation) is the explicit ratio of the one-period defection payoff to the cooperative payoff (an explicit ratio formula); the correction of the critical discount under noise (imperfect monitoring) is a linear inflation in the noise variance sigma^2 (a linear inflation law); and the spectrum of the critical discounts over static profiles is a finite union of closed intervals inside (0,1) (a finite interval union law), the interval endpoints being the switching points of defection-punishment (a switching endpoint law). (folk critical discount explicit ratio intervals) 定义：重复博弈的合作的临界贴现：Folk 定理的临界贴现因子 δ_c 的显式公式 folk_delta。猜想：folk_delta（合作的临界贴现）= 单期背叛收益与合作收益的显式比（显式比公式）；且噪声（不完全监测）下的临界贴现的修正为噪声方差 σ² 的线性膨胀（线性膨胀律）；临界贴现的博弈族的谱（一切静态剖面的 δ_c 的值）为介于 0 与 1 之间的有限并闭区间（有限区间并律），区间的端点为背叛-惩罚的切换点（切换端点律）。

**Decisive results.** The first conjunct equates the cooperation discount threshold with the raw one-period defection payoff divided by the cooperation payoff. In the repeated prisoner's dilemma with T=3, R=2, P=1, S=0, grim trigger is a cooperative subgame-perfect equilibrium at discount 1/2, so the critical discount over all cooperative pure history-dependent SPE is at most 1/2. The proposed raw ratio is 3/2. The counterexample is classical, not a new folk theorem. The paper cites Jonathan Levin's *Repeated Games I: Perfect Monitoring*, Proposition 1, and a Northwestern course handout giving the exact stage-payoff table. The argument is independent of those references and is reproduced completely. The decisive Lean declaration is `conjecture8240_false`, whose statement is: ¬ ClaimedRatio := by. Read against the filed statement, this establishes the negation of the printed clause identified in the README.

**Report correspondence.** The report, README and Lean sources were read. The report states the same construction and the same decisive conclusion; the Lean declaration matches the report's main theorem. The LaTeX source recompiled cleanly, and the build log reports only propext, Classical.choice and Quot.sound.

## Disposition

APPROVED — merged as PR 1092. The submission gives a complete, formalised disproof of conjecture 00000008240.
