# Solution Review — Conjecture 00000007841 (PR 1073)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261022091401`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000007841; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.19.0` and Mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** `verify.py` exited 0.

## Semantic audit

**Conjecture as filed.** Definition: The success probability p(G) of Karger's contraction algorithm on an n-vertex graph is the probability that the random contraction sequence outputs a minimum cut; the optimal contraction schedule ratio rho(G) is the infimum over connected n-vertex graphs of p(G) relative to the theoretical extremum 2/n^2. Conjecture: The limit constant of rho is e^{-1/2}, attained asymptotically by near-complete graphs; and for every simple graph the explicit bound p(G) >= 2(1-epsilon)/n^2 with epsilon(n) = O(1/n) follows from the independent repetition combinatorial bound, tight on the cycle. (Karger contraction extremal ratio) 定义：Karger 收缩算法在 n 点图上的成功概率 p(G) 为随机收缩序列产生最小割的概率。定义最优收缩调度比 ρ(G) 为 p(G) 与理论极值 2/n² 之比在一切 n 点连通图上的下确界。猜想：ρ 的极限常数为 e^{-1/2}（由完全图的近似下界达到渐近），且对一切简单图 p(G) ≥ 2(1-ε)/n² 的显式 ε(n)=O(1/n) 可由独立重复的组合下界给出，界在圈图上精确取等。

**Decisive results.** For every simple connected cycle C_n, n>=3, the actual uniform-edge Karger contraction algorithm returns some minimum cut with probability one. The claimed cycle-sharp expression 2(1-epsilon(n))/n^2 tends to zero for epsilon(n)=O(1/n), and its gap from the actual success probability tends to one. The decisive Lean declaration is `actual_gap_not_tends_zero`, whose statement is: theorem actual_gap_not_tends_zero (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0)) : ¬ Tendsto (fun k : ℕ => actualSuccessProbability k - 2 * (1-ε k) / (k+2)^2) atTop (𝓝 0) := by. Read against the filed statement, this establishes the negation of the printed clause identified in the README.

**Report correspondence.** The report, README and Lean sources were read. The report states the same construction and the same decisive conclusion; the Lean declaration matches the report's main theorem. The LaTeX source recompiled cleanly, and the build log reports only propext, Classical.choice and Quot.sound.

## Disposition

APPROVED — merged as PR 1073. The submission gives a complete, formalised disproof of conjecture 00000007841.
