# Solution Review — Conjecture 00000008333 (PR 1116)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261022121830`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000008333; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.19.0` and Mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** Definition: The arithmetic of the Markov spectrum of quadratic forms: the distribution mark_dist of Markov numbers (solutions of x^2 + y^2 + z^2 = 3xyz). Conjecture: mark_dist (the distribution density of Markov numbers) grows as c x^{1/2} (a half-exponential growth law); the density of the prime factor spectrum (distribution of prime Markov numbers) is log-log sparse (a log-log sparsity law); the completeness of the Markov tree (Cohn tree) branching (Fricke iteration) — the tree covers all Markov numbers — strengthens to unique representation (Frobenius uniqueness, a Frobenius uniqueness law); and the stationary distribution of random walks on the tree (random generation of Markov numbers) has the 1/3-2/3 bias (a biased stationarity law). (Markov half-exponential Frobenius biased walk) 定义：二次型的 Markov 谱的算术：Markov 数（x²+y²+z²=3xyz 的解）的分布 mark_dist。猜想：mark_dist（Markov 数的分布密度）~ c·x^{1/2} 的增长（半指数增长律）；且 Markov 数的素因子谱（素 Markov 数的分布）的密度为 log-log 型稀疏（log-log 稀疏律）；Markov 树（Cohn 树）的分支（Fricke 的迭代）的完全性（树覆盖一切 Markov 数）的已证的强化（唯一表示）为 Frobenius 唯一性（Frobenius 唯一律）；树的随机游走（Markov 数的随机生成）的分布的稳态为 1/3-2/3 

**Decisive results.** Under the standard cumulative counting interpretation, let M(X) count distinct positive integers m≤X for which positive integers a,b satisfy a²+b²+m²=3abm. The source asserts M(X)~c√X with c>0. We prove M(64^n) ≤ 2 + 3(6n+1)²·2^(2n+1), and hence M(64^n)/8^n→0. This contradicts the asserted positive-constant limit. It does not assume Frobenius uniqueness, count repeated numbers, or claim to settle the source's prime-number or random-walk clauses. The entire mathematical bridge is formalized: sorted positive Markov triples descend to (1,1,1)/(1,1,2) or the actual tree rooted at (1,2,5); every coordinate is 1,2, or the largest coordinate of an ancestor; growth bounds control the finite word collection; its image bounds the actual finite set of Markov numbers; and the real limit refutes every positive c. Main Lean theorem: `Markov8333.conjecture_8333_false : ¬Markov8333.SquareRootGrowth`. `S The decisive Lean declaration is `conjecture_8333_false`, whose statement is: ¬SquareRootGrowth := by. Read against the filed statement, this establishes the negation of the printed clause identified in the README.

**Report correspondence.** The report, README and Lean sources were read. The report states the same construction and the same decisive conclusion; the Lean declaration matches the report's main theorem. The LaTeX source recompiled cleanly, and the build log reports only propext, Classical.choice and Quot.sound.

## Disposition

APPROVED — merged as PR 1116. The submission gives a complete, formalised disproof of conjecture 00000008333.
