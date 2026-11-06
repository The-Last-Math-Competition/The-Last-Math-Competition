# Solution Review — Conjecture 00000005512 (PR 1088)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261022104324`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000005512; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.19.0` and Mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** Definition: The supermarket model is the power-of-two load balancing strategy, sampling two queues at arrival and joining the shorter. Conjecture: The fixed point is an explicit hyperbolic-type distribution with tail a power law in the selection count, doubling the queue-length tail exponent; the location parameter of the hyperbolic fixed point is the ratio of arrival rate to total service rate; and the power-tail exponent diverges linearly as the sampling count tends to infinity. (supermarket hyperbolic fixed point with power tail) 定义：超市模型：两选一的负载平衡策略（到达时抽查两队列选短者）。猜想：固定点为显式双曲型分布且尾部为选择数次幂律——队长尾概率的指数加倍；双曲固定点的位置参数为到达率与总服务率之比；幂尾指数在抽查数趋于无穷时发散且发散率为线性。（超市双曲固定点幂尾）

**Decisive results.** The standard two-choice supermarket mean-field fixed point at load one half has survival tail q_k=2^{-(2^k-1)}, which decays faster than every inverse polynomial in queue length. The actual d-choice fixed-point family has q_d(2)=2^{-(d+1)}, which also decays faster than every inverse polynomial in selection count. Lean verifies the actual infinite drift equations, the two-choice fixed point and uniqueness, exact closed form, actual nonnegative probability masses of total one, all survival-tail identities, and the infinite asymptotic negations in both variables. The paper openly distinguishes genuine power tails from the correct d-th-power recursion reading and cites the classical model equations. Finite-server stochastic limit results are not claimed as formalized. From lean/ run `lake build`, then `lake env lean -DwarningAsError=true Main.lean`. The pinned Lean and Mathlib revisions are The decisive Lean declaration is `no_selection_count_power_tail`, whose statement is: ¬ PolynomialTail (fun d => tailD d 2) := by. Read against the filed statement, this establishes the negation of the printed clause identified in the README.

**Report correspondence.** The report, README and Lean sources were read. The report states the same construction and the same decisive conclusion; the Lean declaration matches the report's main theorem. The LaTeX source recompiled cleanly, and the build log reports only propext, Classical.choice and Quot.sound.

## Disposition

APPROVED — merged as PR 1088. The submission gives a complete, formalised disproof of conjecture 00000005512.
