# Solution Review — Conjecture 00000005501 (PR 1083)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261022103119`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000005501; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.19.0` and Mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** Definition: An open network is a Markovian network with exponential service. Conjecture: Near the stability boundary the queue length scales as the negative one-half power of the load deficit, with exponent given by the branching structure of the bottleneck and consistent with heavy-traffic diffusion; and the pre-exponential constant is exactly the load redistribution coefficient of the bottleneck branch. (half-power critical exponent of bottlenecks) 定义：开网络指指数服务的马尔可夫网络。猜想：稳定边界附近的队长按负载缺口的负二分之一次幂标度,指数由瓶颈的分支结构给出且与重话务扩散一致。(瓶颈临界指数半幂标度)；且指数前常数恰为瓶颈分支的负载重分配系数。

**Decisive results.** A genuine stationary open M/M/1 queue has mean rho/(1-rho). Along a stable sequence approaching load one, the actual probability captured by every fixed multiple of the proposed inverse-square-root deficit scale tends to zero. The decisive Lean declaration is `no_fixed_waiting_scaled_half_mass`, whose statement is: theorem no_fixed_waiting_scaled_half_mass (M : ℕ) : ¬ ∀ᶠ k in atTop, (1/2:ℝ)≤waitingCDF (load k) (load_mem k).1 (load_mem k).2 (M*(k+2)) := by. Read against the filed statement, this establishes the negation of the printed clause identified in the README.

**Report correspondence.** The report, README and Lean sources were read. The report states the same construction and the same decisive conclusion; the Lean declaration matches the report's main theorem. The LaTeX source recompiled cleanly, and the build log reports only propext, Classical.choice and Quot.sound.

## Disposition

APPROVED — merged as PR 1083. The submission gives a complete, formalised disproof of conjecture 00000005501.
