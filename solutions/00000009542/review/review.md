# Solution Review — Conjecture 00000009542 (PR 1096)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261022111228`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000009542; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.19.0` and Mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** `verify.py` exited 0.

## Semantic audit

**Conjecture as filed.** Definition: Composite channel capacity is the reliable rate when the sender only knows that the true channel lies in a set W; random-coding capacity and deterministic-coding capacity can differ. Conjecture: The entanglement-assisted capacity of a finite composite quantum set {phi_i} is the minimax formula min_i max_rho I(rho, phi_i), and the formula extends continuously to compact composite sets; and the random-coding error exponent is the worst-channel exponent min_i E(R, phi_i). (composite capacity minimax) 定义：复合信道容量指发送端仅知真实信道属于集合 W 的条件下的可靠速率；随机编码容量与确定编码容量可分离。猜想：有限复合量子集 {φ_i} 的纠缠辅助容量为极小极大公式 min_i max_ρ I(ρ,φ_i)，该公式延拓到紧复合集时连续；随机编码错误指数为 min_i E(R,φ_i) 的最坏信道指数。（复合容量极小极大）

**Decisive results.** Three actual qutrit-to-classical-bit CPTP maps have common-input max-min quantum mutual information h(1/3), strictly below their min-max value log2. The compound entanglement-assisted coding theorem identifies the first value with operational capacity, refuting the proposed finite-set formula. The decisive Lean declaration is `strict_minimax_gap`, whose statement is: compoundSingleLetter < Finset.univ.inf' Finset.univ_nonempty individualSingleLetter := by. Read against the filed statement, this establishes the negation of the printed clause identified in the README.

**Report correspondence.** The report, README and Lean sources were read. The report states the same construction and the same decisive conclusion; the Lean declaration matches the report's main theorem. The LaTeX source recompiled cleanly, and the build log reports only propext, Classical.choice and Quot.sound.

## Disposition

APPROVED — merged as PR 1096. The submission gives a complete, formalised disproof of conjecture 00000009542.
