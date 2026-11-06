# Solution Review — Conjecture 00000008262 (PR 1085)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261022103738`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000008262; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.19.0` and Mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** Definition: The spectral condition number ric_cond of the steady state P-infinity of the error-covariance Riccati equation of Kalman-Bucy filtering. Conjecture: ric_cond (the condition number of the steady Riccati) is at most the explicit double ratio (sigma_obs/sigma_sys)^2 (a double-ratio condition law); the rate of convergence of the steady state (transient decay) is the double decay 2|lambda_max(A) minus the observation gain (a double decay formula); and the mismatch radius of the robustness of filtering (stability domain under model mismatch) is the reciprocal 1/(2 cond) (a reciprocal radius law). (Kalman-Bucy Riccati condition double decay) 定义：Kalman–Bucy 滤波的误差协方差 Riccati 方程的稳态 P∞ 的谱条件数 ric_cond。猜想：ric_cond（稳态 Riccati 的条件数）≤ (σ_obs/σ_sys)² 的显式双比（双比条件律）；且稳态的收敛（暂态衰减）的速率为 2·|λ_max(A)-观测增益| 的双衰减（双衰减公式）；滤波的鲁棒性（模型失配下的稳定域）的失配半径 = 1/(2·cond) 的倒数（倒数半径律）。

**Decisive results.** For A=diag(3/4,-3/4), H=I and equal unit isotropic noises, the stabilizing covariance P=diag(2,1/2) has condition number four, contradicting the claimed bound one. Lean formalizes actual matrices, positive definiteness, the complete algebraic Riccati equation, complex-spectrum stability and the true real-spectrum extremal eigenvalue ratio. The final theorem negates the universal claimed bound. The paper gives the model interpretation and an explicit covariance trajectory converging from zero to P. The Brownian filtering interpretation and time-dependent trajectory are paper-only. They are not represented as having been formalized. Run `lake env lean -DwarningAsError=true Main.lean` in `lean/`. The direct check passed; parent fresh build and PDF review are separate. Developed by a delegated AI agent with a self-review; the coordinating agent reviews it separately. No external independent  The decisive Lean declaration is `conjecture8262_false`, whose statement is: ¬ ClaimedBound := by. Read against the filed statement, this establishes the negation of the printed clause identified in the README.

**Report correspondence.** The report, README and Lean sources were read. The report states the same construction and the same decisive conclusion; the Lean declaration matches the report's main theorem. The LaTeX source recompiled cleanly, and the build log reports only propext, Classical.choice and Quot.sound.

## Disposition

APPROVED — merged as PR 1085. The submission gives a complete, formalised disproof of conjecture 00000008262.
