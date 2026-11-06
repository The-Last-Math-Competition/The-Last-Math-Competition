# Solution Review — Conjecture 00000002362 (PR 1084)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261022103633`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000002362; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.19.0` and Mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** Definition: The H∞ calculus of sectorial operators is the sector function calculus. Conjecture: The bound constant of the calculus is an explicit function of the sector angle; and the singularity of the function diverges as the angle tends to π. (sector calculus bound constant divergence) 定义：sectorial 算子的 H∞ 演算为扇形函数演算。猜想：演算的界常数为扇形角的显式函数；且函数的奇性在角趋于 π 发散。（扇形演算界常数发散）

**Decisive results.** On genuine Euclidean C^2, A_N=I+N E12 are all sectorial of angle zero and belong to the same Sect(pi/3) class. The same admissible rational H0-infinity test g(z)=z/(1+z)^3 on Sigma(pi/2) has scalar sup norm at most one but g(A_N)=I/8-N E12/16 has unbounded operator norm. The decisive Lean declaration is `no_fixed_positive_angle_bound`, whose statement is: ¬ ∃ C : ℝ, ∀ A : B, Sectorial (Real.pi/3) A → ‖operatorRationalValue A‖ ≤ C := by. Read against the filed statement, this establishes the negation of the printed clause identified in the README.

**Report correspondence.** The report, README and Lean sources were read. The report states the same construction and the same decisive conclusion; the Lean declaration matches the report's main theorem. The LaTeX source recompiled cleanly, and the build log reports only propext, Classical.choice and Quot.sound.

## Disposition

APPROVED — merged as PR 1084. The submission gives a complete, formalised disproof of conjecture 00000002362.
