# Solution Review — Conjecture 00000009690 (PR 1062)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261020021535`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000009690; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.19.0` and Mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** `verify.py` exited 0.

## Semantic audit

**Conjecture as filed.** Definition: Baker's logarithmic linear forms: lower bounds |Lambda| at least B^{-kappa} for Q-linear combinations of logarithms of algebraic numbers. Conjecture: The optimal exponent is kappa = 1: lower bounds for logarithmic linear forms can be improved to (log B)^{-1-epsilon} for every epsilon > 0, and the exponent 1 cannot be broken; breaking is excluded by explicit constructions of near-degenerate linear forms. (Baker optimal exponent) 定义：Baker 对数线性型：代数数对数的 Q 线性组合的下界 |Λ|≥B^{−κ}。猜想：最优指数为 κ=1：对数线性型下界可改进为 (log B)^{−1−ε} 对任意 ε>0 且指数 1 不可突破；突破将由近退化线性型的显式构造排除。（Baker 最优指数）

**Decisive results.** For fixed algebraic arguments 2 and 3, Dirichlet approximation produces integer forms a log 2 - b log 3 with nonzero absolute value at most log 3/(N+1) and coefficient bounds a<=N, b<=N+1. Their actual height is H=max(3,a,b). For every positive C and actual-height cutoff H0, the proof constructs a form with H>=H0 and absolute value below C/(log H)^2. Hence the proposed bound fails already at epsilon=1, even with arbitrary implied constants and sufficiently-large-height qualifications. The decisive Lean declaration is `no_uniform_bound`, whose statement is: ¬ ∃ C : ℝ, 0 < C ∧ ∃ H₀ : ℕ, ∀ a b : ℕ, 0 < a → H₀ ≤ height a b → C / (Real.log (height a b)) ^ 2 ≤ |linearForm a b| := by. Read against the filed statement, this establishes the negation of the printed clause identified in the README.

**Report correspondence.** The report, README and Lean sources were read. The report states the same construction and the same decisive conclusion; the Lean declaration matches the report's main theorem. The LaTeX source recompiled cleanly, and the build log reports only propext, Classical.choice and Quot.sound.

## Disposition

APPROVED — merged as PR 1062. The submission gives a complete, formalised disproof of conjecture 00000009690.
