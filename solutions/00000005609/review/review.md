# Solution Review — Conjecture 00000005609 (PR 1065)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261020024352`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000005609; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.19.0` and Mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** Definition: The covering-packing gap is the ratio of covering radius to packing radius. Conjecture: The gap of three-dimensional lattices is always the explicit expression of the cell diameter ratio, minimal at the body-centered cubic; the minimum is the optimal covering-packing ratio, an algebraic number; and the spectrum of the gap in three dimensions is a closed interval with endpoints attained by the cubic lattice. (body-centered cubic minimal gap diameter ratio) 定义：覆盖-堆积间隙：覆盖半径与堆积半径之比。猜想：三维格的间隙恒为胞腔直径比的显式式且体心立方处极小；极小值为覆盖堆积的最优比且比值为代数数；间隙的谱在三维为闭区间且端点由立方格达到。（体心立方极小间隙直径比）

**Decisive results.** For each t>=1 the actual full-rank discrete Euclidean lattice Lambda_t={(tm,n,p):m,n,p integers} has packing radius 1/2 and covering radius sqrt(t^2+2)/2. Their ratio sqrt(t^2+2) is unbounded. Thus its three-dimensional spectrum cannot have the asserted finite upper endpoint attained by a cubic lattice. The decisive Lean declaration is `no_upper_endpoint`, whose statement is: ¬ ∃ B : ℝ, ∀ t : ℝ, 1 ≤ t → gap t ≤ B := by. Read against the filed statement, this establishes the negation of the printed clause identified in the README.

**Report correspondence.** The report, README and Lean sources were read. The report states the same construction and the same decisive conclusion; the Lean declaration matches the report's main theorem. The LaTeX source recompiled cleanly, and the build log reports only propext, Classical.choice and Quot.sound.

## Disposition

APPROVED — merged as PR 1065. The submission gives a complete, formalised disproof of conjecture 00000005609.
