# Solution Review — Conjecture 00000008908 (PR 1075)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261022095240`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000008908; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.19.0` and Mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** `verify.py` exited 0.

## Semantic audit

**Conjecture as filed.** Definition: The Lovasz theta function: homomorphisms and capacity. Conjecture: The monotonicity of theta: the monotone chain of the function, with the endpoints of the chain the independence number and the clique number of the complement. (Lovasz theta independence clique monotone chain endpoints) 定义：Lovász θ 函数：同态与容量。猜想：θ 的单调：函数的单调链且链的端为独立数与补数。（Lovasz theta 独立数补数函数单调链端点香农容量）

**Decisive results.** The actual simple five-cycle has independence number and complement clique number both equal to two, but the full standard Lovasz theta SDP is at least 5041/2257>2. An explicit rational Gram certificate disproves the monotone chain with the endpoints named in the English source. The decisive Lean declaration is `no_claimed_chain`, whose statement is: ¬ ((graph.indepNum : ℝ) ≤ theta graph ∧ theta graph ≤ (graphᶜ.cliqueNum : ℝ)) := by. Read against the filed statement, this establishes the negation of the printed clause identified in the README.

**Report correspondence.** The report, README and Lean sources were read. The report states the same construction and the same decisive conclusion; the Lean declaration matches the report's main theorem. The LaTeX source recompiled cleanly, and the build log reports only propext, Classical.choice and Quot.sound.

## Disposition

APPROVED — merged as PR 1075. The submission gives a complete, formalised disproof of conjecture 00000008908.
