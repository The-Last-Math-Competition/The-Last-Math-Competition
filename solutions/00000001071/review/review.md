# Solution Review — Conjecture 00000001071 (PR 1111)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261022114815`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000001071; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.19.0` and Mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** Definition: The quadratic-residue graph (adjacency by ±1). Conjecture: The deviation of the smallest eigenvalue of QR(p) from the limit −2√p is at most p^{−1/4+ε}, and the spectral gap is uniform via Weil sums (QR spectral uniformity). 定义：二次剩余图(±1 邻接)。猜想：QR(p) 的最小特征值的极限 −2√p 的偏差 ≤ p^{−1/4+ε} 且谱间隙由 Weil 和均匀(QR 谱均匀)。

**Decisive results.** The standard Paley graph at prime order p = 1 (mod 4) has smallest adjacency eigenvalue at least -(1 + sqrt(p))/2. Its discrepancy from -2 sqrt(p) is therefore at least (3 sqrt(p) - 1)/2 and is unbounded on those primes. The source's literal difference-±1 reading gives the cycle graph, with discrepancy at least 2 sqrt(p) - 2. Both readings contradict the claimed error even with an arbitrary Big-O constant and an arbitrary starting point. The decisive Lean declaration is `not_spectralClaim`, whose statement is: ¬ SpectralClaim := by. Read against the filed statement, this establishes the negation of the printed clause identified in the README.

**Report correspondence.** The report, README and Lean sources were read. The report states the same construction and the same decisive conclusion; the Lean declaration matches the report's main theorem. The LaTeX source recompiled cleanly, and the build log reports only propext, Classical.choice and Quot.sound.

## Disposition

APPROVED — merged as PR 1111. The submission gives a complete, formalised disproof of conjecture 00000001071.
