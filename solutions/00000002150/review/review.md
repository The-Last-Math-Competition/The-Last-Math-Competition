# Solution Review — Conjecture 00000002150 (PR 1100)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261022112032`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000002150; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.19.0` and Mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** Definition: The nullity of the signless Laplacian and bipartiteness. Conjecture: For general graphs, the dimension of the zero eigenspace is the count of bipartite components; and the kernel of the count is an arbitrary bipartite base graph. (signless arbitrary bipartite base zero-dimension count) 定义：signless Laplacian 零重数与二部性。猜想：一般图的零特征空间维数为分支二部性计数；且计数的核为任意二部母图。（signless 任意二部母图零维计数）

**Decisive results.** Lean proves that for every finite undirected simple graph the real nullity of the signless Laplacian Q=D+A equals the number of bipartite connected components, by constructing an explicit alternating-sign basis on each bipartite component. The theorem `conjecture : Conjecture` is the universal statement. This establishes the filed conjecture under the stated finite simple-graph reading.

**Report correspondence.** The report, README and Lean sources were read. The report states the same construction and the same decisive conclusion; the Lean declaration matches the report's main theorem. The LaTeX source recompiled cleanly, and the build log reports only propext, Classical.choice and Quot.sound.

## Disposition

APPROVED — merged as PR 1100. The submission gives a complete, formalised proof of conjecture 00000002150.
