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

**Conjecture as filed.** The filed statement is about the signless Laplacian Q = D + A of a finite undirected simple graph: the zero-eigenspace dimension is the number of bipartite connected components, and the kernel has an explicit bipartite-component basis. 'General graphs' is read in the standard finite simple-graph matrix setting; the undefined phrase 'the kernel of the count is an arbitrary bipartite base graph' is reconstructed as the explicit alternating-sign kernel basis.

**Decisive results.** Lean proves the quadratic identity x^T Q x = sum over edges (x_u+x_v)^2, the exact kernel condition x_u = -x_v on every edge, and that a nonzero kernel value forces its connected component to be bipartite. It constructs one alternating-sign vector per bipartite component, proves linear independence, spanning, and the resulting basis, and concludes finrank ker Q = number of bipartite components for every finite vertex type and simple graph. The statement is universal over all finite simple graphs, including isolated vertices and the empty graph. The second clause is not a separate well-defined operation in the source; the submission's explicit basis is a faithful concrete realization of the kernel statement.

**Report correspondence.** The report's Theorem 1, its basis construction, and its dimension conclusion match `nullity_eq_bipartite_components`, `signlessKernelBasis`, and `conjecture`. The report explicitly discloses the interpretation of the undefined second phrase and does not claim a separate base-graph construction.

## Disposition

APPROVED — merged as PR 1100. The submission gives a complete, formalised proof of conjecture 00000002150.
