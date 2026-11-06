# Solution Review — Conjecture 00000000506 (PR 1069)

**Submission:** Galaxy-0 — `Galaxy-0_submission_20261021194220`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000000506; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.31.0`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** `reproduce.py` exited 0.

## Semantic audit

**Conjecture as filed.** The filed clause says that for a monomial ideal the support of the first Betti row β_{1,j} is connected and has no isolated points. The submission reads support as the graded support of the minimal-generator quotient K/mK of the first syzygy module, and 'no isolated points' topologically (a point with an open neighbourhood meeting the support only in itself), also checking the graph-adjacency reading.

**Decisive results.** For I=(X,Y) in F2[X,Y], the minimal free resolution is 0→R(−2)→R(−1)²→I→0, so the first Betti support is the singleton {2}. A singleton is connected but its only point is isolated in the subspace topology (and has no neighbour under any irreflexive adjacency). Thus the universal no-isolated-points clause is false. The Lean constructs the actual polynomial ring, edge ideal, minimal resolution, quotient K/mK and its support, rather than postulating a table.

**Report correspondence.** Report and Lean agree: both prove the exact resolution, the support identity ∀d, FirstBettiSupportZ d ↔ d=2, and the failure of NoIsolatedPoints for every topology. The report also covers the alternative quotient-ring indexing and the graph reading. No stronger claim is made.

## Disposition

APPROVED — merged as PR 1069. The submission gives a complete, formalised disproof of conjecture 00000000506.
