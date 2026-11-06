# Solution Review — Conjecture 00000007717 (PR 1064)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261020023648`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000007717; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.19.0` and Mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** `verify.py` exited 0.

## Semantic audit

**Conjecture as filed.** The source claims that for all periodic tessellation cell graphs of bounded geometry (vertex degree ≤D, cell edge count ≤E), λ1≥c/D² for a universal c>0, and that the optimal c is c=λ1(hex)/4=3/16. The submission reads D as the graph's degree bound, so the square quotient has D=4 and the claimed bound is (3/16)/4²=3/256.

**Decisive results.** Lean constructs the actual quotient of the square tessellation by the period subgroup 64Z×4Z on Z/64×Z/4. It proves the quotient is connected, 4-regular, that each square cell has four distinct vertices and four edges, and that the actual combinatorial Laplacian has a least positive eigenvalue gap with 0<gap<(3/16)/4². The explicit eigenvector cos(π i/32) gives eigenvalue 2-2cos(π/32)<3/256, and a finite positive-eigenvalue argument supplies the least positive eigenvalue. This refutes the claimed optimal constant c=3/16 at D=4 under the natural per-graph reading of D.

**Report correspondence.** The report and Lean agree: the same 64×4 quotient, the same degree/cell checks, the same cosine eigenvector and the same strict bound gap<3/256. The report's D=4 and E=4 are exactly the Lean degree and four-edge cell certificates.

## Disposition

APPROVED — merged as PR 1064. The submission gives a complete, formalised disproof of conjecture 00000007717.
