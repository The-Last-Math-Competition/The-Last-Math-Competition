# Solution Review — Conjecture 00000005268 (PR 1099)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261022112031`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000005268; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.19.0` and Mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** The filed statement says finite-time collision of three point vortices is impossible for general strength triples, with an explicit additional integral excluding it. I read the point-vortex system as the standard planar Hamiltonian ODE with the conventional 1/(2*pi) factor, and 'general strength triples' as allowing mixed signs. A finite-time total collision means the vortices are pairwise distinct on [0,T) and all converge to one point as t -> T^-.

**Decisive results.** Lean constructs the explicit trajectory z_i(t) = c + u(t) w_i with u(t)=exp((1/2 + (119/15)i) log(1-2t)). It proves the actual conventional vortex ODE with nonzero physical circulations 2*pi*gamma, exact initial positions 0, 1, 3/8+(7/8)i, injectivity for every t, and all three one-sided limits equal to c=3/8-(15/56)i at T=1/2. `conjecture_false` instantiates the universal exclusion with this nonzero mixed-sign triple and derives a contradiction. Thus the universal impossibility claim is negated; the hypotheses (nonzero circulations, T>0, injectivity before T, ODE on [0,T)) are all satisfied. The additional-integral clause is not needed once the impossibility clause is refuted.

**Report correspondence.** The report's displayed q, u, c, and shape values match the Lean definitions, and its theorem matches `trajectory_solves`, `trajectory_collapses`, and `conjecture_false`. The report correctly notes that the Hamiltonian reformulation and a classification of collapsing triples are not formalized; neither is needed for the counterexample.

## Disposition

APPROVED — merged as PR 1099. The submission gives a complete, formalised disproof of conjecture 00000005268.
