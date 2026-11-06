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

**Conjecture as filed.** The source claims that the 3D covering-packing gap is an explicit cell-diameter expression, minimal at the BCC lattice, and that the spectrum of the gap in dimension three is a closed interval with endpoints attained by the cubic lattice. The submission reads 'spectrum' as the set of gap values over all full-rank 3D Euclidean lattices and tests the rectangular family tZ×Z×Z.

**Decisive results.** Lean defines packing and covering radii as actual extrema over the Euclidean lattice, proves the packing radius is 1/2 and the covering radius is sqrt(t²+2)/2 for t≥1, and hence gap(t)=sqrt(t²+2). `valid_lattice_unbounded` shows for every B there is a full-rank discrete lattice with gap>B, so the spectrum is unbounded above. A closed interval with an upper endpoint attained by the cubic lattice cannot have unbounded values; the 'endpoints attained' conjunct is therefore false. The separate BCC-minimum and algebraic-value claims are not needed.

**Report correspondence.** The report proves the same rectangular family, the same exact radius computations, the same unboundedness theorem and the same `no_upper_endpoint` conclusion. It explicitly notes that unboundedness alone does not rule out a half-infinite interval, but does refute the claimed attained finite upper endpoint, which is the clause used.

## Disposition

APPROVED — merged as PR 1065. The submission gives a complete, formalised disproof of conjecture 00000005609.
