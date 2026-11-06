# Solution Review — Conjecture 00000009783 (PR 1114)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261022115619`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000009783; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.19.0` and Mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** The source claims that for an AF algebra the closed ideal lattice is isomorphic to the hereditary-subset lattice of its Bratteli diagram, that the isomorphism preserves dimension-vector stratification, and that maximal ideal-chain length equals the supremum of diagram path depths. The submission takes the AF algebra C with the constant identity system C=M_1(C) at every stage and refutes the chain-depth clause.

**Decisive results.** Lean proves C is AF with all stages equal to the top closed finite-dimensional star subalgebra, that its closed ideals are exactly 0 and C, that every maximal chain is the whole two-element ideal set, and that the strict-inclusion length is 1 while the element count is 2. The constant one-block Bratteli diagram is a genuine Quiver with one vertex per level and one edge between consecutive levels; Lean constructs actual Quiver.Path objects of every finite length and proves pathDepth=top. Thus a genuine AF algebra with its standard diagram has ideal-chain length 1 (or 2 elements) but unbounded path depth, falsifying the claimed equality. Refuting this conjunct disproves the conjunction.

**Report correspondence.** The report proves the same C example, the AF/direct-limit property, the two closed ideals, the maximal chain, the one-block ray and both chain-length conventions. Lean's idealChainLength_one, idealChainElements_two, pathDepth_infinite and conjecture_9783_false match; the report explicitly disclaims the general hereditary-subset and dimension-vector clauses, which are not needed.

## Disposition

APPROVED — merged as PR 1114. The submission gives a complete, formalised disproof of conjecture 00000009783.
