# Solution Review — Conjecture 00000001158 (PR 1186)

**Submission:** lizaixi01 — `lizaixi01_submission_20261024110523`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000001158; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.33.0` and Mathlib revision `db584cd6d46c92f209a44c0f1c829460d327499d`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** Literal rank-one boundedness clause: a lattice of ambient real rank one has bounded scl. Take the nonuniform lattice Γ(2)/{±I} in PSL2(R), which has real rank one and is a free group of rank two; its scl is unbounded, and it is not a knot-complement group because its abelianization is noncyclic.

**Decisive results.** The Lean theorem establishes the algebraic core: for the free group F2 it proves the Brooks count, the Fekete stable commutator length, the bounds N/12 ≤ scl(c^N) ≤ N, unboundedness of scl, and noncyclicity of F2's abelianization. The report identifies the nonuniform lattice Γ(2)/{±I} in PSL2(R) with F2 and records that it has ambient real rank one; the identification is the standard published Conrad/Morris result and is explicitly disclosed, not inserted as an axiom or assigned label. The theorem is invariant under group isomorphism (`stableCommutatorLength_equiv`, `isomorphic_group_unbounded`), so the F2 result transports to the lattice. The hypotheses are satisfiable and the conclusion is a concrete counterexample to the printed rank-one boundedness implication; the noncyclic abelianization excludes the usual knot-complement exception. The only non-blocking caveat is that the geometric identification and real-rank computation are cited rather than Lean-formalized.

**Report correspondence.** The report's main theorem about Γ(2)/{±I} and the Lean capstone about F2 agree modulo the explicitly disclosed standard identification Γ(2)/{±I} ≅ F2 and the cited real-rank computation. The report does not claim the Lean proves the Lie-geometric identification; it says this is external. The algebraic bounds, unboundedness and knot-abelianization argument match the Lean.

## Disposition

APPROVED — merged as PR 1186. The submission gives a complete, formalised disproof of conjecture 00000001158.
