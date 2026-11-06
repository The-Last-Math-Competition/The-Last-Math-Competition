# Solution Review — Conjecture 00000001104 (PR 1138)

**Submission:** Galaxy-0 — `Galaxy-0_submission_20261022201500`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000001104; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.31.0`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** The filed clause says that for every Coxeter system and every parabolic I, the parabolic KL polynomial P^I_{x,w} has leading coefficient 1, with an affine-A1/(B3,B2) exception. The submission takes type A4, W=S5, I=∅, x=id, w=34512. For I=∅ the parabolic polynomial is the ordinary KL polynomial.

**Decisive results.** The Lean implements the standard right-descent KL recurrence on all 120 permutations of S5, proves the recurrence is well-founded and unique, and kernel-computes P_{id,34512}=1+2q. Its leading coefficient is 2, not 1. The trivial parabolic subgroup contains no affine A1, so this is outside the stated exception. The conclusion is the negation of the universal monicity clause. The hypotheses (I=∅ is allowed; the group is finite type A4) are satisfiable.

**Report correspondence.** Report and Lean agree: both give P=1+2q, the witness permutation, the recurrence and its uniqueness, and the non-monic conclusion. The report explicitly says the abstract Hecke-algebra identification is the cited standard theorem, not formalized; the Lean verifies the recurrence computation.

## Disposition

APPROVED — merged as PR 1138. The submission gives a complete, formalised disproof of conjecture 00000001104.
