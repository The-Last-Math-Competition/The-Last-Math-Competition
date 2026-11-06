# Solution Review — Conjecture 00000005207 (PR 1067)

**Submission:** Galaxy-0 — `Galaxy-0_submission_20261020200400`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000005207; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.31.0`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** The filed clause says the noncommutative-minus-commutative rank gap is multiplicative under tensor products, within order three. The submission reads this as gap(X⊗Y)=gap(X)gap(Y) for matrix spaces of size at most 3, with standard commutative rank (max scalar specialization) and noncommutative rank (max normalized tensor blowup).

**Decisive results.** For the 3×3 skew-symmetric space S, commutative rank 2 and noncommutative rank 3; for the 1×1 scalar space U both ranks are 1. S⊗U is S entrywise (proved by tensor_unit), so gap(S⊗U)=1 while gap(S)gap(U)=(1)(0)=0. All factors and the product have size at most 3, so this is inside the literal order-three clause. The conclusion is the negation of the universal multiplicativity law.

**Report correspondence.** Report and Lean agree: both give exact rank certificates (symbolic determinant zero, attaining minor, explicit nonsingular 6×6 blowup) and the tensor-unit identity. The report explicitly does not interpret the undefined 'multiplicative deficit' phrase, which is not needed to refute the explicit equality.

## Disposition

APPROVED — merged as PR 1067. The submission gives a complete, formalised proof of conjecture 00000005207.
