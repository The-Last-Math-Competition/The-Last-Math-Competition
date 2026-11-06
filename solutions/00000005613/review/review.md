# Solution Review — Conjecture 00000005613 (PR 1068)

**Submission:** Galaxy-0 — `Galaxy-0_submission_20261020202240`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000005613; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.31.0`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** The filed clause says a subresultant minor is zero iff the corresponding principal minor is zero. The submission uses the standard subresultant coefficient/principal convention: M_{k,t} is the coefficient minor obtained from the first k rows, first k−1 columns and column k+t, and the corresponding principal minor is M_{k,0}; it cites Kerber, Definitions 2.3.10–2.3.12.

**Decisive results.** For f=x³−4x and g=x²−1, the first Sylvester submatrix is generated from rows f, xg, g. It has M_{3,1}=0 while M_{3,0}=−3≠0. The inputs are monic, squarefree, coprime and strictly interlacing, so this is a literal instance of the universal vanishing-equivalence clause; the conclusion is its negation. The example does not refute the separate whole-subresultant statement, which the report explicitly disclaims.

**Report correspondence.** Report and Lean agree on the matrix, both determinants, the first subresultant −3x, the root/factorization facts, and the Bezout identity. The report states the same coefficient/principal convention and explicitly limits the claim to individual coefficient minors, not the whole polynomial subresultant.

## Disposition

APPROVED — merged as PR 1068. The submission gives a complete, formalised proof of conjecture 00000005613.
