# Solution Review — Conjecture 00000001470 (PR 1160)

**Submission:** lizaixi01 — `lizaixi01_submission_20261023181334`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000001470; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.33.0` and Mathlib revision `db584cd6d46c92f209a44c0f1c829460d327499d`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** The Lasserre moment/SOS hierarchy for a compact semialgebraic set presented by its defining polynomials of degree deg is exact at a level d* = ceil(deg/2) + O(1), uniformly in the input; exactness means the moment projection equals K and/or the moment and SOS optimal values equal the true minimum.

**Decisive results.** For the standard Lasserre hierarchy built from g1=X^3, g2=1-X^2 on K=[0,1] (degree 3), Lean constructs, for every r≥2, a genuine full linear functional L with L(1)=1, PSD moment matrix M_r(L), PSD localizing matrices M_{r-2}(X^3L) and M_{r-1}((1-X^2)L), and L(X)<0. The interpolation/atomic construction is checked against the actual matrix quadratic forms, not assumed. Hence K ⊊ momentValues r for every r, and both momentValue r and sosValue r are strictly below the true minimum 0 at every finite level. This is exactly the negation of the universal finite-exactness claim; the hypotheses (compact semialgebraic K, degree-3 input) are satisfiable and the conclusion is not assumed.

**Report correspondence.** report.tex Sections 1-3 state the same matrices, atomic functional, SOS certificate gamma=-1, weak duality, and inf/sup bounds as Main.lean. The PDF text matches the LaTeX (the PDF in the packet was recompiled by the review harness, hence the SHA256SUMS.pdf hash differs, but its content matches). No stronger prose claim.

## Disposition

APPROVED — merged as PR 1160. The submission gives a complete, formalised disproof of conjecture 00000001470.
