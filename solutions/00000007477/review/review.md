# Solution Review — Conjecture 00000007477 (PR 1166)

**Submission:** lizaixi01 — `lizaixi01_submission_20261023202224`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000007477; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.33.0` and Mathlib revision `db584cd6d46c92f209a44c0f1c829460d327499d`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** In the Perron-Frobenius setting for positive operators, irreducibility yields an eigenvector at the spectral radius (and positivity of the eigenvector is equivalent to irreducibility). The source states no finite-dimensionality or compactness hypothesis.

**Decisive results.** On the real Banach lattice c0(N;R), the half-line adjacency A with (Ax)_0=x_1 and (Ax)_{n+1}=x_n+x_{n+2} is bounded (norm ≤2), positive, and ideal irreducible: every closed solid invariant submodule contains a coordinate vector, adjacency propagates to all coordinates, and finite truncations converge, so it is 0 or the whole space. Its complexification has spectral radius exactly 2 (2 is in the spectrum because 2I-A has no e_0 preimage, and ||A||≤2). But Ax=2x forces x_n=(n+1)x_0, which is not in c0 unless x=0, so there is no nonzero spectral-radius eigenvector. This is exactly the negation of the eigenvector clause for an irreducible positive operator; the hypotheses are satisfiable.

**Report correspondence.** report.tex Sections 1-5 match the Lean construction (C0, pointwise lattice, solid norm, adjacency, ideal irreducibility, complexification, spectrum, spectral radius, nonexistence). PDF text matches. No stronger prose claim.

## Disposition

APPROVED — merged as PR 1166. The submission gives a complete, formalised disproof of conjecture 00000007477.
