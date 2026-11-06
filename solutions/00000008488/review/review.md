# Solution Review — Conjecture 00000008488 (PR 1169)

**Submission:** lizaixi01 — `lizaixi01_submission_20261024030413`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000008488; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.33.0` and Mathlib revision `db584cd6d46c92f209a44c0f1c829460d327499d`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** For compact systems, the finite-scale values n^{-1} log r_n(U) of the equivalent Bowen-entropy definitions converge to the entropy with a uniform 1/n rate (the harmonic decay law).

**Decisive results.** Let X={x∈{0,1}^N : at most one coordinate is 1} with the left shift. X is compact and the shift is continuous; Lean proves the native Bowen-Dinaburg coverEntropy is 0. At the fixed entourage U_1 (agreement on the first coordinate), the n-th dynamical entourage is agreement on the first n coordinates, and the n+1 points z,e_0,...,e_{n-1} give a spanning cover with pairwise disjoint U_n-balls; hence the actual minimum spanning number is exactly n+1. The finite-scale value is therefore log(n+1)/n, and for every C∈R and N there is n≥N with C/n<log(n+1)/n, so no eventual C/n error bound exists. This is exactly the negation of the 1/n rate clause.

**Report correspondence.** report.tex Sections 1-4 match the Lean system, the exact n+1 spanning count, the zero entropy, and the quantified failure of the harmonic bound. PDF text matches. No stronger prose claim.

## Disposition

APPROVED — merged as PR 1169. The submission gives a complete, formalised disproof of conjecture 00000008488.
