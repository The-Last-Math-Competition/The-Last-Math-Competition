# Solution Review — Conjecture 00000002698 (PR 1164)

**Submission:** lizaixi01 — `lizaixi01_submission_20261023193507`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000002698; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.33.0` and Mathlib revision `db584cd6d46c92f209a44c0f1c829460d327499d`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** For a polynomial iterated map over a non-Archimedean field, the periodic points of its standard coefficientwise min-plus tropicalization agree with the valuations of the classical periodic points; the same for each positive iterate.

**Decisive results.** Take f(X)=X+1 over Q5. Lean constructs the actual coefficientwise tropicalization from Polynomial Q5, with v5(0)=+∞, and proves T_f(w)=min(w,0). The value -1 is in the range of v5 (v5(1/5)=-1), and T_f(-1)=-1, so -1 is a tropical periodic (indeed fixed) point. But f has no classical periodic points in characteristic zero (x+k=x forces k=0), so val '' Per(f)=∅. Hence the two sets differ; the same is proved for every positive iterate X+n, whose tropicalization is min(w,v5(n)) and still fixes -1. This is exactly the negation of the correspondence, with no degree≥2 hypothesis in the source.

**Report correspondence.** report.tex Sections 1-4 match the Lean construction (tropicalize, val, tropicalMap formula, iteratedPolynomial, tropicalIteratedMap, field_no_periodic, periodic_correspondence_false). PDF text matches. No stronger prose claim.

## Disposition

APPROVED — merged as PR 1164. The submission gives a complete, formalised disproof of conjecture 00000002698.
