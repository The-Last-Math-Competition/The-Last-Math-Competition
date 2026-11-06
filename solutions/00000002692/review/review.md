# Solution Review — Conjecture 00000002692 (PR 1162)

**Submission:** lizaixi01 — `lizaixi01_submission_20261023185251`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000002692; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.33.0` and Mathlib revision `db584cd6d46c92f209a44c0f1c829460d327499d`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** For a p-adic contraction with an attracting basin, the basin measure is an explicit fraction of the ball volume (with denominator the order of the multiplier mod p), and the basin boundary is the closure of the periodic points. The source states no connectedness, invertibility, or unit-multiplier hypothesis.

**Decisive results.** f(x)=5x on Z5 (and Q5) is a genuine strict contraction: |5|_5=1/5<1 and |f(x)-f(y)|_5=(1/5)|x-y|_5. Its convergence basin at 0 is the whole space (all orbits 5^n x→0), its periodic set is exactly {0} (5^n x=x forces x=0), the frontier of the whole space is empty, while the closure of {0} is {0}. Hence the boundary conjunct of the conjecture is false; Lean's `no_universal_boundary_law` negates the corresponding universal statement over all contractions fixing 0. The example satisfies the literal 'p-adic contraction' hypothesis, and the measure clause need not be addressed because the conjecture is a conjunction.

**Report correspondence.** report.tex Sections 1-4 match the Lean objects (Padic 5/PadicInt 5, mulMap 5, basin, periodicPts, frontier, unit-ball image, measure lemma). The report also fully explains the earlier closed PR 276 and its arithmetic-only defect. PDF text matches. No stronger prose claim.

## Disposition

APPROVED — merged as PR 1162. The submission gives a complete, formalised disproof of conjecture 00000002692.
