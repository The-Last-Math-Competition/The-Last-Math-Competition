# Solution Review — Conjecture 00000000721 (PR 1122)

**Submission:** lizaixi01 — `lizaixi01_submission_20261022233139`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000000721; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.33.0` and Mathlib revision `db584cd6d46c92f209a44c0f1c829460d327499d`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** The filed statement uses the literal negative factorial exponent p^{-n!} and claims the value set contains a subfamily of cardinality 2^{aleph0} algebraically independent over Q̄. The submission takes p=2 and considers convergent series in PadicAlgCl 2.

**Decisive results.** At p=2, a nonzero digit gives |2^{-n!}|_2=2^{n!}≥1. Convergence forces the terms to tend to 0, hence all sufficiently late digits vanish; every value is a finite rational sum and the value set is countable. no_continuum_subfamily proves no subset of the value set has cardinality 2^{aleph0}, which directly negates the existence claim. The hypotheses are satisfiable (p=2, convergent series).

**Report correspondence.** The report states the same negative-exponent reading, the finite-support argument, and the countability conclusion; the Lean theorem matches. No stronger prose claim.

## Disposition

APPROVED — merged as PR 1122. The submission gives a complete, formalised disproof of conjecture 00000000721.
