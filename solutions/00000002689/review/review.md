# Solution Review — Conjecture 00000002689 (PR 1171)

**Submission:** lizaixi01 — `lizaixi01_submission_20261024032939`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000002689; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.33.0` and Mathlib revision `db584cd6d46c92f209a44c0f1c829460d327499d`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** Literal reading of 'mean height of orbits': the ordinary Cesaro mean (1/n)∑_{k<n} h(f^k(x)) of the naive logarithmic (or multiplicative) height along the forward orbit. The definition in the source explicitly mentions naive heights; I therefore do not normalize by the degree d^k.

**Decisive results.** The theorem negates the claimed finite mean-height limit for the actual nonpreperiodic orbit of 2 under f(z)=z^2. It proves the canonical height of 2 is log 2, while meanHeight n = ((2^n-1)/n) log 2 tends to +∞ and meanMultiplicativeHeight also tends to +∞; both therefore have no finite limit, so neither the asserted linear combination of canonical heights nor the 1/log n rate can hold. The orbit is genuinely outside the preperiodic set (strictly increasing iterates) and all objects are actual heights, so the hypotheses are satisfiable.

**Report correspondence.** Report and Lean agree: both use the ordinary unnormalized arithmetic mean, prove divergence to +∞, and prove nonconvergence to every real L. The report explicitly says it does not address a degree-normalized averaging statement; no stronger claim is made.

## Disposition

APPROVED — merged as PR 1171. The submission gives a complete, formalised disproof of conjecture 00000002689.
