# Solution Review — Conjecture 00000003161 (PR 1128)

**Submission:** lizaixi01 — `lizaixi01_submission_20261023013917`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000003161; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.33.0` and Mathlib revision `db584cd6d46c92f209a44c0f1c829460d327499d`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** The filed statement says the minimal number m of measurements for recovery of k-sparse signals in y=Ax satisfies m ≥ C·k·log(n/k) uniformly, with C a positive dimension-independent constant. The submission takes the literal exact real-arithmetic model: A is any real m×n matrix and D any total decoder with D(Ax)=x for every k-sparse x; no noise, stability, precision or decoder restriction is added.

**Decisive results.** For k=1 and ambient dimension N=n+3, Lean uses the actual 2×N matrix A with rows (1,…,1) and (0,1,…,N−1). It proves the measurement map is injective on all one-sparse signals (including zero), constructs a total decoder, and defines minimalMeasurements via Nat.find on the genuine existence of a successful matrix/decoder. For every C>0 it produces n with minimalMeasurements n ≤ 2 < C·1·log((n+3)/1). This is the negation of the universal lower bound at k=1 in the regime N→∞; the hypotheses are satisfiable and the bound is actually violated, not merely a different arithmetic fact.

**Report correspondence.** The report/PDF state the same exact-recovery model, the same 2×N matrix, the total decoder and the same quantifier over every C>0; the Lean theorem matches. The report explicitly says it does not refute stable/noisy/finite-precision lower bounds with additional assumptions.

## Disposition

APPROVED — merged as PR 1128. The submission gives a complete, formalised disproof of conjecture 00000003161.
