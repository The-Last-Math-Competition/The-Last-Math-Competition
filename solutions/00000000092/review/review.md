# Solution Review — Conjecture 00000000092 (PR 1180)

**Submission:** lizaixi01 — `lizaixi01_submission_20261024071821`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000000092; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.33.0` and Mathlib revision `db584cd6d46c92f209a44c0f1c829460d327499d`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** Literal reading: with q=2 fixed (A=F_2[T], K=F_2(T)) and rank r=1 fixed, there is a single finite bound depending only on r and q that bounds the torsion of every rank-one Drinfeld module in the setting. The filed text states no degree or fixed-field restriction, so varying finite extensions of K is allowed.

**Decisive results.** The theorem negates the claimed uniform bound. For each n it constructs the rank-one Carlitz module φ_T(x)=x^2+θx over the finite splitting field L_n of P_n, proves P_n has degree 2^n and is separable with exactly 2^n roots in L_n, and injects those roots into the native A-torsion submodule. Hence the torsion cardinality is at least 2^n for every n, so no single B bounds all n; taking n=B gives 2^B≤B, impossible. All Drinfeld-module axioms, rank, generic characteristic and torsion membership are proved from actual objects.

**Report correspondence.** Report and Lean agree: both construct the Carlitz module over the splitting fields, prove the exact 2^n root count and the torsion injection, and conclude no bound depending only on r=1,q=2 exists. The report explicitly says it does not refute fixed-degree or fixed-field formulations; no stronger claim is made.

## Disposition

APPROVED — merged as PR 1180. The submission gives a complete, formalised disproof of conjecture 00000000092.
