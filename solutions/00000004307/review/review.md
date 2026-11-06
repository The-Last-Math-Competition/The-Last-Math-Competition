# Solution Review — Conjecture 00000004307 (PR 1146)

**Submission:** lizaixi01 — `lizaixi01_submission_20261023055756`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000004307; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.33.0` and Mathlib revision `db584cd6d46c92f209a44c0f1c829460d327499d`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** Literal: the same minimal Euler-system rank is 2k−1, and when k is coprime to p−1 the rank is exactly 1. The submission reads this as a conjunction about one rank function, with the legitimate parameters k=3 and p=5 (k>0, p odd prime, k≤p−2, gcd(3,4)=1).

**Decisive results.** Lean proves k=3,p=5 is legal and coprime. At those parameters the first clause requires rank=2·3−1=5 and the second requires rank=1. In any characteristic-zero semiring 5≠1, so no value r can satisfy both. Lean then quantifies over every rank function ℕ→ℕ→R and proves no function satisfies both GeneralNumericalClause and CoprimeNumericalClause; it also proves the unrestricted formula negation and the fixed-p=5 negation, plus natural, integer and cardinal specializations. The source's conjunction is therefore logically inconsistent; the witness parameters are satisfiable and no actual rank value is assumed.

**Report correspondence.** The report matches Lean: legal_witness, pointwise_obstruction, no_candidate_rank_function, unrestricted_formulas_impossible, fixed_odd_prime_impossible, and the natural/integer/cardinal specializations. The report explicitly says it does not compute an actual Euler-system or higher-K-group rank and does not refute a corrected piecewise reading. No stronger prose claim.

## Disposition

APPROVED — merged as PR 1146. The submission gives a complete, formalised disproof of conjecture 00000004307.
