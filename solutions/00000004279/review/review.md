# Solution Review — Conjecture 00000004279 (PR 1139)

**Submission:** lizaixi01 — `lizaixi01_submission_20261023041703`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000004279; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.33.0` and Mathlib revision `db584cd6d46c92f209a44c0f1c829460d327499d`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** Literal: 'Rank-3 Butler groups are completely classified ... and the quotient space is finite up to isomorphism.' The submission reads the finite-quotient clause as: there are only finitely many isomorphism classes of rank-3 Butler groups (the data/GL quotient is the isomorphism-class set).

**Decisive results.** The submission constructs G_p = (Z[1/p])^3 = (⨁_{i∈Fin 3} Z[1/p]) for every prime p. Lean proves the actual localization Z[1/p] has Z-rank 1 and is torsion-free, that G_p has Z-rank 3 and is torsion-free, and that the top submodule of the finite direct sum is pure and linearly isomorphic to G_p. Thus every G_p is literally a rank-3 Butler group. Lean then proves p is surjective on G_p and every q≠p is not surjective on G_p, so the additive groups G_p and G_q are non-isomorphic for p≠q. The quotient by actual additive isomorphism is therefore infinite, and no finite complete labelling exists. This is a direct negation of the source's finite-quotient necessary clause; the hypotheses are satisfiable and the conclusion is not assumed.

**Report correspondence.** The report says the G_p are rank-three Butler groups, pairwise non-isomorphic, and that the actual isomorphism quotient is infinite. Lean proves exactly family_qualifies, pairwise_nonisomorphic, prime_class_injective, infinite_actual_isomorphism_quotient, and no_finite_classification. The report does not claim the separate two-component classification or GL-action clause, and explicitly disclaims variants with fixed rank-one types; no stronger prose claim than Lean.

## Disposition

APPROVED — merged as PR 1139. The submission gives a complete, formalised disproof of conjecture 00000004279.
