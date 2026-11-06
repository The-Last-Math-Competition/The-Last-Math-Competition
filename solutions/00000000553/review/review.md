# Solution Review — Conjecture 00000000553 (PR 1181)

**Submission:** lizaixi01 — `lizaixi01_submission_20261024075952`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000000553; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.33.0` and Mathlib revision `db584cd6d46c92f209a44c0f1c829460d327499d`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** Literal reading: for the algebra Λ=Q×Q of rank 2 (two simple modules), the number of complete exceptional sequences in mod Λ (up to componentwise isomorphism) equals the number of ordinary positive rational points of the associated coefficient-free cluster A-variety. The filed text does not require connectedness.

**Decisive results.** The theorem negates the asserted equality. It proves the actual algebra Λ=Q×Q has rank 2, classifies its simple modules, shows all modules are projective and all Ext^1 vanish, and proves the complete-sequence isomorphism quotient is finite and nonempty. The associated zero exchange matrix gives mutation μ_k(x)=2/x_k; the positive atlas is constructed with actual transition maps, each chart is bijective onto the global positive set, and an injective family (n+1,1) shows the global positive set is infinite. A finite set cannot be in bijection with an infinite one, so the claimed equality fails.

**Report correspondence.** Report and Lean agree: both use Λ=Q×Q, the zero exchange matrix, the 2/x mutations, the positive-atlas gluing, and the finite-versus-infinite contradiction. The report explicitly says it does not challenge ordinary finite cluster-tilting correspondences or counts of clusters/tropical points; no stronger claim is made.

## Disposition

APPROVED — merged as PR 1181. The submission gives a complete, formalised disproof of conjecture 00000000553.
