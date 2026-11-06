# Solution Review — Conjecture 00000000742 (PR 1120)

**Submission:** lizaixi01 — `lizaixi01_submission_20261022231421`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000000742; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.33.0` and Mathlib revision `db584cd6d46c92f209a44c0f1c829460d327499d`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** The filed statement says the number of minimal decompositions/minimal dynamical systems of 1-Lipschitz maps f:Z_p→Z_p is p^{p-1}, with 'a count of minimal maps'. The submission takes p=2 and checks both the minimal-component count and the count of distinct minimal maps.

**Decisive results.** The odometer T(x)=x+1 is 1-Lipschitz and every forward orbit is dense in Z_2, so the only nonempty closed minimal invariant subset is Z_2; minimal_component_count proves the count is 1, while p^{p-1}=2. Also T_a(x)=x+a for a=1,3,5 are three distinct minimal 1-Lipschitz maps, so there are at least 3 minimal maps; not_exactly_two_minimal_maps proves no bijection with Fin 2. Both natural readings are refuted. The hypotheses are satisfiable and the conclusion is the negation of the claimed count.

**Report correspondence.** The report states the same two readings and the same examples; the Lean theorems match. No stronger prose claim.

## Disposition

APPROVED — merged as PR 1120. The submission gives a complete, formalised proof of conjecture 00000000742.
