# Solution Review — Conjecture 00000009926 (PR 1158)

**Submission:** lizaixi01 — `lizaixi01_submission_20261023122452`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000009926; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.33.0` and Mathlib revision `db584cd6d46c92f209a44c0f1c829460d327499d`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** The source asserts that any family of two invariants on two-parameter persistence modules fails to separate some nonisomorphic pair, hence at least three invariants are needed. The submission takes 'invariant' literally, with no numerical, computability or locality restriction, and 'two-parameter' as the actual functor categories over ℕ² and ℝ².

**Decisive results.** Persistence modules are actual functors J→ModuleCat ℚ, and the natural-isomorphism-class invariant I = toSkeleton is complete because `toSkeleton_eq_toSkeleton_iff` gives I(M)=I(N) ↔ M≅N. The distinct constant invariant K = class(zeroModule) is also an invariant, and a linear-equivalence component argument proves the zero and one constant modules are nonisomorphic, so the Finset {I,K} has cardinality 2. If both invariants agree on M,N, then I(M)=I(N), hence M≅N; so this two-invariant family is complete. `twoFamily_card`, `twoFamily_invariant`, `twoFamily_complete` and `no_two_invariant_lower_bound` formalize the claim, and `pfd_no_two_invariant_lower_bound`, `discrete_two_parameter_counterexample` and `real_two_parameter_counterexample` cover the pointwise-finite subcategory and both indexing categories.

**Report correspondence.** The report and Lean agree: the report states the functor model, Skeleton quotient bridge, zero/one constant modules, distinct invariants, Finset cardinality 2, completeness, and the negation of the two-invariant lower bound. `class_eq_iff`, `zero_not_iso_one`, `invariants_distinct`, `twoFamily_card`, `twoFamily_complete` and `no_two_invariant_lower_bound` formalize those claims. The report explicitly says the invariants are noncomputable isomorphism-class-valued and that no numerical/computable local classification is claimed.

## Disposition

APPROVED — merged as PR 1158. The submission gives a complete, formalised disproof of conjecture 00000009926.
