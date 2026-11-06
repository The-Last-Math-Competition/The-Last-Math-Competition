# Solution Review — Conjecture 00000001876 (PR 1156)

**Submission:** lizaixi01 — `lizaixi01_submission_20261023092539`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000001876; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.33.0` and Mathlib revision `db584cd6d46c92f209a44c0f1c829460d327499d`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** The source defines a dp-minimal group as a definable group of dp-rank ≤1 in a dependent theory and asserts that all such groups are solvable, with no infinitude or connectedness restriction. The submission takes the literal unrestricted definition, so the finite group S5 is allowed.

**Decisive results.** G = S5 = Perm(Fin 5) is realized as an actual first-order structure with identity, inverse and multiplication, expanded by constants for all its elements. T = Th_L(G) is complete; a finite disjunction sentence in T forces every model to be finite, so every model is NIP and satisfies the standard two-formula ICT criterion for dp-minimality (an infinite IP or ICT pattern would inject ℕ into a finite tuple domain). Thus T is dependent and dp-minimal and G is a definable group of dp-rank ≤1. Mathlib's `Equiv.Perm.not_isSolvable_fin_5` gives ¬Group.IsSolvable G. Hence the universal 'all are solvable' clause is false. The finite-group example is admitted by the literal definition; the report explicitly does not claim to refute an infinite-only or virtually-solvable classification.

**Report correspondence.** The report and Lean agree: the report states the language with constants, the complete theory, the finite-cover sentence, the all-arity IP and ICT pattern definitions, the finite-model dp-minimality, and the actual nonsolvability of S5. `every_model_finite`, `finite_model_dependent`, `finite_model_dpMinimal`, `theory_dependent`, `theory_dpMinimal` and `actual_counterexample` formalize those claims. No stronger prose claim is made.

## Disposition

APPROVED — merged as PR 1156. The submission gives a complete, formalised disproof of conjecture 00000001876.
