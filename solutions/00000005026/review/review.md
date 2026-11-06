# Solution Review — Conjecture 00000005026 (PR 1148)

**Submission:** lizaixi01 — `lizaixi01_submission_20261023062015`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000005026; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.33.0` and Mathlib revision `db584cd6d46c92f209a44c0f1c829460d327499d`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** Literal: a universal sentence is (by the source's stated definition, also explicit in the Chinese) a sentence that characterizes a unique structure up to isomorphism; the conjecture asserts that four variables is the lower bound. The submission reads this in the empty first-order language with equality, targets the singleton structure Unit, and measures variables by the maximum allocated bound-variable context width (and separately by the number of quantifier constructors).

**Decisive results.** Lean defines φ = ∃x∀y(y=x) in the empty language with equality. It proves the actual AST uses the two Fin 2 bound variables, binderCount φ=2 and contextWidth φ=2, and proves the realization equivalence M⊨φ ↔ ∃x∈M, ∀y∈M, y=x. Unit is a model, the empty type is not, and every model of φ is genuinely L-isomorphic to Unit; any two models are L-isomorphic. Hence a two-variable sentence characterizes the singleton up to isomorphism, so the asserted global lower bound of four variables is false. The counterexample satisfies the source's custom definition of 'universal sentence'; the lower-bound clause is negated. The report also handles the syntactically universal variant ∀x∀y(y=x) under the nonempty-model convention.

**Report correspondence.** The report matches Lean: equalityBody, singletonSentence, singleton_realize, singleton_iff_actual_model_iso, actual_two_variable_counterexample and no_global_four_variable_lower_bound. The report explicitly notes that contextWidth is a sufficient two-variable certificate, not a general identity with every minimal reusable-variable notion, and that the main witness is existential rather than syntactically ∀-quantified. No stronger prose claim.

## Disposition

APPROVED — merged as PR 1148. The submission gives a complete, formalised disproof of conjecture 00000005026.
