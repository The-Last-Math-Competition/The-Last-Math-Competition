# Solution Review — Conjecture 00000001670 (PR 1130)

**Submission:** lizaixi01 — `lizaixi01_submission_20261023022548`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000001670; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.33.0` and Mathlib revision `db584cd6d46c92f209a44c0f1c829460d327499d`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** The filed statement prints the same constant P3 both as 0.918=459/500 and as the closed form (2/π)arctan(√2), and separately asserts the M_d asymptotic. The submission reads the printed numerical equalities as an explicit necessary conjunction and refutes it, allowing both exact equality and the generous three-decimal rounding interval |P−459/500|≤1/2000.

**Decisive results.** Lean defines closedForm=(2/Real.pi)*Real.arctan(Real.sqrt 2) using Mathlib's actual real sqrt, arctan and pi. It proves √2<√3, arctan(√2)<π/3, hence closedForm<2/3, then 459/500−closedForm>1/4. It also proves any P in the rounding interval satisfies P≥367/400, so P−closedForm>1/4. Therefore no real P can satisfy both printed characterizations, exactly or rounded. This is the direct negation of the explicit numerical conjunction in the filed statement; the hypotheses are trivially satisfiable and the conclusion is a universal negation over all real P and all sequences P:N→R.

**Report correspondence.** The report/PDF state the same exact and rounded readings, the same strict analytic inequalities, and the same universal/sequence negations; the Lean theorems match. No stronger prose claim; the report explicitly says it does not assume a graph limit or identify the genuine DMS constant.

## Disposition

APPROVED — merged as PR 1130. The submission gives a complete, formalised disproof of conjecture 00000001670.
