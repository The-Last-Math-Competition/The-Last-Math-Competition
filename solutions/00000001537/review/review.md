# Solution Review — Conjecture 00000001537 (PR 1182)

**Submission:** lizaixi01 — `lizaixi01_submission_20261024085149`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000001537; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.33.0` and Mathlib revision `db584cd6d46c92f209a44c0f1c829460d327499d`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** Ordinary integral cyclic cohomology HC^n(R) of R = Z[X]/(X^2), n ≥ 0, in the standard normalized (b*,B*) total cochain model; 'period 2' is read as at least an additive isomorphism HC^0(R) ≃ HC^2(R) with the printed two-point coefficient groups.

**Decisive results.** The theorem proves the literal negation of the period-two claim: HC^0(R) is torsion-free (x + x = 0 implies x = 0), while HC^2(R) contains a nonzero 2-torsion class; hence there is no additive-group isomorphism HC^0(R) ≃ HC^2(R). The Lean constructs the actual AdjoinRoot(X^2), all normalized source cochains, the genuine b*/B* differential, the native total complex and its homology, and transports the calculation to the source algebra. The hypotheses are satisfiable and the conclusion is a universal obstruction, not a numerical special case. The comparison of the normalized model with the standard cyclic complex is the cited Loday 2.4.3 identification.

**Report correspondence.** The report's final display (∀x∈HC^0, x+x=0 ⇒ x=0; ∃y∈HC^2, y≠0 and y+y=0; no additive equivalence) matches the Lean capstone and its supporting theorems. The report explicitly excludes HP, rational coefficients and eventual periodicity; it does not claim a stronger statement.

## Disposition

APPROVED — merged as PR 1182. The submission gives a complete, formalised disproof of conjecture 00000001537.
