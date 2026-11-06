# Solution Review — Conjecture 00000002783 (PR 1129)

**Submission:** lizaixi01 — `lizaixi01_submission_20261023015836`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000002783; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.33.0` and Mathlib revision `db584cd6d46c92f209a44c0f1c829460d327499d`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** The filed statement claims d(X,Y)≤√n for all n-dimensional pairs, with equality only for the ℓ1^n–ℓ∞^n pair. The submission uses the standard multiplicative Banach–Mazur distance d(X,Y)=inf_T ‖T‖‖T⁻¹‖ over invertible linear maps, and takes the 2-dimensional pair E=ℓ2², S=ℓ∞².

**Decisive results.** Lean defines distortion over all actual continuous linear equivalences E≃L S, proves the universal lower bound √2≤distortion T via the parallelogram identity, proves the coordinate equivalence attains √2, and proves √2 is the least element of the range, so bmDistance=√2. It also proves E is not isometric to L1=ℓ1² or to S=ℓ∞² (parallelogram contradictions). Hence (E,S) is a 2-dimensional equality pair d=√2=√n that is not the named ℓ1²–ℓ∞² pair in either order (NamedPair is false). This directly negates the 'equality only for' clause at n=2; the hypotheses are satisfiable.

**Report correspondence.** The report/PDF state the same standard multiplicative distance, the same E,S, the √2 lower bound and attainment, and the same exclusion of both named isometry classes; the Lean theorems match. The report explicitly discloses that the source's isometric-embedding wording is imprecise and that the second-extremal-value clause is not addressed.

## Disposition

APPROVED — merged as PR 1129. The submission gives a complete, formalised disproof of conjecture 00000002783.
