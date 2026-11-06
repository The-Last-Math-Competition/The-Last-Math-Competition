# Solution Review — Conjecture 00000001520 (PR 1190)

**Submission:** lizaixi01 — `lizaixi01_submission_20261024155054`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000001520; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.33.0` and Mathlib revision `db584cd6d46c92f209a44c0f1c829460d327499d`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** Literal unrestricted vanishing clause: every Gromov-hyperbolic group Γ has Wh(Γ) = 0; the parenthetical '(torsion-free and trivial)' describes Wh(Γ), and no torsion-freeness is imposed on Γ. Take Γ = C5.

**Decisive results.** The theorem constructs the actual group ring Z[C5], the stable GL colimit and K1, the Whitehead quotient by the signed group units, and the genuine unit u = 1 - t - t^{-1} with inverse 1 - t^2 - t^3. The determinant detector sends u to a nontrivial coset in A^×/T because u has two distinct coefficients and is not a signed group unit, so u has nonidentity Whitehead class. The same group C5 is finite, hence hyperbolic: the Cayley graph with S = C5 \ {1} is complete, the word metric is 0/1, left-invariant, and satisfies the four-point inequality with δ = 1. Thus a hyperbolic group with nonzero Wh exists and the universal vanishing clause is false. The hypotheses are satisfiable and the conclusion is a concrete counterexample.

**Report correspondence.** The report states the same C5 example, the same unit, the same determinant detection, and the same finite-group four-point argument; it explicitly excludes the torsion-free-Γ revision and the later clauses. Lean and report agree.

## Disposition

APPROVED — merged as PR 1190. The submission gives a complete, formalised disproof of conjecture 00000001520.
