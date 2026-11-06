# Solution Review — Conjecture 00000002894 (PR 1127)

**Submission:** lizaixi01 — `lizaixi01_submission_20261023013015`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000002894; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.33.0` and Mathlib revision `db584cd6d46c92f209a44c0f1c829460d327499d`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** The filed statement says every nontrivial inclusion-minimal blocking set in a projective plane of order q² is of Rédei type, and non-Rédei ones exist only when q is a square. The submission takes the literal English reading: 'minimal' is inclusion-minimal, the plane order is Q=q², and Rédei type means the standard necessary condition that some line ℓ has |B\ℓ|=Q. No smallness hypothesis is added.

**Decisive results.** For Q=9=3², the vertexless triangle B={[0:1:t],[t:0:1],[1:t:0]:t∈F9^×} has 24 points. Lean proves B is blocking, inclusion-minimal (each point has a tangent meeting B only there), nontrivial, and ¬IsRedei: for every nonzero linear form a, |B\line a| ≥ 3(9−1)−(9+1)=14>9, so no line has the required complement size 9. This is a genuine member of the stated class (plane order q², q=3 non-square, nontrivial minimal, non-Rédei) and directly falsifies both the universal Rédei assertion and the square-q restriction. The hypotheses are satisfiable and the conclusion is the negation of the filed universal claim.

**Report correspondence.** The report/PDF state exactly the same literal reading (inclusion-minimal, no smallness), the same 24-point set, the tangent/minimality argument, the line-complement bound 14>9, and the same Lean theorem. No stronger prose claim; the only cited external facts are the standard Rédei definition and line cardinality.

## Disposition

APPROVED — merged as PR 1127. The submission gives a complete, formalised disproof of conjecture 00000002894.
