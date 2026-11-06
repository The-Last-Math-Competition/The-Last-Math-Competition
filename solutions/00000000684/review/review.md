# Solution Review — Conjecture 00000000684 (PR 1140)

**Submission:** lizaixi01 — `lizaixi01_submission_20261023042705`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000000684; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.33.0` and Mathlib revision `db584cd6d46c92f209a44c0f1c829460d327499d`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** Literal iff: 'The group is finitely generated and infinite if and only if the knot is non-classical; and the criterion's combination is the Gauss diagram.' The submission reads this in the standard Kauffman Wirtinger virtual-group model and takes the ordinary round unknot, a crossing-free classical diagram, as the counterexample. ClassicalRealization is a sufficient certificate of an actual planar embedding (zero height) of the diagram, not a definition of non-classicality for arbitrary virtual diagrams.

**Decisive results.** For the crossing-free round diagram, Lean defines arcs as the genuine connected components of the circle minus the actual double-point set, proves the double-point and crossing sets are empty, defines the PresentedGroup on the one arc and empty relator set, and proves it is group-isomorphic to Multiplicative ℤ. Hence the group is finitely generated and infinite. Lean also constructs the actual spatial embedding z↦(f(z),0) and proves it projects to the diagram, so the round diagram has a genuine classical realization. Applying the proposed iff to this classical unknot gives a true left side and a false right side, so the forward implication and the iff both fail. The counterexample is inside the filed domain (a virtual diagram), satisfies the literal hypotheses, and negates the universal claim. The Lean theorem is restricted to crossing-free diagrams, but that is a nonempty subclass, sufficient to refute the universal iff.

**Report correspondence.** The report matches Lean: it explicitly works in the standard Kauffman Wirtinger model, states that the round unknot is classical with group Z, and proves the negations of both the restricted iff and its necessary implication. It explicitly disclaims a general virtual-knot classification, Reidemeister invariance, and a complement fundamental-group identification. No stronger prose claim than the formal statements.

## Disposition

APPROVED — merged as PR 1140. The submission gives a complete, formalised disproof of conjecture 00000000684.
