# Solution Review — Conjecture 00000006291 (PR 1106)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261022113544`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000006291; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.19.0` and Mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** The filed statement says the zeroth group is a complete invariant of regular rings, the classification is by ordered groups of continuous geometry, and the dimension function is the coordinate lattice. I read 'regular ring' as unital von Neumann regular (forall a, exists b, a*b*a=a), 'zeroth group' as the algebraic K_0 of finitely generated projective modules with its positive cone and order unit [R], and 'complete invariant' as implying that isomorphic scaled ordered K_0 groups force ring isomorphism.

**Decisive results.** Lean constructs K_0 from actual finite-dimensional vector spaces and linear equivalences, proves the stabilized relation, the group operations, the rank isomorphism to Z, the universal group-completion property, the positive cone, the order unit, and that every field has scaled ordered K_0 isomorphic to (Z, Z_{>=0}, 1). It then proves F_2 and F_3 are von Neumann regular, have isomorphic scaled ordered K_0 groups, and are not isomorphic as rings. Thus the completeness assertion fails already for regular fields, which are a subclass of regular rings. The counterexample is universal: it refutes the source's complete-invariant claim, even with the positive cone and unit retained.

**Report correspondence.** The report's Theorem 1 and its K_0 computation match `fields_same_scaled_ordered_K0`, `finite_fields_witness`, and `conjecture_6291_false`. The report explicitly says the Lean theorem is a necessary restriction to fields, which is enough to refute the source's universal claim; the remaining continuous-geometry clauses are not needed once completeness fails.

## Disposition

APPROVED — merged as PR 1106. The submission gives a complete, formalised disproof of conjecture 00000006291.
