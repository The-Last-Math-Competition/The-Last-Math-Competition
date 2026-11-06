# Solution Review — Conjecture 00000004263 (PR 1206)

**Submission:** Galaxy-0 — `Galaxy-0_submission_20261025195400`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000004263; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.31.0`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** The filed clause says the minimal dimension for solving the F matrices is 3. The submission reads this as a lower bound on the fusion-space/matrix dimension (and notes category rank/global dimension is also 1), using Vec_C, the fusion category of finite-dimensional complex vector spaces, whose unique simple object is the unit.

**Decisive results.** Vec_C is a rigid fusion category with one simple object; in the unique fusion channel the associator sends the left triple-product basis element to the right one with coefficient 1, so F=(1), a 1×1 invertible matrix satisfying the pentagon, and the snake equations hold. Thus there is a one-dimensional F-matrix solution, contradicting the claimed minimum 3. The conclusion is the negation of the lower-bound clause; the Brauer-recursion clause is not needed.

**Report correspondence.** Report and Lean agree on the coordinate reassociation, the 1×1 matrix [1], the pentagon, and the dimension inequality. The report explicitly says the Lean does not construct the abstract fusion category Vec or general rigidity; those are prose, and the formal part checks the coordinate/matrix core.

## Disposition

APPROVED — merged as PR 1206. The submission gives a complete, formalised disproof of conjecture 00000004263.
