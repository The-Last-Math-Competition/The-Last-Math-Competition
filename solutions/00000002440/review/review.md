# Solution Review — Conjecture 00000002440 (PR 1108)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261022114059`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000002440; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.19.0` and Mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** The filed statement is an existence claim: some smooth variety X has finite etale pi_1 and nonabelian etale pi_3, with an Enriques-type construction. The submission reads 'nonabelian' as internal noncommutativity of the actual group/pro-group and proves the universal obstruction for every pointed topological space. The etale homotopy type is identified levelwise with actual spaces using the standard Artin-Mazur-Friedlander construction.

**Decisive results.** For every BasedSpace X, Pi3 X is Mathlib's actual HomotopyGroup.Pi 3 and is abelian by the Eckmann-Hilton instance; moreover every diagram of such groups factors through CommGrp via abelian_factorization. Since each level of the etale pi_3 pro-group is pi_3 of a level space, the pro-group is pro-abelian. Hence no smooth variety can have internally nonabelian pi_3, which is the negation of the filed existential. The theorem is universal, the hypotheses are satisfiable, and no commutativity hypothesis is assumed.

**Report correspondence.** The report states the same universal topological obstruction, the abelian-valued diagram factorization, and the conclusion that the required variety cannot exist. It explicitly marks schemes, the etale type functor, geometric realization and the induced-map functor as standard mathematical bridges outside Lean; no hidden stronger formal claim is made.

## Disposition

APPROVED — merged as PR 1108. The submission gives a complete, formalised disproof of conjecture 00000002440.
