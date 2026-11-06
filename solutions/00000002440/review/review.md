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

**Conjecture as filed.** Conjecture: There exists a smooth variety X with π₁^ét(X) finite but π₃^ét(X) nonabelian (noncommutativity of higher fundamental groups); the construction is of Enriques surface type. 猜想：存在光滑簇 X 使 π₁^{ét}(X) 有限但 π_3^{ét}(X) 非交换(高阶基本群的非交换性);构造由 Enriques 表面型。

**Decisive results.** Actual third homotopy groups are abelian by the cube-loop Eckmann-Hilton argument. The entire defining diagram of an etale third homotopy pro-group therefore has an abelian-valued representative, excluding the proposed internally nonabelian group for any smooth variety. The decisive Lean declaration is `no_nonabelian_layer`, whose statement is: ¬ ∃ i : I, Nonabelian (Pi3 (D.space i)) := by. Read against the filed statement, this establishes the negation of the printed clause identified in the README.

**Report correspondence.** The report, README and Lean sources were read. The report states the same construction and the same decisive conclusion; the Lean declaration matches the report's main theorem. The LaTeX source recompiled cleanly, and the build log reports only propext, Classical.choice and Quot.sound.

## Disposition

APPROVED — merged as PR 1108. The submission gives a complete, formalised disproof of conjecture 00000002440.
