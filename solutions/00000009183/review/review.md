# Solution Review — Conjecture 00000009183 (PR 1081)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261022101706`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000009183; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.19.0` and Mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** Definition: First-order limits of dense graphs. Conjecture: The dense-side limit: the limit objects of graph sequences, with the characterization of the objects graphons. (dense graph graphon first-order limit) 定义：密集图的一阶极限。猜想：密集侧的极限：图序列的极限对象且象的刻画为 graphon。（密集图 graphon 一阶极限图序列极限对象刻画侧）

**Decisive results.** The complete graphs and the complete graphs with one edge deleted converge to the same constant-one graphon but have different limiting first-order theories. The sentence asserting completeness separates every pair. The paper proves that both sequences are first-order convergent. Interpretation: the source explicitly says first-order limits in English and Chinese. We refute the necessary claim that the graphon limit determines first-order limiting truth values. Ordinary graphon characterization of homomorphism-density convergence remains valid. Lean uses standard `SimpleGraph`, actual adjacency kernels, all fractional rectangle weights, their uniform error bound and its genuine real limit, and proves `¬ GraphonDeterminesCompleteness`. The identification of step integrals with finite sums and the full first-order convergence proof are paper-only and explicitly marked. No generic first-ord The decisive Lean declaration is `conjecture9183_false`, whose statement is: ¬ GraphonDeterminesCompleteness := by. Read against the filed statement, this establishes the negation of the printed clause identified in the README.

**Report correspondence.** The report, README and Lean sources were read. The report states the same construction and the same decisive conclusion; the Lean declaration matches the report's main theorem. The LaTeX source recompiled cleanly, and the build log reports only propext, Classical.choice and Quot.sound.

## Disposition

APPROVED — merged as PR 1081. The submission gives a complete, formalised disproof of conjecture 00000009183.
