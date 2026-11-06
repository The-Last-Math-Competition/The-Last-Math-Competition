# Solution Review — Conjecture 00000009783 (PR 1114)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261022115619`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000009783; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.19.0` and Mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** Definition: Ideal lattices of AF algebras: combinatorial realizations by Bratteli diagrams. Conjecture: The closed ideal lattice of an AF algebra is isomorphic to the hereditary-subset lattice of its Bratteli diagram; the isomorphism preserves stratification of dimension vectors, and the length of maximal ideal chains equals the supremum of path depths of the diagram. (AF ideal lattice combinatorial realization) 定义：AF 代数的理想格：Bratteli 图的组合实现。猜想：AF 代数的闭理想格与 Bratteli 图的遗传子集格同构；同构保持维数向量的层化且极大理想链的长度等于图的路径深度上确界。（AF 理想格组合实现）

**Decisive results.** The actual AF algebra C has only the closed ideals zero and C. Its unique maximal ideal chain has one strict inclusion or two elements. The standard constant identity system C=M_1(C) at every stage has a Bratteli ray, with one vertex per level and one edge between neighboring levels. There is a genuine path of length N for every natural N, so the supremum of depths is infinite. This contradicts the source's chain-depth equality under both chain-length conventions. The decisive Lean declaration is `conjecture_9783_false`, whose statement is: ¬ OneBlockDepthClause. Read against the filed statement, this establishes the negation of the printed clause identified in the README.

**Report correspondence.** The report, README and Lean sources were read. The report states the same construction and the same decisive conclusion; the Lean declaration matches the report's main theorem. The LaTeX source recompiled cleanly, and the build log reports only propext, Classical.choice and Quot.sound.

## Disposition

APPROVED — merged as PR 1114. The submission gives a complete, formalised disproof of conjecture 00000009783.
