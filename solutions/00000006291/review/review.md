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

**Conjecture as filed.** Definition: A regular ring is one where element equations are always solvable. Conjecture: The zeroth group is a complete invariant; the classification is given by the ordered groups of continuous geometry; and the dimension function of the ordered group is the coordinate lattice of continuous geometry. (complete ordered-group zeroth classification of regular rings) 定义：正则环为元素方程恒可解的环。猜想：零阶群为完备不变量；且分类由连续几何的有序群给出；且有序群的维数函数为连续几何的坐标格。（正则环零阶有序群完备）

**Decisive results.** The fields F₂ and F₃ are nonisomorphic von Neumann regular rings, yet both scaled ordered Grothendieck groups are (Z, Z≥0, 1). This refutes the source's claim that the zeroth group is a complete invariant of regular rings. The positive cone and order unit are retained, so the example also works when the proposed invariant is stronger than the abstract abelian group. `SOURCE.md` is the exact bilingual source at upstream commit `b355e42906e6eaf52bc7e9d005e0ef02d8aa7400`. The current snapshot has no prior PR or solution for this conjecture. The decisive Lean declaration is `conjecture_6291_false`, whose statement is: ¬ FieldCompleteness := by. Read against the filed statement, this establishes the negation of the printed clause identified in the README.

**Report correspondence.** The report, README and Lean sources were read. The report states the same construction and the same decisive conclusion; the Lean declaration matches the report's main theorem. The LaTeX source recompiled cleanly, and the build log reports only propext, Classical.choice and Quot.sound.

## Disposition

APPROVED — merged as PR 1106. The submission gives a complete, formalised disproof of conjecture 00000006291.
