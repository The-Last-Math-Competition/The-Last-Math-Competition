# Solution Review — Conjecture 00000009305 (PR 1107)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261022113614`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000009305; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.19.0` and Mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** `verify.py` exited 0.

## Semantic audit

**Conjecture as filed.** Definition: The ergodic decomposition of local limits. Conjecture: Ergodic decomposition: the decomposition of limits into extreme points, with the support of the points transitive graphs. (local ergodic decomposition extreme transitive support) 定义：局部极限的遍历分解。猜想：遍历分解：极限的分解为极端点且点的支撑为传递图。（局部极限遍历分解极端点传递图极限分解支撑）

**Decisive results.** Uniform rooting of growing disjoint unions of P3 has the actual constant local weak limit given by uniform rooting of P3. A measurable radius-two cylinder event has mass one in this limit and zero in every law concentrated on vertex-transitive graphs, excluding any such barycentric decomposition. The decisive Lean declaration is `no_transitive_barycentric_decomposition`, whose statement is: theorem no_transitive_barycentric_decomposition {I : Type*} [MeasurableSpace I] (mixing : Measure I) (components : I → Measure RootedSpace) (hsupport : ∀ᵐ i ∂mixing, ConcentratedOnTransitive (components i)) : ¬ (∀ s, MeasurableSet s → pathLaw s = ∫⁻ i, components i s ∂mixing) := by. Read against the filed statement, this establishes the negation of the printed clause identified in the README.

**Report correspondence.** The report, README and Lean sources were read. The report states the same construction and the same decisive conclusion; the Lean declaration matches the report's main theorem. The LaTeX source recompiled cleanly, and the build log reports only propext, Classical.choice and Quot.sound.

## Disposition

APPROVED — merged as PR 1107. The submission gives a complete, formalised disproof of conjecture 00000009305.
