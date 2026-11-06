# Solution Review — Conjecture 00000005268 (PR 1099)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261022112031`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000005268; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.19.0` and Mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** Definition: The point-vortex system is the Hamiltonian dynamics of planar vortex points. Conjecture: Finite-time collision of three vortices is impossible, the exclusion is given by an explicit additional integral of relative coordinates, valid for general strength triples. (additional-integral exclusion of three-vortex collisions) 定义：点涡系统指平面涡点的哈密顿动力学。猜想：三点涡的有限时间碰撞不可能,排除由相对坐标的显式通积分给出且对一般强度组成立。（三点涡碰撞通积分排除）

**Decisive results.** Three vortices of nonzero mixed-sign circulation undergo an explicit finite-time total collision. The initial positions are 0, 1, and 3/8 + (7/8)i. All three remain distinct for 0 ≤ t < 1/2 and converge to c = 3/8 − (15/56)i as t approaches 1/2 from the left. The complete trajectory and actual conventional point-vortex ODE (including 1/(2π)) are formally verified. The proof does not substitute a numeric identity, an assumed ODE solution, or an arbitrary collision endpoint for the dynamics. - `lean/Main.lean`: vector fields, rational circulations, physical circulation rescaling, exact initial data, differentiable solution, noncollision before T, all three collision limits, and negation of the universal exclusion. - `main.tex`: complete direct mathematical argument and formalization boundary. - `SOURCE.md`: frozen bilingual statement. - `verification/lean-strict.log`: actual warnings-as-er The decisive Lean declaration is `conjecture_false`, whose statement is: ¬ NoFiniteTimeThreeVortexCollision := by. Read against the filed statement, this establishes the negation of the printed clause identified in the README.

**Report correspondence.** The report, README and Lean sources were read. The report states the same construction and the same decisive conclusion; the Lean declaration matches the report's main theorem. The LaTeX source recompiled cleanly, and the build log reports only propext, Classical.choice and Quot.sound.

## Disposition

APPROVED — merged as PR 1099. The submission gives a complete, formalised disproof of conjecture 00000005268.
