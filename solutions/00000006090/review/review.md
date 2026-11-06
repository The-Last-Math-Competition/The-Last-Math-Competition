# Solution Review — Conjecture 00000006090 (PR 1113)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261022115444`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000006090; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.19.0` and Mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** Definition: Asymptotic convergence and the finite-scale spectrum are two layers. Conjecture: There exist two algorithms with the same asymptotic convergence rate but different finite-scale behavior, and the separation is realized by an explicit step-size pair with the same limit but different pre-asymptotics. (same asymptotics-different finite-spectrum step-size separation) 定义：渐近收敛与有限尺度谱指两层。猜想：存在两算法的渐近收敛率相同而有限尺度行为不同,分离由同极限异预渐近的显式步长对实现。（渐近同-有限谱异步长分离）

**Decisive results.** Lean constructs two gradient-descent step-size schedules with the same asymptotic rate 1/2 and the same limit 0 but different finite-scale error curves, and verifies the recursive updates and exact error gap. The theorem `conjecture_6090_true : SeparationClaim` establishes the filed separation.

**Report correspondence.** The report, README and Lean sources were read. The report states the same construction and the same decisive conclusion; the Lean declaration matches the report's main theorem. The LaTeX source recompiled cleanly, and the build log reports only propext, Classical.choice and Quot.sound.

## Disposition

APPROVED — merged as PR 1113. The submission gives a complete, formalised proof of conjecture 00000006090.
