# Solution Review — Conjecture 00000003527 (PR 1115)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261022121412`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000003527; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.19.0` and Mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** Definition: Convergence of ordinal exponentiation: normal functions. Conjecture: The fixed-point chain of normal functions: the fixed-point sequence of a normal function is closed unbounded, with the ω-th term of the sequence the transfinite iteration limit. (normal function fixed point closed unbounded chain) 定义：序数指数的收敛：正规函数。猜想：正规函数的不动点链：正规函数的不动点列为闭无界且列的第 ω 项为超限迭代极限。（正规函数不动点闭无界链）

**Decisive results.** Lean proves, for every normal ordinal function, that the fixed-point set is closed and unbounded, that Mathlib's derivative enumerates it, that the ω-th term is the supremum of the finite iterates, and that the least fixed point above any ordinal is the transfinite iteration limit. The theorem `conjecture_3527_true : FixedPointClaim` establishes the filed statement.

**Report correspondence.** The report, README and Lean sources were read. The report states the same construction and the same decisive conclusion; the Lean declaration matches the report's main theorem. The LaTeX source recompiled cleanly, and the build log reports only propext, Classical.choice and Quot.sound.

## Disposition

APPROVED — merged as PR 1115. The submission gives a complete, formalised proof of conjecture 00000003527.
