# Solution Review — Conjecture 00000002819 (PR 1091)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261022105333`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000002819; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.19.0` and Mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** Definition: Large deviations of subadditive processes: Hammersley-type functionals. Conjecture: For the independent case the large-deviation rate of subadditive functionals is always a linear function; the subadditive correction of the rate is the reciprocal of the correlation length. (subadditive rate correlation correction) 定义：子加性过程的大偏差指 Hammersley 类型泛函。猜想：独立情形的子加性泛函的大偏差速率恒为线性函数；速率的次可加修正由相关长度的倒数给出。（子加性速率相关修正）

**Decisive results.** Actual iid standard Gaussian coordinates on an infinite product probability space give samplewise additive, hence subadditive, block sums. Their genuine sample-mean laws satisfy a Chernoff bound exp(-N/2) on (1,infinity), incompatible with every affine real-valued LDP rate: nonnegativity forces a constant rate, normalization forces zero, and the open-set lower bound on (1,2) contradicts that exponential tail bound. Every nonempty real interval has positive probability. The decisive Lean declaration is `independent_subadditive_counterexample`, whose statement is: iIndepFun coordinate gaussianProduct ∧ (∀ i, gaussianProduct.map (coordinate i) = gaussianReal 0 1) ∧ (∀ m n k ω, blockSum m (n + k) ω ≤ blockSum m n ω + blockSum (m + n) k ω) ∧ ¬ LinearRateAssertion :=. Read against the filed statement, this establishes the negation of the printed clause identified in the README.

**Report correspondence.** The report, README and Lean sources were read. The report states the same construction and the same decisive conclusion; the Lean declaration matches the report's main theorem. The LaTeX source recompiled cleanly, and the build log reports only propext, Classical.choice and Quot.sound.

## Disposition

APPROVED — merged as PR 1091. The submission gives a complete, formalised disproof of conjecture 00000002819.
