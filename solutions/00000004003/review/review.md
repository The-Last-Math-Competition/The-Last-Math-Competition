# Solution Review — Conjecture 00000004003 (PR 1103)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261022113015`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000004003; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.19.0` and Mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** Definition: The expected signature E[S(X)] is the integral of the signature against the process distribution. Conjecture: The expected signature determines the distribution if and only if the Carleman condition for the moment problem of the distribution family holds; within this class the first floor(d/2) levels never determine the distribution, and all levels up to infinity are required. (determinacy boundary of the expected signature) 定义：期望签名 E[S(X)] 指签名对过程分布的积分。猜想：期望签名唯一决定分布当且仅当分布族的矩问题 Carleman 条件成立;且在此类内首 ⌊d/2⌋ 层不决定分布,需至无穷层。（期望签名决定性边界）

**Decisive results.** this result concerns an original, unaugmented process/path law. It does not concern a probability law on signatures or a tree-like quotient, and does not refute standard uniqueness theorems on those spaces. The source states process distribution without the latter qualifications. Time augmentation and signature-injective path classes are outside the claim proved here. Take x₁(t) = 4t(1−t) and x₂(t) = 8t(1−t), 0 ≤ t ≤ 1, and their two Dirac laws. Their midpoint values differ (1 versus 2), whereas the actual recursive iterated integrals give the same full signature (1,0,0,...). Both smooth paths start at zero. Their exact supremum norms are 1 and 2, giving all finite norm moments and inverse-even-moment-root Carleman summands 1 and 1/2. The source does not specify a unique infinite-dimensional Carleman convention. The formal statement uses a genuine radial supremum-norm Carleman condition, The decisive Lean declaration is `conjecture_false`, whose statement is: ¬ CarlemanSignatureDetermination := by. Read against the filed statement, this establishes the negation of the printed clause identified in the README.

**Report correspondence.** The report, README and Lean sources were read. The report states the same construction and the same decisive conclusion; the Lean declaration matches the report's main theorem. The LaTeX source recompiled cleanly, and the build log reports only propext, Classical.choice and Quot.sound.

## Disposition

APPROVED — merged as PR 1103. The submission gives a complete, formalised disproof of conjecture 00000004003.
