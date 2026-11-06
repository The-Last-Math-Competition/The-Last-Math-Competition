# Solution Review — Conjecture 00000005131 (PR 1080)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261022101706`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000005131; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.19.0` and Mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** Definition: The eigenvalue condition number is the modulus of the reciprocal of the inner product of left and right eigenvectors, together with the perturbation sensitivity of multiple eigenvalues. Conjecture: An eigenvalue of algebraic multiplicity m shifts under epsilon perturbation by the one-over-m power of epsilon, with the exponent decided by the maximal Jordan block size; the pseudospectral area scales as epsilon to the 2/m, with constant containing an explicit power of the condition number; and for nearly orthogonal eigenvectors the reciprocal condition number is an epsilon-type small quantity, with minimal perturbation configuration of lattice type. (power-law response of multiple eigenvalue perturbations) 定义：特征值条件数：左右特征向量内积倒数的模；重特征值的扰动敏感度。猜想：代数重数 m 的特征值在 ε 扰动下偏移为 ε 的 m 分之一次幂型且指数由最大若尔当块尺寸决定；伪谱面积标度为 ε 的 2/m 次幂且常数含条件数的显式幂；特征向量几乎正交时条件数倒数为 ε 型小量且最小扰动配置为格点型。（重特征值扰动幂律响应）

**Decisive results.** For the complex zero matrix of order two, algebraic multiplicity is two, but the exact worst eigenvalue displacement under induced infinity norm perturbations of radius epsilon is epsilon and the exact pseudospectral Lebesgue area is pi epsilon squared. Therefore the source's sharp powers based on algebraic multiplicity are false. The source also mentions maximal Jordan block size. The paper openly acknowledges that the corrected version based consistently on maximal Jordan block size is compatible with the example; a big-O-only reading is likewise not refuted. The condition-number and lattice clauses are not addressed. Lean proves actual characteristic-polynomial root multiplicity, the exact disk pseudospectrum over all admissible complex matrix perturbations, attained worst displacement, actual Lebesgue area, and negations of the universal lower bounds required by the two claimed sharp The decisive Lean declaration is `not_multiplicity_response_law`, whose statement is: ¬ MultiplicityResponseLaw := by. Read against the filed statement, this establishes the negation of the printed clause identified in the README.

**Report correspondence.** The report, README and Lean sources were read. The report states the same construction and the same decisive conclusion; the Lean declaration matches the report's main theorem. The LaTeX source recompiled cleanly, and the build log reports only propext, Classical.choice and Quot.sound.

## Disposition

APPROVED — merged as PR 1080. The submission gives a complete, formalised disproof of conjecture 00000005131.
