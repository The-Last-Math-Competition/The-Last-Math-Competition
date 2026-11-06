# Solution Review — Conjecture 00000009774 (PR 1101)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261022112228`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000009774; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.19.0` and Mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** Definition: Szego's strong limit theorem: logarithmic asymptotics of Toeplitz determinants (secondary terms given by Widom theory). Conjecture: The secondary coefficient of Toeplitz determinants on general domains is given entirely by corner angles of the boundary; in the smooth case the secondary term vanishes, corner contributions being local multiplicative factors with no global correction. (Szego secondary corner law) 定义：Szegő 强极限定理：Toeplitz 行列式的对数渐近（次主项由 Widom 理论给出）。猜想：一般区域上 Toeplitz 行列式的次主项系数完全由边界角落的角代数给出；光滑情形次主项消失且角落贡献为局部乘性因子，无整体修正。（Szego 次主项角落律）

**Decisive results.** On the smooth unit circle, the positive analytic symbol f(θ)=5/4+cos θ has actual n×n Toeplitz matrices with diagonal 5/4 and adjacent diagonals 1/2. Their determinants are (4/3)(1−(1/4)^(n+1)). Consequently log D_n / n tends to zero while log D_n tends to log(4/3)>0. The smooth secondary term does not vanish, and the normalized determinant has a global factor 4/3 without any corners. `lean/Main.lean` defines actual Laurent coefficients and Mathlib Toeplitz matrices c(i−j), proves the general tridiagonal determinant recurrence by Laplace expansion, proves the formula for every n and positivity, and establishes both limits. It also proves C∞ smoothness and positivity of the symbol. `SmoothSecondaryVanishes` is the necessary universal smooth-case subclause over this positive Laurent-symbol family; `conjecture9774_false` negates it. Paper-only bridges are explicitly listed: Fourier coeffici The decisive Lean declaration is `conjecture9774_false`, whose statement is: ¬ SmoothSecondaryVanishes := by. Read against the filed statement, this establishes the negation of the printed clause identified in the README.

**Report correspondence.** The report, README and Lean sources were read. The report states the same construction and the same decisive conclusion; the Lean declaration matches the report's main theorem. The LaTeX source recompiled cleanly, and the build log reports only propext, Classical.choice and Quot.sound.

## Disposition

APPROVED — merged as PR 1101. The submission gives a complete, formalised disproof of conjecture 00000009774.
