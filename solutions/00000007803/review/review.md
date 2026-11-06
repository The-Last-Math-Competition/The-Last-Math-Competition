# Solution Review — Conjecture 00000007803 (PR 1087)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261022104309`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000007803; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.19.0` and Mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** Definition: A zero-one type extreme value law: the ratio of the maximal norm M_n = max_{i<=n}|X_i| of an isotropic log-concave sequence X_i to sqrt n. Conjecture: The distribution of M_n/sqrt n minus c_n converges to a Gumbel-type extreme value law, with normalization c_n = sqrt(2 log n)/sqrt n and correction term (log log n)/sqrt(2 log n) times n^{-1/2}; the Gumbel scale parameter is an explicit function of L_K, and the product of the extreme exponent with the thin-shell constant is the universal constant 1/sqrt 3. (Gumbel law for maximal log-concave norms) 定义：0-1 型极端值律：迷向 log-concave 列 X_i 的最大范数 M_n=max_{i≤n}|X_i| 与 √n 之比。猜想：M_n/√n - c_n 的分布收敛到 Gumbel 型极值律，规范化常数 c_n=√(2 log n)/√n 的修正项为 log log n/√(2 log n)·√n^{-1}；且 Gumbel 尺度参数为 L_K 的显式函数，极值指数与薄壳常数之积恒为普适常数 1/√3。

**Decisive results.** Actual iid samples uniform on [-sqrt(3),sqrt(3)] are isotropic and log-concave, but their maxima are uniformly bounded. The exact normalization in the source, including any fixed multiple of its log-log correction, tends almost surely to zero and cannot converge to any positive-scale Gumbel law. The decisive Lean declaration is `corrected_center_no_gumbel`, whose statement is: theorem corrected_center_no_gumbel (a location scale : ℝ) : ¬ConvergesToCDF (fun n => center n+a*correction n) (gumbelCDF location scale) := by. Read against the filed statement, this establishes the negation of the printed clause identified in the README.

**Report correspondence.** The report, README and Lean sources were read. The report states the same construction and the same decisive conclusion; the Lean declaration matches the report's main theorem. The LaTeX source recompiled cleanly, and the build log reports only propext, Classical.choice and Quot.sound.

## Disposition

APPROVED — merged as PR 1087. The submission gives a complete, formalised disproof of conjecture 00000007803.
