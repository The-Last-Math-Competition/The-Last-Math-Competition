# Solution Review — Conjecture 00000009624 (PR 1102)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261022112955`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000009624; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.19.0` and Mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** `verify.py` exited 0.

## Semantic audit

**Conjecture as filed.** Definition: The Curtis-Hedlund-Lyndon theorem gives automorphisms as sliding block codes of radius r; the joint constraint of radius and entropy is unknown. Conjecture: The radius r and entropy h of surjective automorphisms satisfy the linear upper bound h <= r log 2; automorphisms asymptotically attaining equality are elementary rule families, and the entropy spectrum of extremal systems is discrete. (radius-entropy linear law) 定义：Curtis–Hedlund–Lyndon 定理给出自同构为半径 r 的滑动块代码；半径与熵的联合约束未知。猜想：满射自同构的半径 r 与熵 h 满足 h ≤ r·log 2 的线性上界；等号渐近达到的极值自同构为初等规则族，极值系统的熵谱为离散集。（半径-熵线性律）

**Decisive results.** The actual bilateral three-symbol full shift is a surjective shift-commuting homeomorphism with minimal sliding-block radius one. Its genuine dynamical cylinder covering number is 3^n, so Mathlib topological entropy is at least log3>log2, violating the proposed universal radius bound. The decisive Lean declaration is `radius_entropy_law_false`, whose statement is: ¬ ∀ (f : Config ≃ₜ Config) (r : ℕ), Function.Commute (f : Config → Config) shift → HasRadius f r → Dynamics.coverEntropy f univ ≤ ((r : ℝ) * Real.log 2 : ℝ) := by. Read against the filed statement, this establishes the negation of the printed clause identified in the README.

**Report correspondence.** The report, README and Lean sources were read. The report states the same construction and the same decisive conclusion; the Lean declaration matches the report's main theorem. The LaTeX source recompiled cleanly, and the build log reports only propext, Classical.choice and Quot.sound.

## Disposition

APPROVED — merged as PR 1102. The submission gives a complete, formalised disproof of conjecture 00000009624.
