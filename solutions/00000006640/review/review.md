# Solution Review — Conjecture 00000006640 (PR 1110)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261022114433`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000006640; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.19.0` and Mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** The source asks for two systems with the same static solution set but different time spectra, realized by an explicit master-equation pair with the same statics and different dynamics. The submission uses two-state continuous-time master equations Q_1=[[-1,1],[1,-1]] and Q_2=[[-2,2],[2,-2]] with common stationary vector (1/2,1/2).

**Decisive results.** Lean proves Q_1 and Q_2 are genuine generators, are symmetric and reversible with respect to the same probability vector, have the same normalized static set {uniform} and the same full kernel {(a,a)}, but have generator spectra {0,-2} and {0,-4}. It also proves the explicit propagators are stochastic fundamental solutions with HasDerivAt master equations, semigroup law and initial condition, and that their spectra {1,e^{-2t}} and {1,e^{-4t}} differ for every t>0. SeparationClaim existentially quantifies exactly these systems; the hypotheses are satisfiable and the conclusion is the source's existence claim, strengthened to full-kernel equality and every positive time.

**Report correspondence.** The report's theorem lists the same generators, common stationary vector, identical static sets and kernels, different generator spectra, and different propagator spectra at every positive time. Lean's SeparationClaim and the generator/transition spectrum theorems match; no stronger prose claim.

## Disposition

APPROVED — merged as PR 1110. The submission gives a complete, formalised proof of conjecture 00000006640.
