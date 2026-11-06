# Solution Review — Conjecture 00000002362 (PR 1084)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261022103633`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000002362; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.19.0` and Mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** The filed statement says the bound constant of the sectorial H∞ calculus is an explicit function of the sector angle, and its singularity diverges as the angle tends to π. The submission reads the first clause as a finite uniform bound depending only on the sector angle and constructs a family A_N=I+NE on fixed C², all sectorial of angle zero (hence in Sect(π/3)), with a fixed admissible rational test g(z)=z/(1+z)^3 on the right half-plane.

**Decisive results.** Lean proves the A_N are genuine complex 2×2 matrices with the Euclidean operator norm, that each is sectorial of angle zero with the full spectral/resolvent condition, that g is holomorphic and bounded (sup≤1, with H0∞ decay) on the open right half-plane, that g(A_N)=I/8−N E/16 is the actual rational functional-calculus value, and that its operator norm is unbounded. The theorem no_fixed_positive_angle_bound negates the existence of a finite uniform bound on this rational test over all operators in Sect(π/3). Since any bounded H∞ calculus on the fixed sector must agree with the rational calculus and satisfy ||g(A)||≤K||g||∞≤K, the unbounded rational test is a necessary obstruction to the filed angle-only calculus bound. The source's second clause (divergence as angle→π) need not be analyzed once the angle-only bound fails.

**Report correspondence.** The report and Lean agree on the fixed Hilbert space, the Euclidean operator norm, the A_N family, sectoriality of angle zero, the admissible g, the exact g(A_N), and the unbounded norm. The report is explicit that the Lean project formalizes the rational-test obstruction and that the full contour calculus/rational-consistency bridge is supplied in the paper, not formalized; it does not claim a formalized H∞ calculus. No undisclosed stronger prose claim was found beyond that bridge.

## Disposition

APPROVED — merged as PR 1084. The submission gives a complete, formalised disproof of conjecture 00000002362.
