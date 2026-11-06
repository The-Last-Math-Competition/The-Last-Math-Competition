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

**Conjecture as filed.** The source asks for two algorithms with the same asymptotic convergence rate but different finite-scale behavior, realized by an explicit step-size pair with the same limit but different pre-asymptotics. The submission uses gradient descent on f(x)=x^2/2 from x_0=1 with step schedule 1/2 throughout versus 1/4 at index m, 2/3 at m+1, and 1/2 elsewhere.

**Decisive results.** Lean defines the actual gradient iterates using Mathlib's deriv, proves both step schedules lie in (0,1), proves the closed forms x_n=2^{-n} and y_n=(3/2)2^{-n} only at n=m+1, prefix equality through m, the exact error gap 2^{-(m+2)}, identical tails from m+2, convergence to 0, and successive-error ratio 1/2 for both. SeparationClaim existentially quantifies a single differentiable objective and, for every m, two valid schedules with these properties, exactly the source's existential separation. The hypotheses are satisfiable and the conclusion is not assumed.

**Report correspondence.** The report proves the same schedules, closed forms, exact gap, limits, rate and eventual equality; Lean's SeparationClaim and error_gap match. The report explicitly notes that the source defines no operator or numerical invariant called 'finite-scale spectrum' and that finite error behavior is the chosen natural reading.

## Disposition

APPROVED — merged as PR 1113. The submission gives a complete, formalised proof of conjecture 00000006090.
