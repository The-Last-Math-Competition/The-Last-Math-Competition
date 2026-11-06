# Solution Review — Conjecture 00000002704 (PR 1170)

**Submission:** lizaixi01 — `lizaixi01_submission_20261024031707`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000002704; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.33.0` and Mathlib revision `db584cd6d46c92f209a44c0f1c829460d327499d`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** Literal reading of the unconditional iteration clause: for a genuine p-adic local inverse with multiplier norm m, every orbit inside the convergence radius converges linearly (with constant log m). The filed text states no attracting hypothesis |m|<1; I read 'local inverse' as the inverse furnished by the p-adic inverse function theorem, here the actual inverse of f(z)=-z on Q5.

**Decisive results.** The theorem is the negation of the literal universal within-radius convergence claim. It constructs the actual Q5 analytic inverse g(z)=-z (f=g is an involution, derivative -1, multiplier norm 1), proves the native inverse power series has radius ∞ and represents g, and then for every real r>0 produces a nonzero x=5^N with the whole g-orbit in B(0,r) while the even and odd subsequences are the distinct constants x and -x. Hence no limit exists, so the orbit cannot converge linearly. The hypotheses are satisfiable by an actual analytic inverse; the conclusion is a universal negation over all positive radii and all candidate limits.

**Report correspondence.** Report and Lean agree: both state the same f,g, radius ∞, HasFPowerSeriesOnBall, multiplier norm 1, and arbitrarily small nonconvergent orbits. The report explicitly says it refutes only the unconditional iteration clause and makes no claim about a contraction theorem with attracting hypotheses; no stronger prose claim is made.

## Disposition

APPROVED — merged as PR 1170. The submission gives a complete, formalised disproof of conjecture 00000002704.
