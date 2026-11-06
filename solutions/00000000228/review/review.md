# Solution Review — Conjecture 00000000228 (PR 1098)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261022111808`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000000228; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.19.0` and Mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** `verify.py` exited 0.

## Semantic audit

**Conjecture as filed.** The filed statement uses Stern's actual sequence s(0)=0, s(1)=1, s(2n)=s(n), s(2n+1)=s(n)+s(n+1) and the literal normalization s(n^2)/3^(log_2 n). I read 'the distribution' as the empirical law of a uniformly chosen positive index n in {1,...,N}; this is the natural distribution of the displayed sequence. The spectral-dimension clause is a separate conjunct and need not be interpreted once the first conjunct is refuted.

**Decisive results.** Lean proves s(n^2) <= 25^(m+1) on 8^m <= n <= 8^(m+1), hence normalized n <= 25*(25/27)^m -> 0 for every positive index. It then proves the empirical CDFs have the delta_0 CDF limit at every x != 0 and that no continuous F can be the pointwise CDF limit. Thus the claimed continuous (and nowhere-differentiable) fractal limit is false. The result is a universal statement over the actual Stern sequence, and its hypotheses (the recurrence, positive indices) are satisfiable. The first conjunct is refuted, so the spectral-dimension clause is moot.

**Report correspondence.** The report and Lean agree on the three-bit block bound, the full-sequence limit, the empirical CDF values, and the no-continuous-limit theorem. The report's phrase 'weak limit delta_0' is the standard continuity-point/Portmanteau consequence of the formal CDF limits; the report explicitly says the general weak-convergence equivalence is not formalized, and the decisive no-continuity theorem is formal.

## Disposition

APPROVED — merged as PR 1098. The submission gives a complete, formalised disproof of conjecture 00000000228.
