# Solution Review — Conjecture 00000003363 (PR 1199)

**Submission:** lizaixi01 — `lizaixi01_submission_20261025011842`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000003363; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.33.0` and Mathlib revision `db584cd6d46c92f209a44c0f1c829460d327499d`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** Literal: the entropy function of quadratic maps is continuous but nowhere monotone. The submission reads the canonical logistic family q_a(x)=a x(1−x) on [0,1], parameters a∈[0,4], with topological entropy.

**Decisive results.** For a∈[1/4,1/2], q_a is 1/2-Lipschitz on [0,1], so the Lean general theorem proves its topological cover entropy is zero. Hence the entropy function is constant on the nonempty open interval (1/4,1/2), so it is both monotone and antitone there and is not nowhere monotone in the standard weak sense. The hypotheses are satisfiable and this is the negation of the printed nowhere-monotone clause.

**Report correspondence.** The report theorem matches the Lean `printed_nowhere_monotone_false`; the report explicitly states the logistic/topological-entropy reading and does not claim continuity or the fractal-dimension correction.

## Disposition

APPROVED — merged as PR 1199. The submission gives a complete, formalised disproof of conjecture 00000003363.
