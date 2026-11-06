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

**Conjecture as filed.** The filed statement says surjective sliding-block automorphisms of radius r and entropy h satisfy h <= r log 2, with equality asymptotically attained by elementary families and a discrete extremal entropy spectrum. I read 'automorphism' as a shift-commuting homeomorphism of a full shift on a finite alphabet, 'radius' as the minimal symmetric sliding-block radius, and 'entropy' as topological entropy. The source imposes no binary-alphabet restriction.

**Decisive results.** Lean takes the bilateral full shift on the three-symbol alphabet Fin 3. The shift map is a shift-commuting homeomorphism with an explicit inverse; both directions have radius one, and radius zero is impossible because a configuration differing only at coordinate 1 is not detected at coordinate 0. The actual dynamical cylinder covering number is proved to be exactly 3^n for every n, so Mathlib's cover entropy is at least log 3. Since log 3 > log 2 = 1*log 2, `counterexample` violates the literal bound and `radius_entropy_law_false` negates the universal radius-entropy inequality. The hypotheses (surjective shift-commuting homeomorphism, radius one, three-symbol alphabet) are satisfiable and are all met.

**Report correspondence.** The report and Lean agree on the three-symbol shift, the radius-one/minimal-radius proof, the cylinder covering count 3^n, the lower bound log 3, and the final negation. The report explicitly says only a lower bound on total entropy is needed and that the later extremal-family and spectrum clauses are not separately analyzed; refuting the universal inequality is enough.

## Disposition

APPROVED — merged as PR 1102. The submission gives a complete, formalised disproof of conjecture 00000009624.
