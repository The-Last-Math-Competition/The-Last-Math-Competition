# Solution Review — Conjecture 00000004271 (PR 1135)

**Submission:** lizaixi01 — `lizaixi01_submission_20261023034830`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000004271; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.33.0` and Mathlib revision `db584cd6d46c92f209a44c0f1c829460d327499d`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** The filed statement says automorphisms of divisible groups can be uniformly approximated by finitely supported automorphisms in the subgroup-index metric, with an explicit linear exponent bound. The submission takes Q as a divisible group and reads 'finitely supported' as literal finite moved support, finite defect image, or a finite-index fixed subgroup (the standard group-theoretic finitary notions), and allows any genuine metric on Q or on Aut(Q).

**Decisive results.** Lean proves Q is divisible, doubling x↦2x is a nonidentity additive automorphism, and every additive automorphism of Q has the form x↦c x. If c≠1, the moved set is infinite, the defect image (c−1)Q is infinite, and the fixed subgroup is {0} of infinite index; hence the only finitary automorphism is the identity. For any metric on Q, dist(1,2)>0 forces a fixed positive error at x=1, and for any metric on Aut(Q), dist(id,doubling)>0 prevents approximation; the T1-closure version is also proved. Thus the universal approximation claim is false; the hypotheses are satisfiable and the conclusion is the direct negation.

**Report correspondence.** The report/PDF state the same Q, doubling, three finitary notions, finite-index bridge, and the same metric/metric-on-Aut/T1 negations; the Lean theorems match. The report explicitly says the 'subgroup-index metric' is undefined and that all genuine metrics are covered, while nonseparating pseudometrics and basis-relative finite-rank notions are not claimed.

## Disposition

APPROVED — merged as PR 1135. The submission gives a complete, formalised disproof of conjecture 00000004271.
