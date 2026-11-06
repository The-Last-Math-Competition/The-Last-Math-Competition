# Solution Review — Conjecture 00000001002 (PR 1125)

**Submission:** lizaixi01 — `lizaixi01_submission_20261023002437`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000001002; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.33.0` and Mathlib revision `db584cd6d46c92f209a44c0f1c829460d327499d`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** The filed statement claims the smallest complete arc of PG(2,q) has size q^{1/2}+o(q^{1/2}), precisely liminf (min complete arc size)/√q = 1. The submission works with actual projective points and complete arcs for every finite field.

**Decisive results.** For any complete arc S of size k, every point is in S or on a secant through two points of S; counting gives q^2+q+1 ≤ k + C(k,2)(q+1), hence k^2>2q. Thus minSize/√q ≥ √2>1 for every finite field. growing_fields_real_liminf_ne_one proves the liminf is never 1 for any sequence of finite fields with growing cardinality, directly negating the filed liminf claim. The hypotheses are satisfiable (every finite field).

**Report correspondence.** The report states the same counting argument and the same uniform bound; the Lean theorems match. No stronger prose claim.

## Disposition

APPROVED — merged as PR 1125. The submission gives a complete, formalised disproof of conjecture 00000001002.
