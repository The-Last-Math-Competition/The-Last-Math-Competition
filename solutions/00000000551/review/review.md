# Solution Review — Conjecture 00000000551 (PR 1168)

**Submission:** lizaixi01 — `lizaixi01_submission_20261024022805`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000000551; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.33.0` and Mathlib revision `db584cd6d46c92f209a44c0f1c829460d327499d`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** For every special biserial algebra, the little finitistic dimension findim is at most 2; the source's parenthetical mentions cyclic string algebras only as the subclass verified up to n=7.

**Decisive results.** Let A=CQ/I with Q the linearly oriented quiver 3→2→1→0 and I the ideal of all paths of length at least 2. Lean proves the path presentation (the incidence-algebra basis, the quotient equivalence, and that the relation ideal is exactly the span of the three length-2 paths), and certifies the standard special biserial conditions: every vertex has at most one incoming and one outgoing arrow, every arrow has zero permitted followers/predecessors, and all long paths lie in I. The simple S_3 has projective dimension exactly 3: the short exact sequences 0→S_{i-1}→P_i→S_i→0 with P_i projective give pd S_3≤3, while S_1 is not projective and dimension shifting gives pd S_3<3 ⇒ pd S_2<2 ⇒ pd S_1<1, a contradiction. The finitistic dimension is the genuine supremum over finitely generated modules of finite projective dimension, so it is ≥3, negating the universal bound 2.

**Report correspondence.** report.tex matches the Lean algebra, path presentation, special-biserial certificate, projective modules/sequences, projective dimension 3, and finitistic lower bound. PDF text matches. No stronger prose claim.

## Disposition

APPROVED — merged as PR 1168. The submission gives a complete, formalised disproof of conjecture 00000000551.
