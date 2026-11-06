# Solution Review — Conjecture 00000001491 (PR 1144)

**Submission:** lizaixi01 — `lizaixi01_submission_20261023052235`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000001491; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.33.0` and Mathlib revision `db584cd6d46c92f209a44c0f1c829460d327499d`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** Literal: the Hénon map is H_{a,b}(x,y)=(1−ax²+y,b), with classical parameters (a,b)=(1.4,0.3); its attractor has Hausdorff dimension d_H with 1.26<d_H<1.28. The submission reads the printed second coordinate as the constant b (not the usual bx) and treats the attractor through the natural omega-limit and compact fully invariant objects.

**Decisive results.** Lean defines exactly the printed polynomial map on the Euclidean plane. It proves every image lies on the horizontal line y=b, hence every positive iterate lies there; Mathlib's actual omegaLimit of every initial set and the closure of the union of all singleton omega-limits lie on that closed line. It constructs a real-line isometry onto the line and proves the line has genuine Hausdorff dimension 1, so every subset of the line has dimH≤1. Any compact fully invariant set A with H(A)=A is also contained in the line, because A=H(A) is an image of H. Therefore at a=7/5, b=3/10 the lower bound 63/50=1.26 fails for every actual omega-limit set and every compact fully invariant set. This is a direct counterexample to the filed dimension claim for the printed map; the usual map with second coordinate bx is explicitly outside the claim.

**Report correspondence.** The report matches Lean: printedMap, horizontalLine, line_dimension, omega_subset_line, fully_invariant_subset_line, no_large_compact_fully_invariant_set, source_parameters_counterexample and source_parameters_real_dimensions. The report explicitly emphasizes the printed constant b, not bx, and disclaims any result for the usual Hénon map, box dimension, or Kaplan–Yorke formula. No stronger prose claim than the formal statements.

## Disposition

APPROVED — merged as PR 1144. The submission gives a complete, formalised disproof of conjecture 00000001491.
