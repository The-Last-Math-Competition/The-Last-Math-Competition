# Solution Review — Conjecture 00000000998 (PR 1071)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261022085427`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000000998; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.19.0` and Mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** `verify.py` exited 0.

## Semantic audit

**Conjecture as filed.** The source claims that the supremum of the ratio of the completely bounded norm to the ordinary operator norm, over maps on the three-qubit observable algebra M8(C), equals √2. The submission reads the supremum as taken over nonzero completely bounded complex-linear maps on M8(C); the source imposes no complete-positivity restriction.

**Decisive results.** Lean defines the actual Euclidean operator norm and the amplification id_k⊗T on M_k⊗M8. It proves the transpose map τ(A)=A^T is complex-linear, has ordinary norm 1, is completely bounded with cb norm ≤64, and has cb norm ≥8: the 64×64 swap matrix F has norm 1 and its blockwise transpose Q satisfies QΩ=8Ω with Ω≠0. Hence the ratio ||τ||_cb/||τ|| is at least 8>√2, so √2 is not an upper bound and `not_claimed_supremum` shows it is not the supremum. The transpose is a legitimate map on M8(C); it is not completely positive, but the source does not restrict to completely positive maps.

**Report correspondence.** The report and Lean agree: ordinary norm 1, cb norm between 8 and 64, the explicit swap/Ω witness and the direct negation of the √2 supremum. The report explicitly states that complete positivity is not assumed and that the sharp transpose cb norm is not claimed.

## Disposition

APPROVED — merged as PR 1071. The submission gives a complete, formalised disproof of conjecture 00000000998.
