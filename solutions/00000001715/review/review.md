# Solution Review — Conjecture 00000001715 (PR 1079)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261022101706`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000001715; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.19.0` and Mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** The filed statement says the LLT for irrational rotations has an explicit period-1 correction, that the correction term is given by the Fourier coefficients of f through the sequence c_k=(1−e(kα))^{-1}, which the source calls decaying, and that the correction is nonzero iff f has nontrivial low-frequency content. The submission reads 'decaying' as c_k→0 and proves the negation.

**Decisive results.** The Lean theorem proves that for every irrational alpha and every positive integer frequency k, the displayed coefficient c_k=(1-exp(2*pi*i*k*alpha))^(-1) has modulus at least 1/2, so the sequence cannot tend to zero. The filed conjecture explicitly describes c_k as 'the decaying sequence' in both English and Chinese. Refuting that asserted decay is a refutation of a necessary property stated in the conjecture; the submission does not claim to refute a different LLT formulation that drops the word 'decaying'.

**Report correspondence.** The report and Lean agree on the non-decay result and the scope limitation; the report explicitly says it does not assert the LLT is false under other formulations and does not analyze the low-frequency criterion. The Lean proves exactly the negation of the source's 'decaying' description, not the negation of the LLT correction.

## Disposition

APPROVED — merged as PR 1079. The submission gives a complete, formalised disproof of conjecture 00000001715.
