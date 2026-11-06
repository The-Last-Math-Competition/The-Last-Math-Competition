# Solution Review — Conjecture 00000007841 (PR 1073)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261022091401`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000007841; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.19.0` and Mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** `verify.py` exited 0.

## Semantic audit

**Conjecture as filed.** The source defines p(G) as the probability that Karger's uniform-edge contraction algorithm outputs any minimum cut, and claims that the explicit bound p(G)≥2(1-ε)/n² with ε(n)=O(1/n) is tight (the Chinese says equality) on the cycle. The submission reads p(G) literally as returning any minimum cut and tests the simple cycles C_n.

**Decisive results.** Lean models the actual simple cycle graph, the actual uniform-edge contraction histories and the actual returned bipartition. It proves every history returns a proper cut of size exactly 2, and every proper cut of a cycle has size at least 2, so every history succeeds in returning a minimum cut. The actual path weights are nonnegative and sum to one, hence `actual_cycle_success_probability` gives p(C_n)=1. `actual_no_cycle_sharpness` shows that for any ε with eventual |ε(k)|≤C/(k+2) and any cutoff K, some larger cycle has 2(1-ε)/n²<1=p(C_n). Thus the bound is not tight in the asserted equality sense; the gap tends to one, not zero.

**Report correspondence.** The report and Lean agree: the same cycle model, the same 'any minimum cut' success event, the same probability-one theorem, the same quantitative arbitrary-cutoff contradiction and the same gap-to-one limit. The report explicitly distinguishes this from the survival of a prescribed minimum cut.

## Disposition

APPROVED — merged as PR 1073. The submission gives a complete, formalised disproof of conjecture 00000007841.
