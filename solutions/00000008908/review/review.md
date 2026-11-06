# Solution Review — Conjecture 00000008908 (PR 1075)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261022095240`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000008908; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.19.0` and Mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** `verify.py` exited 0.

## Semantic audit

**Conjecture as filed.** The source says 'the monotone chain of the function, with the endpoints of the chain the independence number and the clique number of the complement.' The submission reads this as the sandwich α(G)≤θ(G)≤ω(complement G) for every graph and tests the simple five-cycle C5.

**Decisive results.** Lean uses the actual Mathlib cycleGraph 5 and defines theta as the full standard Lovász SDP supremum over all real PSD trace-one edge-zero matrices. It proves indepNum(C5)=2 and complement.cliqueNum(C5)=2. An explicit rational Gram matrix X=B^T B/11285 (B circulant with first row (-9,32,8,8,32)) is PSD, trace one and edge-zero, and has objective 5041/2257>2; the feasible set is proved nonempty and bounded. Hence θ(C5)>2=ω(complement C5), and the claimed chain α≤θ≤ω(complement) fails. The report also notes that the standard sandwich's true upper endpoint is χ(complement), but the literal source says clique number of the complement.

**Report correspondence.** The report and Lean agree: the same C5 parameters, the same SDP definition, the same Gram certificate and the same strict inequality 2<5041/2257≤θ(C5). The report's chain 2<5041/2257≤θ is supported by the separate `theta_lower_bound` theorem, while the bundled `counterexample` states the final strict inequality 2<θ.

## Disposition

APPROVED — merged as PR 1075. The submission gives a complete, formalised disproof of conjecture 00000008908.
