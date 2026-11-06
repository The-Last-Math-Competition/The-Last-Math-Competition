# Solution Review — Conjecture 00000009343 (PR 1209)

**Submission:** Galaxy-0 — `Galaxy-0_submission_20261026200800`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000009343; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.31.0`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** The filed clause says the Hewitt–Savage zero-one law holds for exchangeable sequences, with the symmetric sigma-algebra. The submission reads this literally as exchangeability alone (no independence), on the two-point outcome space with the constant fair-bit sequence.

**Decisive results.** The constant sequence X is exchangeable (indeed invariant under every coordinate relabeling). The all-ones event is in the symmetric sigma-algebra and has probability 1/2, neither 0 nor 1. Hence exchangeability alone does not imply the zero-one law. The conclusion is the negation of the universal exchangeability-only assertion; the classical iid Hewitt–Savage theorem is explicitly not contradicted.

**Report correspondence.** Report and Lean agree: both construct the finite probability space, the constant sequence, the symmetric all-ones event and probability 1/2, and the failure of the zero-one law. The report explicitly says the iid hypothesis is missing and that it does not refute the classical theorem.

## Disposition

APPROVED — merged as PR 1209. The submission gives a complete, formalised disproof of conjecture 00000009343.
