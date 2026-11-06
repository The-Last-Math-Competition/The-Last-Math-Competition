# Solution Review — Conjecture 00000002195 (PR 1198)

**Submission:** lizaixi01 — `lizaixi01_submission_20261025002144`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000002195; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.33.0` and Mathlib revision `db584cd6d46c92f209a44c0f1c829460d327499d`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** Literal: the speed of the substitution product of perfect-graph properties is exp((1/2+o(1)) n log n). The submission reads the labelled speed, ordinary one-vertex substitution, and both input properties the full hereditary perfect-graph property.

**Decisive results.** The theorem injects every Boolean m×m matrix into a distinct perfect labelled graph on 2m vertices in the substitution product (via K1 substitution and the two-colouring bipartite construction), giving 2^{m²}≤s_{2m} and m² log2≤log s_{2m}. Hence log s_n cannot be eventually bounded by C n log n for any finite C, and the exact exp((1/2+o(1))n log n) formula is false. The construction uses only perfect graphs and genuine substitutions; hypotheses are satisfiable.

**Report correspondence.** The report theorem matches the Lean `not_printed_speed_formula` and `no_eventual_log_bound`; the report explicitly states the labelled-speed and full-property reading. No stronger claim about unlabelled speeds or restricted factorial subclasses.

## Disposition

APPROVED — merged as PR 1198. The submission gives a complete, formalised disproof of conjecture 00000002195.
