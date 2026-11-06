# Solution Review — Conjecture 00000008872 (PR 1061)

**Submission:** Galaxy-0 — `Galaxy-0_submission_20261019194300`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000008872; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.31.0`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** The filed clause says atomic weight together with the number part is a complete invariant of all-small equivalence. The submission reads all-small in the standard finite-game sense (every follower is terminal for both players or offers moves to both), and reads atomic-weight zero as far-star equivalence to 0, citing Larsson–Nowakowski.

**Decisive results.** 0 and * are both all-small, both have atomic weight 0 (the Lean proves * is far-star equivalent to 0 in every finite context) and both have numerical part 0, yet they are not equivalent (0 is a previous-player win, * a next-player win). This directly falsifies the 'complete invariant' universal. The hypotheses are satisfiable and the conclusion is the negation of the completeness clause; the other conjuncts are not needed.

**Report correspondence.** Report and Lean agree. The report proves the same witnesses, documents that general atomic-weight theory is not formalized, and states that weight zero is represented by its defining far-star fibre rather than a lookup table. No stronger claim is made than the Lean counterexample.

## Disposition

APPROVED — merged as PR 1061. The submission gives a complete, formalised proof of conjecture 00000008872.
