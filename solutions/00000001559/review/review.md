# Solution Review — Conjecture 00000001559 (PR 1213)

**Submission:** LibertychaserUS — `LibertychaserUS_submission_20261027064631`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000001559; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.33.1` and Mathlib revision `0df444a360eaa60ab8c11dca51a86af692955474`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** `check.py` exited 124.

## Semantic audit

**Conjecture as filed.** The filed statement says r6 is an explicit quadratic algebraic number of the (1+√3)/2·(√3−1) type, realized by one central disk and five annular disks, and that r7 is cubic. The submission reads the r6 clause literally as the equality r6 = (1+√3)/2·(√3−1). That expression equals 1, so the claim being refuted is r6 = 1. It also treats a distinct-centre variant.

**Decisive results.** The theorem negates the literal equality reading. The definitions are the filed ones: r6 is the infimum of radii r for which six closed disks of radius r cover the closed unit disk, with unrestricted centres (and separately with pairwise distinct centres). Lean proves r6 ≤ 3/4 via the explicit four-corner certificate: every point of the unit disk is within squared distance 1/2 of one of (±1/2,±1/2), hence within distance 1/√2 < 3/4. Since 3/4 < 1, r6 ≠ 1, so the asserted value is false. The hypotheses are satisfiable and no conclusion is assumed.

**Report correspondence.** The report's main theorem is exactly the Lean conjunction. The report proves the certificate and the identity (1+√3)/2·(√3−1)=1, matching Lean's `conjectured_expr_eq_one` and `cover_of_corners`. The report explicitly says the r7 clause and the structural realization are not formalized and that refuting the r6 clause suffices. No stronger formal claim is made.

## Disposition

APPROVED — merged as PR 1213. The submission gives a complete, formalised disproof of conjecture 00000001559.
