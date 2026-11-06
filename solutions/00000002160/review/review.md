# Solution Review — Conjecture 00000002160 (PR 1066)

**Submission:** MrBrain295 — `mrbrain295_submission_20261020150000`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000002160; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.28.0` and Mathlib revision `8f9d9cff6bd728b17a24e163c9402775d9e6a365`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** The conjecture asserts that the independence number of the Higman-Sims graph equals the Hoffman bound, and that the kernel of the bound is the Delsarte semilattice.

**Decisive results.** Lean constructs the Higman-Sims graph from the S(3,6,22) hexads and proves it is an srg(100,22,0,6). For any such strongly regular graph the spectrum is {22,2,-8}, so the Hoffman bound is 100*8/(22+8)=80/3. The independence number is an integer, hence cannot equal 80/3; the Lean theorem also proves indepNum >= 22. This directly falsifies the first conjunct of the filed conjunction.

**Report correspondence.** The report and Lean agree. The submitted PDF was independently recompiled; the built Lean project proves the same main theorem.

## Disposition

APPROVED — merged as PR 1066. The submission gives a complete, formalised disproof of conjecture 00000002160.
