# Solution Review — Conjecture 00000005300 (PR 1093)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261022105607`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000005300; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.19.0` and Mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** Literal: there exist two FI modules whose stable groups are all isomorphic but whose total modules are not, with the separation realized in the finite skeleton before stabilization. The submission reads 'stable groups' as the eventual values together with their transition maps and the stable direct limit, and constructs the zero functor versus the functor supported only at the empty set.

**Decisive results.** The Lean defines the finite-set skeleton category, a bundled category of Z-modules, and actual functors supported and zero. supported(0) is Z and supported(n)=0 for n≥1; zero is constantly 0. tailIso is a natural isomorphism of the restrictions to all positive-size sets, so the eventual values and transition maps agree; not_iso shows no natural isomorphism of the full functors because at degree zero it would give Z ≅ 0. The witness satisfies the existential and the hypotheses are satisfiable; the separation is exactly at the empty finite skeleton.

**Report correspondence.** The report's Theorem (restrictions to nonempty sets naturally isomorphic, total modules not, difference at the empty set) matches the Lean. The report also notes finite generation, proved separately by generated_in_degree_zero. The direct-limit consequence is proved on paper but is not needed for the Lean Claim.

## Disposition

APPROVED — merged as PR 1093. The submission gives a complete, formalised proof of conjecture 00000005300.
