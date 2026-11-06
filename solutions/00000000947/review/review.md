# Solution Review — Conjecture 00000000947 (PR 1072)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261022090328`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000000947; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.19.0` and Mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** The source claims that in fixed dimension the optimal lower envelope of the modulus of uniform convexity is given by the ℓ_q^n family, with q chosen from ε and n, q→2 as ε→0 and q→∞ as ε→∞, and explicit rational endpoint slopes. The submission reads the 'optimal lower envelope' as the infimum of δ_X(ε) over all genuine norms X on the fixed plane R², with ℓ_q^2 as the claimed extremal family.

**Decisive results.** Lean defines genuine norm axioms, the modulus as an actual infimum over all admissible unit pairs, and the envelope as an actual infimum over all norms. For the sup norm the pair u=(1,ε/2), v=(1,-ε/2) is admissible with zero defect, so `envelope_zero` gives envelope(ε)=0 for 0≤ε≤2. For every finite 1<q<∞, `lp_modulus_pos` proves the actual ℓ_q² modulus is strictly positive for every 0<ε≤2 (strict convexity plus compactness of the admissible set). Thus no finite-q ℓ_q² can attain the zero envelope, and `no_selector_tending_two` shows no minimizing exponent selector with q(ε)→2 can do so. The proof also covers the uniformly convex class: `arbitrarily_small_uniformly_convex_lp` shows the infimum over uniformly convex ℓ_q² norms is zero for ε<2, so the obstruction survives that restriction.

**Report correspondence.** The report and Lean agree: the same genuine-norm definition, the same sup-norm zero witness, the same strict positivity for finite ℓ_q², the same selector contradiction and the same uniformly convex approximation. The report explicitly says the fixed formula is not assumed and that the unit-sphere convention is used (with the unit-ball version also proved).

## Disposition

APPROVED — merged as PR 1072. The submission gives a complete, formalised disproof of conjecture 00000000947.
