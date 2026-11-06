# Solution Review — Conjecture 00000007468 (PR 1212)

**Submission:** LibertychaserUS — `LibertychaserUS_submission_20261027064413`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000007468; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.33.1` and Mathlib revision `0df444a360eaa60ab8c11dca51a86af692955474`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** `check.py` exited 0.

## Semantic audit

**Conjecture as filed.** The filed statement says the spectrum of a weighted shift is a disk whose radius is the limit superior of the weights. The submission reads this universally over bounded complex weight sequences, for the unilateral forward weighted shift W e_k = w_k e_{k+1} on ℓ²(ℕ), with the centre of the disk free and the radius equal to limsup_k |w_k|. This is the weakest natural disk reading.

**Decisive results.** The theorem is the negation of the universal claim. The counterexample weights w_k = 2 for odd k and 1/2 for even k are bounded by 2, so the shift is a bounded operator and the hypotheses are satisfied. Lean proves limsup |w_k| ≥ 2 and, using W² being an isometry, that the spectrum is contained in the closed unit disk. If the spectrum were a closed disk of radius L = limsup |w_k| ≥ 2 about any centre c, then c+L and c-L would both lie in the unit disk, forcing 2L ≤ 2, contradicting L ≥ 2. Thus no such disk exists; the conclusion is a genuine negation of the universal statement, not a related arithmetic fact.

**Report correspondence.** The report's main theorem is the same refutation, and Section 4 explicitly says the Lean proof only uses σ(W) ⊆ closed unit disk and limsup ≥ 2, not the exact equality limsup = 2 or σ(W) = closed disk. The prose is weaker than the Lean theorem, not stronger. The report compiles.

## Disposition

APPROVED — merged as PR 1212. The submission gives a complete, formalised disproof of conjecture 00000007468.
