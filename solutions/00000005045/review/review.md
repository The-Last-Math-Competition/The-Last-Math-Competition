# Solution Review — Conjecture 00000005045 (PR 1149)

**Submission:** lizaixi01 — `lizaixi01_submission_20261023064002`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000005045; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.33.0` and Mathlib revision `db584cd6d46c92f209a44c0f1c829460d327499d`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** The source defines the local-to-global transfer as the conversion of Hanf local isomorphism to global isomorphism, then asserts a radius-two conversion-constant table with three degree tiers (breakpoints 3 and 5), monotone within tiers, and size doubling across tier jumps. The submission reads the table as a uniform threshold/size-cutoff rule for that conversion and tests the lowest tier at degree 2.

**Decisive results.** For every t, G_t = (t+1) disjoint copies of C12 and H_t = 2(t+1) disjoint copies of C6 have equal order 12(t+1), all vertex degrees 2, a genuine vertex Hanf matching (every rooted induced radius-2 ball is the same five-vertex path), and equality of every rooted-type count, so ThresholdHanf (G t) (H t) q holds for every q. Yet there is no global graph isomorphism: an isomorphism would send a connected C12 component into one C6 component and induce an injection Fin 12 -> Fin 6. `arbitrary_size_obstruction` produces such t with order at least N for every N, and `no_uniform_global_conversion` negates the existence of any uniform N,q conversion. The cycle-copy graphs are explicit and satisfy the literal degree-2, radius-2 hypotheses; the negation is of the conversion premise on which the asserted table is built.

**Report correspondence.** The report and Lean agree: the report states the same C12/C6 family, actual rooted induced balls, genuine Hanf counts, nonisomorphism and arbitrary-size theorem; `arbitrary_size_obstruction` and `no_uniform_global_conversion` formalize the report's final claims. The report is explicit that it does not assign the unspecified numeric entries 3/5, monotonicity or doubling; that is a scope limitation, not a stronger prose claim.

## Disposition

APPROVED — merged as PR 1149. The submission gives a complete, formalised disproof of conjecture 00000005045.
