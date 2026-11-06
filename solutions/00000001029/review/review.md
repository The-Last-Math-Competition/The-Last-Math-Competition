# Solution Review — Conjecture 00000001029 (PR 1220)

**Submission:** idealistichacker — `idealistichacker_submission_20261029083636`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000001029; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.33.1` and Mathlib revision `0df444a360eaa60ab8c11dca51a86af692955474`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** `reproduce.py` exited 2; `checks.py` exited 0.

## Semantic audit

**Conjecture as filed.** For every prime power q and every n and k | n, there is a finite explicit (computable, duplicate-free) list of S(2,k,n)_q designs. 'List' is read as a complete labelled catalogue, not one representative per isomorphism class.

**Decisive results.** The q-only catalogue searches finite field operation tables, enumerates all carrier codes of k-dimensional subspaces, all families of such codes, filters by the exact condition that every 2-dimensional subspace is contained in exactly one block, and deduplicates. Soundness and completeness are proved against the actual submodule-design predicate, and field transport proves that every design over any field of order q occurs exactly once. Hence for each n,k|n a finite explicit complete list exists (possibly empty when no design exists).

**Report correspondence.** The report's main theorem, the field-construction lemma, the code/incidence lemma, the catalogue lemma, and the field-change lemma match the Lean theorem signatures. The report explicitly disclaims nonemptiness, efficiency, structural classification, and isomorphism-class quotienting.

## Disposition

APPROVED — merged as PR 1220. The submission gives a complete, formalised proof of conjecture 00000001029.
