# Solution Review — Conjecture 00000007126 (PR 1159)

**Submission:** idealistichacker — `idealistichacker_submission_20261023075713`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000007126; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.33.1` and Mathlib revision `0df444a360eaa60ab8c11dca51a86af692955474`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** `reproduce.py` exited 2.

## Semantic audit

**Conjecture as filed.** The barycentric subdivision is the order complex of the nonempty face poset; flag means every finite clique of the comparability graph is a face; the invariant is the f-vector, whose d-th entry is the number of strict chains of d+1 original faces. Both the full face family and the boundary (whole face removed) are covered.

**Decisive results.** For every poset the order complex is flag, because a finite set is a face exactly when all its pairs are comparable, i.e. when it is a chain. The f-vector of the order complex counts chains of the required cardinality; the same statements are proved for arbitrary finite families of actual subsets and for the boundary family. This establishes the combinatorial content of the conjecture for polytope face posets under the standard face-poset/order-complex dictionary.

**Report correspondence.** The report's flagness and chain-count theorems match the Lean signatures, including the full/boundary distinction and order-isomorphism invariance. The report explicitly states that the Lean domain is finite families of actual subsets and that no geometric triangulation/homeomorphism theorem is formalized.

## Disposition

APPROVED — merged as PR 1159. The submission gives a complete, formalised proof of conjecture 00000007126.
