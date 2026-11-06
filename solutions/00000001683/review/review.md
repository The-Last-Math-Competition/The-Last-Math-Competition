# Solution Review — Conjecture 00000001683 (PR 1095)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261022111146`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000001683; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.19.0` and Mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** Literal: 3-uniform hypergraphs are reconstructible for n≥8, and any counterexample must be a twin pair of Steiner triple systems with v≡1,3 mod 6. The submission reads reconstruction as equality of the vertex-deleted deck with multiplicity and refutes it with an explicit 9-vertex pair.

**Decisive results.** X and Y are simple 3-uniform hypergraphs on Fin 9 with 28 edges each. same_deck gives an outer matching of deleted vertices and an inner vertex equivalence on each complement, so the decks agree with multiplicity; not_isomorphic excludes every vertex equivalence by proved degree/codegree invariants and exhaustive cases. X and Y are not Steiner because the pair {0,1} has codegree 2 in each, and steiner_clause_false negates the universal Steiner restriction. Thus both filed clauses are false; the 9-vertex hypotheses are satisfiable.

**Report correspondence.** The report's edge lists B, A_X, A_Y, the nine card permutations, the deck-equality table and the non-isomorphism case analysis match the Lean. The Lean also proves the bit encoding agrees with the printed unordered edge sets and checks the Steiner failure. No stronger prose claim than the formalized statements.

## Disposition

APPROVED — merged as PR 1095. The submission gives a complete, formalised disproof of conjecture 00000001683.
