# Solution Review — Conjecture 00000001216 (PR 1134)

**Submission:** lizaixi01 — `lizaixi01_submission_20261023033532`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000001216; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.33.0` and Mathlib revision `db584cd6d46c92f209a44c0f1c829460d327499d`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** The filed statement says the 2-angel has an explicit winning strategy on the cylinder Z×[0,2] (and an oblivious 7×7 version, and the half-plane case). The submission reads the cylinder as the three-row board Z×Fin(3) and models the angel with the full king-distance-≤2 horizontal bound, allowing arbitrary row changes and staying put; it gives the angel the first move each round.

**Decisive results.** Lean defines the actual infinite board Z×Fin(3), an injective fixed devil schedule `burn` that first burns columns −31,−30,30,31 (12 turns) and then all 177 interior squares of columns −29,…,29 (turns 12–188), and proves the angel's first 12 moves satisfy |x|≤24, so it is trapped in [−29,29]; `trapped_after_walls` proves confinement and `no_legal_190_moves` proves no 190th legal move exists after 189 burns. `explicit_devil_defeats_every_strategy` proves every full-history angel strategy is defeated by this schedule, and `no_angel_winning_strategy` negates survival against all oblivious devils. The model is stronger than the literal 2-angel (arbitrary vertical moves/staying), so it covers the strip and periodic cylinder; the hypothesis is satisfiable and the conclusion is the direct negation of the cylinder winning claim.

**Report correspondence.** The report/PDF state the same board, schedule, turn timing, wall confinement, 190-move obstruction and strategy quantification; the Lean theorems match. The report explicitly says the separate half-plane claim is not addressed.

## Disposition

APPROVED — merged as PR 1134. The submission gives a complete, formalised disproof of conjecture 00000001216.
