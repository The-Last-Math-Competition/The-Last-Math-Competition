# Solution Review — Conjecture 00000006034 (PR 1175)

**Submission:** lizaixi01 — `lizaixi01_submission_20261024052500`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000006034; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.33.0` and Mathlib revision `db584cd6d46c92f209a44c0f1c829460d327499d`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** Literal reading of the final clause: in the nonfree case, the number of occurring isotropy types in the reduced space equals the number of coadjoint orbits. The filed text states no connectedness of the group and no properness of the moment map.

**Decisive results.** The theorem negates the final count clause with an actual Hamiltonian action of the compact (disconnected) group C_2 on the symplectic plane by ±1, with the zero moment map. The zero level is the whole plane, the reduced quotient has two isotropy types (stabilizer C_2 at the origin and trivial stabilizer elsewhere), and the coadjoint dual of the zero-dimensional Lie algebra is a singleton with one orbit. Thus the two cardinalities are 2 and 1. The action is genuinely symplectic and Hamiltonian, the moment map identity and equivariance are proved, and the hypotheses are satisfiable.

**Report correspondence.** Report and Lean agree: both present the C_2 action, the zero moment map, isotropy types 2, coadjoint orbits 1, and the same nonfree quotient. The report explicitly confines itself to the printed final count clause and disclaims connected-group or proper-moment-map variants; no stronger claim is made.

## Disposition

APPROVED — merged as PR 1175. The submission gives a complete, formalised disproof of conjecture 00000006034.
