# Solution Review — Conjecture 00000008551 (PR 1109)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261022114211`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000008551; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.19.0` and Mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** The source says the roots of the chromatic polynomial of a geometric lattice alternate in sign (and makes a further modulus/critical-exponent claim). The submission reads the lattice chromatic polynomial as the standard characteristic polynomial chi_L(t)=sum_x mu(0,x) t^(r-r(x)), and also checks the graph chromatic polynomial of the bond lattice. 'Geometric' is read as finite, bounded, atomistic and upper-semimodular.

**Decisive results.** The partition lattice Pi_3 is finite, modular and atomistic, so geometric. Its Mobius values are 1,-1,-1,-1,2 and its characteristic polynomial is (t-1)(t-2). The consecutive distinct nonzero roots 1 and 2 are both positive, violating the necessary alternating condition a*b<0. The triangle K_3 has chromatic polynomial t(t-1)(t-2) with the same two consecutive positive nonzero roots. RootSignClause is the universal necessary condition over geometric lattices and disprove_root_sign_clause exhibits Pi_3 as a counterexample; GraphRootSignClause is similarly negated by K_3. The second modulus clause is not addressed because refuting the first conjunct already disproves the conjunction.

**Report correspondence.** The report proves exactly the same Pi_3 computation, rank and Mobius recurrence, factorization and root set, and the K_3 coloring count. It explicitly says coefficient alternation is a different true statement and that the modulus clauses are not needed; Lean's RootSignClause/GraphRootSignClause match those claims.

## Disposition

APPROVED — merged as PR 1109. The submission gives a complete, formalised disproof of conjecture 00000008551.
