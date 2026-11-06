# Solution Review — Conjecture 00000008333 (PR 1116)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261022121830`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000008333; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.19.0` and Mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** The source's first clause says the distribution of Markov numbers grows like c x^(1/2). The submission reads this as the cumulative count M(X) of distinct positive Markov numbers <=X satisfying M(X)~c sqrt(X) with c>0, and refutes that clause; the other three source clauses are not needed.

**Decisive results.** Lean defines the actual Markov equation over positive naturals, the finite count M(X), and proves every Markov number is 1, 2, or the largest coordinate of a node in the standard Markov tree. It bounds the number of nodes with largest coordinate <=64^n by 2+3(6n+1)^2 2^(2n+1), hence M(64^n)<=that and M(64^n)/8^n->0. If M(X)/sqrt(X)->c>0, the subsequence X=64^n would also tend to c, contradicting the zero limit. Thus no positive c gives the claimed sqrt growth; the hypotheses are satisfiable and the conclusion negates the first conjunct of the source.

**Report correspondence.** The report states the same cumulative counting interpretation, tree descent/coverage, explicit bound, zero subsequence limit and final negation. Lean's count_bound, count_subsequence_zero and conjecture_8333_false match; the report explicitly disclaims the prime, Frobenius-uniqueness and random-walk clauses.

## Disposition

APPROVED — merged as PR 1116. The submission gives a complete, formalised disproof of conjecture 00000008333.
