# Solution Review — Conjecture 00000005029 (PR 1094)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261022111030`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000005029; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.19.0` and Mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** `verify.py` exited 0.

## Semantic audit

**Conjecture as filed.** Literal: at critical sparsity c=1 the almost-sure first-order limiting theory of G(n,c/n) is the explicit set of forest axioms. The submission reads 'limiting theory' as the set of first-order sentences whose probability tends to one, and refutes the necessary condition that the forest (acyclicity) sentence have probability tending to one.

**Decisive results.** The Lean builds the actual G(3(m+1),1/(3(m+1))) law as a uniform-coordinate pushforward to simple graphs, proves the independent Bernoulli edge-pattern law, counts the h^3 tripartite triangle events, bounds ordered overlaps by a Bonferroni inequality, and proves P(triangle) ≥ 1/50 and hence P(forest) ≤ 49/50 along every block size. Since this bound persists along an unbounded sequence, the forest/acyclicity probability does not tend to one, so the forest axioms cannot be the almost-sure limiting theory. The c=1 model and all hypotheses are satisfiable; the conclusion is the negation of the first conjunct.

**Report correspondence.** The report's Theorem, the triangle construction, the 1/50 bound, the 49/50 upper bound and the asymptotic argument match the Lean. The report explicitly says Lean formalizes the graph semantics of the sentence rather than separate first-order syntax, and the sentence-level logical bridge is paper-level. The supplementary verify.py ran and passed.

## Disposition

APPROVED — merged as PR 1094. The submission gives a complete, formalised disproof of conjecture 00000005029.
