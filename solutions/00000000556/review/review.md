# Solution Review — Conjecture 00000000556 (PR 1189)

**Submission:** lizaixi01 — `lizaixi01_submission_20261024143841`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000000556; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.33.0` and Mathlib revision `db584cd6d46c92f209a44c0f1c829460d327499d`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** Literal general biconditional: HH^1(Λ) = 0 iff Λ is representation-finite and rigid, with no restriction to string algebras (the parenthetical says the characterization is verified for string algebras, not restricted to them). Take the four-leaf extended-D4 path algebra A over Q.

**Decisive results.** The theorem constructs A as the 9-dimensional square-zero Q-algebra Q^5 ⋉ Q^4 and identifies it with the path algebra of the four-leaf star. It proves HH^1(A) = 0 by showing every derivation is inner, and constructs a one-parameter family M_t (t ∈ Q) of 6-dimensional indecomposable modules with Hom(M_t, M_s) = 0 for t ≠ s, giving infinitely many isomorphism classes. Thus HH^1(A) = 0 but A is not representation-finite; the biconditional fails for every possible rigidity predicate, as printed_iff_impossible states. The hypotheses are satisfiable and the conclusion is the negation of the printed implication.

**Report correspondence.** The report's theorem, derivation corrector, module family, endomorphism classification and full quotient injection match the Lean. The report explicitly notes the algebra is not a string algebra and does not claim a string-algebra-restricted version; Lean and report agree.

## Disposition

APPROVED — merged as PR 1189. The submission gives a complete, formalised disproof of conjecture 00000000556.
