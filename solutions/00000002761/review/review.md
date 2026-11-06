# Solution Review — Conjecture 00000002761 (PR 1174)

**Submission:** lizaixi01 — `lizaixi01_submission_20261024050144`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000002761; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.33.0` and Mathlib revision `db584cd6d46c92f209a44c0f1c829460d327499d`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** Literal reading: over Q, for M_3, the minimum degree of a positive-degree central polynomial (nonidentity, every matrix evaluation central) is asserted to be n^2=9. Central polynomials are allowed in any finite number of variables.

**Decisive results.** The theorem negates the n=3 degree clause. It constructs an explicit homogeneous degree-8 element of the free algebra on six variables, proves all its words have length 8 and its constant coefficient is zero, proves every evaluation commutes with every matrix, and exhibits a witness evaluation equal to 2I_3 (so it is not an identity). Hence the attained minimum over all positive-degree central polynomials satisfies d_min ≤ 8 < 9 = 3^2, so minimalCentralDegree ≠ 9. The hypotheses are satisfiable and the conclusion is a negation of the claimed exact minimum for M_3.

**Report correspondence.** Report and Lean agree. The report states the degree-8 polynomial, the 2I_3 witness, and d_min ≤ 8 < 9, and explicitly does not claim d_min=8 or address the moduli/generation clauses. No stronger prose claim is made.

## Disposition

APPROVED — merged as PR 1174. The submission gives a complete, formalised disproof of conjecture 00000002761.
