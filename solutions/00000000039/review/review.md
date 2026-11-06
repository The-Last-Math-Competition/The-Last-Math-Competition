# Solution Review — Conjecture 00000000039 (PR 1176)

**Submission:** lizaixi01 — `lizaixi01_submission_20261024060922`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000000039; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.33.0` and Mathlib revision `db584cd6d46c92f209a44c0f1c829460d327499d`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** Literal reading: every sufficiently large odd natural number N is p+2^a+2^b with p an actual prime and a,b≥0. The submission uses the conventional prime meaning of p; arbitrary integer p would trivialize the statement.

**Decisive results.** The theorem is exactly the negation of the filed eventual-representability assertion. It constructs an explicit odd sequence N_k (a Crocker-type Fermat-product construction with a finite 28-class exponent covering) such that for every cutoff L there is N>L not representable as p+2^a+2^b for any prime p and a,b∈ℕ. The construction handles distinct, equal and zero exponents, uses genuine modular inverses and divisibility obstructions, and proves N_k is odd and arbitrarily large. All arithmetic hypotheses are concrete and satisfiable.

**Report correspondence.** Report and Lean agree: both state the arbitrary-cutoff counterexample and the negation of eventual representability, with the same 28-class covering data, Fermat products and divisibility arguments. No stronger prose claim is made.

## Disposition

APPROVED — merged as PR 1176. The submission gives a complete, formalised disproof of conjecture 00000000039.
