# Solution Review — Conjecture 00000003883 (PR 1119)

**Submission:** lizaixi01 — `lizaixi01_submission_20261022230649`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000003883; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.33.0` and Mathlib revision `db584cd6d46c92f209a44c0f1c829460d327499d`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** The filed statement claims fpt(x^a,y^b)=min(a,b) when gcd(a,b)=1 and p∤min(a,b). The submission uses the standard Frobenius-limit definition of fpt at the origin and takes a=b=1 over F_2.

**Decisive results.** For (x,y) in F_2[x,y], m^{[2^e]}=(x^{2^e},y^{2^e}); m^r⊄m^{[2^e]} iff r≤2(2^e-1), so ν_{2^e}=2(2^e-1) and fpt=2. The conjecture predicts min(1,1)=1 because 2∤1. counterexample formalizes a=1,b=1 with the actual limit and the inequality fpt≠min(a,b). The hypotheses are satisfiable and the conclusion is the negation of the universal formula.

**Report correspondence.** The report states the same standard definition, the computation, and the counterexample; the Lean theorem matches. The report explicitly notes that the general equivalence with the test-ideal wording is not formalized.

## Disposition

APPROVED — merged as PR 1119. The submission gives a complete, formalised proof of conjecture 00000003883.
