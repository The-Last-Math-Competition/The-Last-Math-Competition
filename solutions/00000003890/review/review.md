# Solution Review — Conjecture 00000003890 (PR 1121)

**Submission:** lizaixi01 — `lizaixi01_submission_20261022232313`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000003890; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.33.0` and Mathlib revision `db584cd6d46c92f209a44c0f1c829460d327499d`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** The filed statement says the jumping set of a fixed ideal is always finite. The submission takes the fixed ideal (X) in F_2[X] and uses the standard generalized test ideal τ(I^t)=⋃_e (I^{ceil(t 2^{e+1})})^{[1/2^{e+1}]}.

**Decisive results.** For I=(X), τ(I^k)=(X^k) at integer k, and at t=k+1-2^{-(e+1)} the test ideal contains X^k while τ(I^{k+1})=(X^{k+1}) does not. positive_integer_jump proves a jump at every k+1, and infinitely_many_jumps proves the jump set is infinite. This directly negates the 'always finite' clause. The hypotheses are satisfiable (a fixed nonzero proper ideal).

**Report correspondence.** The report states the same definition, computation, and conclusion; the Lean theorems match. The report explicitly says the second clause about density in (0,1) is not addressed.

## Disposition

APPROVED — merged as PR 1121. The submission gives a complete, formalised proof of conjecture 00000003890.
