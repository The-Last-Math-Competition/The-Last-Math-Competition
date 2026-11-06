# Solution Review — Conjecture 00000003901 (PR 1155)

**Submission:** lizaixi01 — `lizaixi01_submission_20261023085504`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000003901; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.33.0` and Mathlib revision `db584cd6d46c92f209a44c0f1c829460d327499d`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** The source defines the Frobenius exponent quotient as I^{[p^e]}/I and claims the length growth has leading exponent n-1 for every ideal in an n-dimensional ring. Because I^{[q]}⊆I for every ideal and q≥1, the printed direction is not an ordinary quotient; the submission uses the natural corrected quotient I/I^{[q]} and separately proves the printed direction is not nested.

**Decisive results.** In R=F2[[X]] (Krull dimension 1, maximal ideal I=(X)) and q=2^e, the actual iterated Frobenius image is I^{[q]}=(X^q). The R-linear map f↦Xf identifies R/(X^k) with I/(X^{k+1}), and Mathlib's DVR quotient-length theorem gives length_R(I/I^{[q]})=q-1=2^e-1. Thus the length grows like 2^e, not like (2^e)^{n-1}=(2^e)^0=1: `proposed_dimension_minus_one_exponent_fails` negates the IsBigO bound at the conjectured scale, and `no_finite_leading_coefficient` negates every finite normalized limit. n=1 is within the source's 'every ideal in an n-dimensional ring', and I is a genuine ideal. The only change is the necessary correction of the reversed quotient direction, which is disclosed and independently proved non-nested (`reversed_quotient_not_nested`).

**Report correspondence.** The report and Lean agree: the report states the power-series DVR, Krull dimension 1, maximal ideal (X), the iterated Frobenius power (X^{2^e}), the linear equivalence R/(X^k)≅I/(X^{k+1}), the length 2^e-1, the cofinal unboundedness and the failure of the n-1 exponent/finite coefficient. `frobeniusPower_eq`, `quotientEquiv`, `actual_frobenius_length`, `length_cofinally_unbounded` and `actual_counterexample` formalize those claims. The report explicitly says the printed quotient direction is not defined and that the substantive proof is for I/I^{[q]}.

## Disposition

APPROVED — merged as PR 1155. The submission gives a complete, formalised disproof of conjecture 00000003901.
