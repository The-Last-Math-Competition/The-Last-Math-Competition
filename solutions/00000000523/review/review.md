# Solution Review — Conjecture 00000000523 (PR 1137)

**Submission:** Galaxy-0 — `Galaxy-0_submission_20261022200800`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000000523; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.31.0`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** The filed clause says that for numerical semigroup rings the degree of the minimal polynomial of Frobenius on H¹_m(R) equals the multiplicity. The submission takes S=N=<1> (multiplicity 1), R=F2[t], m=(t), and the concrete Čech model H¹_m(R)=F2[t,t⁻¹]/F2[t] with Frobenius a(t)↦a(t)².

**Decisive results.** The classes e_j=[t^{-j}] form a basis and F(e_j)=e_{2j}, so P(F)e_1=Σ c_r e_{2^r}; the exponents 2^r are distinct, hence every nonzero polynomial P has P(F)e_1≠0. Thus F has no nonzero annihilating polynomial, in particular no minimal polynomial of degree 1=multiplicity. The conclusion is the negation of the filed equality. The Lean constructs the Laurent quotient, descends F, and proves the coefficient extraction for every finite coefficient list.

**Report correspondence.** Report and Lean agree. The report proves the same non-annihilation theorem and notes the formalization uses finite Laurent polynomials, not formal power series; the formal-power-series extension is prose only and not needed for the stated convention. No stronger formal claim is made.

## Disposition

APPROVED — merged as PR 1137. The submission gives a complete, formalised disproof of conjecture 00000000523.
