# Solution Review — Conjecture 00000001385 (PR 1150)

**Submission:** lizaixi01 — `lizaixi01_submission_20261023070501`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-11-06

## Checklist results

- **Eligibility and scope.** The submission uses the correct personal folder for conjecture 00000001385; the conjecture was open, and the pull request changed no conjecture, README, leaderboard, metadata, or other file.
- **Report and PDF.** The complete official statement of the conjecture, the LaTeX report, and the submitted PDF were read in full. The LaTeX source was independently recompiled with `pdflatex`; it compiled cleanly, and the theorem statements in the submitted PDF match the source and the Lean declarations.
- **Lean project.** The submission's Lean project was rebuilt from a clean copy of the frozen sources with its own module names, `lakefile`, lean-toolchain `v4.33.0` and Mathlib revision `db584cd6d46c92f209a44c0f1c829460d327499d`. The build completed with no `sorry`, no `native_decide`, no custom `axiom`/`constant`, no `unsafe`, `opaque`, `extern` or `implemented_by` declaration.
- **Axiom audit.** The transitive axiom set of the decisive declarations is contained in {`propext`, `Classical.choice`, `Quot.sound`}; no `sorryAx` is reachable.
- **Auxiliary code.** No additional auxiliary computation was required.

## Semantic audit

**Conjecture as filed.** N_T(λ) is the Hilbert dimension of the eigenspace for eigenvalues ≤ λ; the clause at issue says that once N_T is infinite at some λ, every larger λ has value 2^ℵ₀. The submission takes the literal threshold-function reading (1 and 2 are distinct real thresholds, not two distinct eigenvalues).

**Decisive results.** For the actual identity measure-preserving map on the probability circle, the Koopman operator U is the identity and its only eigenvalue is 1, with eigenspace all of L²(AddCircle 1). The Fourier Hilbert basis is indexed by ℤ and every Hilbert basis of this space is proved to have cardinality ℵ₀; the cutoff subspace at every a≥1 is top. Hence Nreal(1)=Nreal(2)=ℵ₀. `InfiniteJump` would force Nreal(2)=2^ℵ₀, contradicting Cantor's strict inequality ℵ₀<2^ℵ₀. The example is a genuine measure-preserving transformation, the eigenspaces are actual, and dimension is genuine Hilbert dimension (not Hamel rank).

**Report correspondence.** The report and Lean agree: the report states the identity-circle example, U=id, unique eigenvalue 1, Hilbert-basis cardinality ℵ₀, and N(1)=N(2)=ℵ₀≠2^ℵ₀. `true_eigenspace`, `only_eigenvalue`, `all_basis_cardinality`, `top_hilbertDim`, `Nreal_value` and `real_counterexample` formalize exactly those claims, and the same is done independently for the modulus cutoff. No stronger prose claim is made.

## Disposition

APPROVED — merged as PR 1150. The submission gives a complete, formalised disproof of conjecture 00000001385.
