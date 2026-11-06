# Problem 00000007733: no positive second Stein discrepancy value

This submission refutes only the printed “next-smallest value” clause under the standard fixed unit-semicircle target, V(x)=x²/2. “Next” means the next distinct value above zero. The printed class consists of all atomless probability distributions supported in [-2,2], with support containment and no variance-one constraint.

The actual scaled semicircle laws μ_s, 0<s≤1, have genuine full-kernel discrepancy Σ*(μ_s|V)=1−s². For every positive c, choosing ε=min(c/4,1/4) and s=1−ε gives an actual atomless law, a bounded self-adjoint coordinate operator and 0<Σ*<c. Therefore no strictly positive second distinct value can exist in the printed class.

Atomic minimizers and unspecified Jacobi-family classification are outside this refutation. Exact-full-support, variance-normalized, stationary-value or other revised statements are outside its scope. Free Fisher information is not identified with Stein discrepancy.

## Actual mathematical objects

- The probability measure ν has the actual density (2/π)√(1−x²) on [-1,1], and μ_s is its native pushforward by x↦2sx. Probability, atomlessness, support bounds, mean and second moment are proved from these measures. A native change-of-variables identity identifies every continuous test against μ_1 with the standard unit Wigner density on [-2,2].
- Native Chebyshev weighted integrals, a proved bivariate convolution identity and a native polynomial-sequence basis establish the true free integration-by-parts identity for every complex polynomial. The derivative convention on the diagonal and actual product diagonal-null property are present. All moments are actual integrals and their full recurrence is proved by Fubini.
- Stein kernels range over the entire native complex L²(μ_s⊗μ_s), with every complex polynomial test. No restriction to real, constant, symmetric, polynomial or finite-dimensional kernels is imposed. The constant s² is proved admissible; every admissible kernel has mean s², and Cauchy–Schwarz proves the full norm lower bound. The true real infimum is explicitly nonempty and bounded below before use; the constant attains it.
- Multiplication by x on native complex L²(μ_s) is constructed as an actual continuous linear operator. It is self-adjoint and has norm at most2. The actual vector state is bounded, positive and unital; its restriction to polynomial operators is proved tracial, and all complex polynomial distribution identities are proved.

## Definition boundary

The law-level kernel definition is Fathi–Nelson, arXiv:1605.05828v1, Definition1.8 and Section4. We formalize its actual one-variable measure/product-measure formulation directly, with native complex L² inner products and the complete kernel domain. A general von Neumann algebra/GNS/tensor reconstruction and a general spectral functional-calculus reconstruction are not repeated. The concrete coordinate operators and complete polynomial distribution identities are proved, and no extra Lean axiom is introduced for a reconstruction.

Primary PDF: https://arxiv.org/pdf/1605.05828v1 . Actual printed pages4/7/13/14 were read, and full pages7/14 were rendered and visually checked. The reference is to that exact20-page 2016 version.

## Files and reproducibility

- `SOURCE.md`: the complete original bilingual statement at the recorded upstream commit.
- `report.tex` and `report.pdf`: complete mathematical argument and explicit scope.
- `lean/`: the complete pinned Lean project.
- `evidence/`: actual qualification, compilation, ordinary exhaustive axiom coverage, fresh-kernel and execution/mask receipts.
- `SHA256SUMS.json`: the actual package hash manifest.

Original source LF SHA256: `099c327bf586477cd4d9dc8950a6230559a28205a3cfc3c1c9ab2b2c5345abdb`.

The project pins Lean4.33.0 and Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`. From the package directory, run:

```sh
cd lean
lean --version
lake build +Main
lake env lean -DwarningAsError=true Check.lean
lake env leanchecker --fresh Main
```

After the separate version command, `bash lean/verify.sh` from the package directory performs the remaining three steps. The script changes into its own directory.

The dynamic ordinary `#print axioms` check enumerates every owned namespace declaration, including generated/private declarations, and checks the complete explicit-name list. The only allowed foundational axioms are `propext`, `Classical.choice` and `Quot.sound`. There is no `sorry`, `native_decide` or added axiom.

Full native infimum theorem: `TLMC7733.discrepancy_eq`.
Actual operator/measure counterexample for every positive threshold: `TLMC7733.operator_laws_have_no_positive_next_value`.
Logical positive-gap negation: `TLMC7733.no_positive_gap_on_admissible_family`.

CPU affinity is assigned [0,2] with two Lean threads. Original execution records, fresh-kernel logs and actual thread-mask samples are retained. These production timings are diagnostic only; no controlled causal efficiency gain is claimed. Submission remains subject to organizer review.
