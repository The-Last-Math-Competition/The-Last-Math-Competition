# Conjecture 00000000069: disproof of the stated L¹ rate

The supplied English and Chinese statements specify best **L¹** polynomial approximation of |x| on [-1,1]. For the ordinary unweighted Lebesgue integral and degree at most n, this project proves

\[
0 \le E_{8m+2}^* \le 128/(2m+1)^2.
\]
Consequently no nonzero real B satisfies E_n* ~ B/n in the ordinary ratio sense. This refutes a necessary clause of the statement as written. The bound is sufficient for this contradiction; no sharp global asymptotic rate or optimal constant is claimed. It does not assign or import a numerical Bernstein constant, substitute the uniform norm, or claim a result about the uniform-norm Bernstein constant.

## Read and verify

- `report.tex`: complete English mathematical report.
- `source/original.md`: exact bilingual original.
- `TLMC69/Main.lean`: final theorem `TLMC69.conjecture69_disproof`.
- `verification/author-verification.log`: author rebuild, warning replay, and all authored axiom dependencies.
- `verification/verify.sh`: reproduces the verification.

With Lean 4.19.0 selected and the pinned dependencies available:

```sh
lake build
sh verification/verify.sh
```

For a fresh checkout, obtain the dependencies using the checked-in manifest. Mathlib's optional cache command can supply its compiled dependencies; this is a setup convenience, not a proof step:

```sh
lake exe cache get
lake build
sh verification/verify.sh
```

The root `lake-manifest.json` pins Mathlib v4.19.0 to revision `c44e0c8ee63ca166450922a373c7409c5d26b00b` and also pins its transitive packages. `lean-toolchain` pins `leanprover/lean4:v4.19.0`. `lakefile.lean` sets warnings as errors. The private author environment used an unchanged copy of that stock Mathlib tree; no external or patched mathematics is needed.

## What is formally covered

The infimum is over **all real polynomials** with natural degree at most n. The zero polynomial is included at every degree. Its error is the Lebesgue interval integral of `abs (abs x - p.eval x)` from -1 to 1. The explicit competitors are genuine polynomials, and their degree bounds, normalization positivity, exact L¹ error, moment estimates, infimum comparison, and cofinal-subsequence limit argument are all proved.

`HasInverseLinearRate B` is defined as `B ≠ 0` together with convergence of `bestError n / (B / n)` to 1. The final theorem negates the existence of any such B. B=0 is excluded by the ordinary meaning of asymptotic equivalence, not by a numerical assumption.

The proof does not require deciding the informal “closed form” or “transcendence can be decided” clauses: the stated necessary rate is already false. Normalizing Lebesgue measure by 1/2 only multiplies all errors by 1/2 and gives the same contradiction.

## Files

| Module | Role |
| --- | --- |
| `TLMC69/Kernel.lean` | Polynomial recurrence, degree/parity, sine identity, global and local bounds |
| `TLMC69/Primitive.lean` | Genuine polynomial antiderivative, degree, oddness, integral identity |
| `TLMC69/KernelIntegrals.lean` | Mass positivity/lower bound and second-moment upper bound |
| `TLMC69/Approximation.lean` | True L¹ error and best-error definitions, polynomial competitor, exact L¹ identity |
| `TLMC69/Main.lean` | Degree-constrained infimum estimates and final asymptotic contradiction |
| `verification/Axioms.lean` | Prints logical dependencies of every authored lemma/theorem |
| `verification/check_sources.py` | Exact-input hash checks and authored source inventory; no mathematical computation |

All authored theorem axiom dependencies are limited to ordinary Lean foundations (`propext`, `Classical.choice`, `Quot.sound`). No `sorry`, `admit`, `native_decide`, custom axiom, or assumed approximation bridge appears in the proof sources. No auxiliary numerical computation is required. All accompanying verification code is included and run.

The report PDF is to be compiled and visually checked separately from Lean verification. Neither this author package nor a successful Lean build constitutes competition acceptance. Eligibility, independent review, and publication are handled separately.
