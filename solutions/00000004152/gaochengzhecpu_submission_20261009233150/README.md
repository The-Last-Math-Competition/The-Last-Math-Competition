# Conjecture 00000004152: No negative Waring singular series

Every finite real local representation-density limit is nonnegative, and therefore every defined finite real Euler-product Waring singular series is nonnegative. Fourth powers cannot supply a negative value or a negative local factor.

## Scope and formal correspondence

Ordinary Euler products of limits of normalized residue-solution counts, as specified by the source. Convergence is only assumed when a purported finite value is under discussion; no regularized divergent value is introduced. The proof treats all exponents and separately rules out both negative fourth-power assertions.

WaringSolutions is the actual finite subtype of tuples in (Fin q)^s satisfying the sum-of-powers congruence. Nat.card counts those tuples; density uses the standard q^(s-1) normalization. Local factors are Filter.Tendsto limits with no sign assumption. The finite products range over actual primes, and their real limits are proved nonnegative.

## Files and reproduction

- `main.tex` and `main.pdf`: full argument and formal correspondence.
- `SOURCE.md`: exact bilingual source; its commit and SHA-256 are recorded under `verification/`.
- `lean/`: portable Lean 4.19.0 project with Mathlib pinned to `c44e0c8ee63ca166450922a373c7409c5d26b00b`.
- `verification/`: actual clean-build logs, theorem dependencies, PDF compilation and rendering records, and reviews.

Inside `lean/`, run `lake build` and `lake env lean -DwarningAsError=true Main.lean`. On a new machine, `lake exe cache get` retrieves the pinned official dependency artifacts. From the submission directory, `tectonic main.tex` reproduces the PDF. No auxiliary numerical script is needed for this exact argument.

Only the official commit-pinned dependency cache is reused; the submission itself is compiled in a fresh directory without its prior build artifacts. The audit excludes proof gaps, added axioms, and native computation shortcuts. Author self-review and parent review are distinct; no external independent review is claimed.
