# Conjecture 00000004157: Diagonal solutions do not give the proposed VMVT coefficient

For k=1,s=2 in the claimed range, the actual count is J_(2,1)(N)=(2N^3+N)/3, while the diagonal count is D_2(N)=2N^2-N. The true cubic coefficient is 2/3 and the diagonal contribution on the same cubic scale is zero; the diagonal count itself has quadratic leading coefficient 2. A supplementary degree-two example gives J_(6,2)(N)>=N^9/49 but D_6(N)<=720N^6.

## Scope and formal correspondence

The exact coefficient counterexample uses k=1,s=2, with s=k(k+1); the source contains no exclusion of degree one. Both the same-scale diagonal contribution and the factorial coefficient of the diagonal count itself are checked. The k=2,s=6 argument separately refutes diagonal main-term dominance within the claimed range; it does not claim to compute an exact degree-two asymptotic coefficient. These are standard unweighted ordered VMVT solution counts; no unstated restriction or normalization is added.

LinearSolutions is the actual finite subtype of four residues satisfying a+b=c+d, with a proved bridge to the interval 1,...,N. An explicit injective and surjective map partitions this set by the sign of a-c and proves its exact cardinality. The actual diagonal set is the union of the identity and transposition families, and its intersection is counted exactly. J21_exact, D21_exact, and three Tendsto theorems give the polynomial counts and coefficients. For degree two, the genuine moment map from six-tuples is equated with the two VMVT equations. Its actual fibers yield the Cauchy-Schwarz lower bound, and actual permutation pairs give the diagonal upper bound.

The decisive same-scale comparison is J_(2,1)(N)/N^3 -> 2/3 while D_2(N)/N^3 -> 0. The additional limit D_2(N)/N^2 -> 2 checks the factorial interpretation as well. The exact count and the same-scale comparison are not inferred merely from the existence of non-diagonal solutions.

## Files and reproduction

- `main.tex` and `main.pdf`: complete argument and formal correspondence.
- `SOURCE.md`: exact bilingual source; its commit and SHA-256 are recorded under `verification/`.
- `lean/`: portable Lean 4.19.0 project with Mathlib pinned to `c44e0c8ee63ca166450922a373c7409c5d26b00b`.
- `verification/`: actual clean-build logs, theorem dependencies, PDF compilation and rendering records, and reviews.

Inside `lean/`, run `lake build` and `lake env lean -DwarningAsError=true Main.lean`. On a new machine, `lake exe cache get` retrieves the pinned official dependency artifacts. From the submission directory, `tectonic main.tex` reproduces the PDF. No auxiliary numerical script is needed.

Only the official commit-pinned dependency cache is reused; the submission itself is compiled in a fresh directory without its prior build artifacts. The audit excludes proof gaps, added axioms, and native computation shortcuts. Author self-review and parent review are distinct; no external independent review is claimed.
