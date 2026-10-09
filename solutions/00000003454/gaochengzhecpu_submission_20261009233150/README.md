# Conjecture 00000003454: the Bernstein deviation limit needs its position-dependent factor

For the smooth quadratic f(x)=(x-1/2)^2, the actual Bernstein error at x=1/2 equals 1/(4n) for every n>=1. Its n-scaled limit is 1/4 and its unscaled limit is zero, whereas the actual second derivative is two. Both readings of the source's asserted second-derivative limit fail.

## Scope

This refutes the statement that the deviation limit is the second derivative, under both the standard n-scaled Voronovskaya interpretation and the literal unscaled interpretation. The point is interior and the function is a smooth polynomial. The submission does not refute the classical corrected expression x(1-x)f''(x)/2, or a separately specified renormalization absent from the source; the order-1/n approximation error itself is valid in this example.

## Formalization

Lean uses Mathlib's actual bernsteinApproximation on continuous functions on the unit interval and the proved binomial-variance identity. It proves the polynomial smooth and computes its real second derivative, establishes the exact Bernstein sum for every positive approximation order, proves both actual Tendsto limits, and negates convergence to the actual second derivative by uniqueness of limits. The sequence is indexed by n+1 to keep every order positive.

## Reproduction

In `lean/`, run `lake build` and `lake env lean -DwarningAsError=true Main.lean`.
Lean 4.19.0 and Mathlib commit c44e0c8ee63ca166450922a373c7409c5d26b00b are pinned.
The manifest pins transitive dependencies with public Git URLs and no local paths.
On a new machine, fetch official cached dependencies with `lake exe cache get`.
Run `tectonic main.tex` from the submission directory to rebuild the PDF.
No auxiliary numerical script is required. `SOURCE.md` preserves the exact bilingual source.

The project's own Lean artifacts are rebuilt from scratch; only verified official dependency
artifacts are reused. Actual build commands, source hashes, axiom checks, and PDF inspections
are recorded in `verification/`. Author self-review and parent-agent adversarial review are
separate; no external independent review is claimed.
