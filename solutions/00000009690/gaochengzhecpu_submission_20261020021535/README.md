# Disproof of Conjecture 00000009690

For fixed algebraic arguments 2 and 3, Dirichlet approximation produces integer forms a log 2 - b log 3 with nonzero absolute value at most log 3/(N+1) and coefficient bounds a<=N, b<=N+1. Their actual height is H=max(3,a,b). For every positive C and actual-height cutoff H0, the proof constructs a form with H>=H0 and absolute value below C/(log H)^2. Hence the proposed bound fails already at epsilon=1, even with arbitrary implied constants and sufficiently-large-height qualifications.

## Scope

Refutes the literal (log B)^(-1-epsilon) lower bound. The two algebraic arguments remain fixed and coefficients are integers, a subclass of rational coefficients. The proof uses the actual standard coefficient height max(3,|a|,|-b|), not an inflated bound, and proves actual heights are arbitrarily large. It does not determine an optimal true exponent in a corrected power-of-B bound.

## Formalization

Lean uses the actual real logarithm. Nonvanishing follows by logarithm injectivity, equality of natural prime powers and divisibility. A proved Mathlib Dirichlet theorem supplies approximations; all coefficient and sign conditions are derived. Analytic limits and a finite-small-form lower bound give counterexamples beyond every actual height cutoff. The final theorem negates the claimed uniform lower bound. Exact rational-interval Python examples are supplementary; no numerical computation certifies the general theorem.

## Reproduction

Inside `lean/`: `lake exe cache get`, `lake build`, and
`lake env lean -DwarningAsError=true Main.lean`.
Lean 4.19.0 and Mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b` are pinned.
Run `python verify.py` using only the standard library, and
`tectonic main.tex` for the PDF.

Exact source, provenance, actual build logs, hashes and PDF inspection
records are included. Review was solo adversarial self-review; there
was no independent reviewer or subagent.
