# Disproof of Conjecture 00000009778

The actual L2(0,1) Volterra singular values are s_n=1/[pi(n-1/2)], so n^2(s_n-1/(pi*n)) tends to 1/(2*pi), not zero. This excludes the necessary third-order condition for the claimed odd-only Poincare expansion and survives every integer change of starting index.

## Scope

Refutes the odd-only correction clause, not existence of a full unrestricted expansion. The paper gives the actual compact-operator, adjoint, regularity/ODE and exhaustive sorted spectrum proof. That L2 spectral identification is an explicit substantive mathematical bridge outside Lean, also supported by Opmeer 2020 Example31. The supplied project does not claim a complete Lean construction of the L2 operator spectrum.

## Formalization

Lean proves actual forward/backward interval-integral cosine and Gram-mode identities, the half-integer boundary condition, the correct nonnegative square root of the exact Gram spectral formula, and the genuine all-index asymptotic consequence for every sequence eventually satisfying that formula. It defines only the standard necessary third-order odd Poincare truncation, proves that it forces the n^2 difference to zero, and contradicts the actual nonzero limit. Every integer offset is covered without assuming a particular zero/one indexing convention. Pointwise integral identities are explicitly not represented as proving L2 completeness or ordered spectral identification; those are proved mathematically in the paper. An independent exact rational verifier checks finite geometric-remainder identities, second/third coefficients and integer shifts; it is not a spectral oracle.

## Reproduction

Inside lean/: `lake exe cache get`, `lake build`, and
`lake env lean -DwarningAsError=true Main.lean`.
Lean 4.19.0 and Mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b are pinned.
Compile `main.tex` with Tectonic. Any supplementary root-level Python
programs are run with Python 3; none is a computation oracle for Lean.
The exact bilingual source, provenance, actual fresh-build logs, axiom
audit, artifact hashes and all-page PDF review are included. The author
agent supplied a self-review; the parent reviewed the entire frozen proof
and final artifacts separately. No external independent review is claimed.
