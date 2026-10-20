# Disproof of Conjecture 00000009527

For actual qubit channels D(A)=tr(A)I/2 and Z(A)=diag(A00,A11), the source order satisfies D<=Z for every finite ensemble, including arbitrary noncommuting input density states. Both have normalized Kraus families. Depolarization has Holevo information zero, while dephasing has nonnegative Holevo information by scalar Jensen after proving the actual spectral diagonal-entropy formula. The equiprobable orthogonal pure-state ensemble has Holevo values log 2 and 0, so not Z<=D. Thus D has a strict successor and is not maximal.

## Scope

Refutes the maximal-element conjunct in precisely the direction defined in the bilingual source. Both channels have the same qubit input and output spaces. The strict comparison survives quotienting by mutual less-noisy equivalence; it does not merely confuse maximal and greatest elements. Distinct reset maps additionally refute antisymmetry on literal channel space. The separate broadcast-capacity expression is not assessed.

## Formalization

Lean uses actual complex matrices, PosSemidef density states, spectral von Neumann entropy from Hermitian eigenvalues and the normalized finite Kraus characterization of CPTP channels. It proves the spectral diagonal-entropy identity, all-input Kraus action formulas, all-finite-ensemble Jensen comparison and the strict orthogonal-state witness. The actual reset-channel antisymmetry counterexample is also formalized. Exact rational Python checks supplement the arbitrary-complex-input Lean identities; no numerical entropy or capacity oracle is used.

## Reproduction

Inside `lean/`: `lake exe cache get`, `lake build`, and
`lake env lean -DwarningAsError=true Main.lean`.
Lean 4.19.0 and Mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b` are pinned.
Run `python verify.py` (standard library only), and `tectonic main.tex`.
Exact source, provenance, actual build logs, hashes and final PDF review are
included. An author agent performed a self-review; the parent separately
reviewed the complete proof and materials. No external independent review
is claimed. These elementary channel facts are not claimed as novel.
