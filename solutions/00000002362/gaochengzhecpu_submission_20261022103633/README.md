# Disproof of Conjecture 00000002362

On genuine Euclidean C^2, A_N=I+N E12 are all sectorial of angle zero and belong to the same Sect(pi/3) class. The same admissible rational H0-infinity test g(z)=z/(1+z)^3 on Sigma(pi/2) has scalar sup norm at most one but g(A_N)=I/8-N E12/16 has unbounded operator norm.

## Scope

Refutes a finite calculus bound depending only on the sector angles, already at fixed angles and in fixed dimension. Each individual operator has a bounded full calculus, as the paper proves by the Jordan formula and Cauchy estimate. No claim is made against bounds that also depend on resolvent or similarity constants. The additional claimed angle-to-pi singularity need not be analyzed after the angle-only assertion fails.

## Formalization

Lean proves genuine Euclidean matrix operator norms, spectrum containment and the complete sectorial resolvent condition for every larger sector. It proves actual scalar holomorphy and H0-infinity decay on the fixed half-plane, actual invertible rational functional calculus identities and the growing norm. A norm-preserving star algebra equivalence explicitly transfers spectrum, units, resolvents, sectoriality and rational values to true bounded complex-linear operators on Euclidean C^2. The final theorem refutes any finite bound on this necessary rational-test consequence of an H-infinity calculus estimate. The full contour calculus and its standard rational consistency are explained mathematically in the paper, not redefined or claimed fully formalized.

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
