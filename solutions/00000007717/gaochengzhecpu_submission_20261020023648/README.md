# Disproof of Conjecture 00000007717

The square tessellation modulo the period subgroup 64Z x 4Z has degree four and square cells. Its real combinatorial Laplacian has the positive eigenvalue 2-2 cos(pi/32)<3/256. The actual least positive eigenvalue exists and is at most this value, contradicting the explicit claimed constant c=3/16 with D=4.

## Scope

Refutes the explicit optimal-constant conjunct, hence the full source conjunction. The source does not require a primitive period or the full translation group; 64Z x 4Z is an actual period subgroup. The graph is connected and simple, with degree D=4 and cell edge bound E=4. No weighted or normalized Laplacian is used, and no stronger general-family theorem is claimed as formalized.

## Formalization

Actual Mathlib SimpleGraph, quotient projection/kernel/adjacency, connectivity, degree and distinct square-cell vertices. A ZMod additive character yields a complex eigenvector; its real part is a nonzero eigenvector of the actual real lapMatrix. Lean proves the strict trigonometric bound and an IsLeast certificate for the actual positive eigenvalues. Supplementary exact Python checks construct the same finite graph and an independent Rayleigh witness.

## Reproduction

Inside lean/: `lake exe cache get`, `lake build`, and
`lake env lean -DwarningAsError=true Main.lean`.
Lean 4.19.0 and Mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b are pinned.
Compile the paper with `tectonic main.tex`.
Exact source, provenance, full fresh build and strict-check logs are included.
An author agent supplied a self-review; the parent separately reviewed the
complete proof and final PDF. No external independent review is claimed.
Run `python verify.py` for the exact supplementary graph check.
