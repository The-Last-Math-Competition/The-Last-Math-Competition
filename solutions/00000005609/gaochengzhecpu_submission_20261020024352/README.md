# Disproof of Conjecture 00000005609

For each t>=1 the actual full-rank discrete Euclidean lattice Lambda_t={(tm,n,p):m,n,p integers} has packing radius 1/2 and covering radius sqrt(t^2+2)/2. Their ratio sqrt(t^2+2) is unbounded. Thus its three-dimensional spectrum cannot have the asserted finite upper endpoint attained by a cubic lattice.

## Scope

Refutes only the attained-upper-endpoint conjunct. An unbounded spectrum cannot have a finite maximum attained by any lattice. Unboundedness alone is not claimed to rule out a closed half-infinite interval. The separate BCC minimum claim is not assessed. No bounded aspect ratio or well-roundedness restriction appears in the source.

## Formalization

Actual Mathlib EuclideanSpace R (Fin 3), an explicit additive subgroup proved discrete and of full real span, and exact Euclidean norms. Packing is the supremum of all admissible radii, with a proved pairwise-distance interpretation. Covering is the infimum of radii whose closed lattice balls cover all space. Coordinate rounding and a half-integer centre prove the exact covering extremum; the shortest vector proves the exact packing extremum. Lean proves unboundedness with discrete/full-rank witnesses and directly negates a universal finite upper bound. No numerical oracle or auxiliary program is required.

## Reproduction

Inside lean/: `lake exe cache get`, `lake build`, and
`lake env lean -DwarningAsError=true Main.lean`.
Lean 4.19.0 and Mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b are pinned.
Compile the paper with `tectonic main.tex`.
Exact source, provenance, full fresh build and strict-check logs are included.
An author agent supplied a self-review; the parent separately reviewed the
complete proof and final PDF. No external independent review is claimed.
