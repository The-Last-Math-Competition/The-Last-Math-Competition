# Disproof of Conjecture 00000000998

On the actual three-qubit observable algebra M8(C), the complex-linear transpose map has ordinary induced norm one and a genuinely finite completely bounded norm between eight and 64. An explicit 64-by-64 swap matrix has Euclidean operator norm one, while its blockwise transpose has an actual nonzero Euclidean eigenvector of eigenvalue eight. Thus the cb/ordinary ratio is at least eight, exceeding sqrt(2).

## Scope

Refutes the claimed supremum value by proving sqrt(2) is not even an upper bound for the ratios of nonzero completely bounded maps. The source does not impose complete positivity. Transposition is not called a quantum channel. Only 8<=cbNorm(transpose)<=64 and ordinary norm one are claimed as formalized; neither a sharp transpose cb norm nor a sharp universal supremum is required.

## Formalization

Lean uses literal complex matrices and Mathlib Matrix.L2OpNorm from Euclidean continuous linear maps. The transpose is an actual complex continuous linear map. Its amplification applies it to each genuine M8 block at every natural matrix size. A 64-term matrix-unit sandwich identity proves a uniform all-size upper bound. The literal swap matrix, unitarity, nonzero Euclidean witness and matrix-vector equation prove the lower bound. cbNorm is an actual nonempty bounded real sSup, cbRatios restricts to nonzero completely bounded maps, and the final theorem directly negates IsLUB at sqrt(2). Exact integer Python witness checks are supplementary, with no numerical norm oracle.

## Reproduction

Inside lean/: `lake exe cache get`, `lake build`, and
`lake env lean -DwarningAsError=true Main.lean`.
Lean 4.19.0 and Mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b are pinned.
Run `python verify.py` (standard library only) and `tectonic main.tex`.
The exact bilingual source, provenance, actual fresh-build logs, axiom audit,
artifact hashes and all-page PDF review are included. An author agent performed
a self-review; the parent separately reviewed the complete proof and final
artifacts. No external independent review or novelty of the transpose example
is claimed. The standard definitions and background appear in Paulsen's
Operator Algebra Methods in QIT (Winter 2020), p.22, linked in the paper.
