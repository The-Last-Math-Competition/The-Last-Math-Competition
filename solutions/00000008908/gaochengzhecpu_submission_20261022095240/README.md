# Disproof of Conjecture 00000008908

The actual simple five-cycle has independence number and complement clique number both equal to two, but the full standard Lovasz theta SDP is at least 5041/2257>2. An explicit rational Gram certificate disproves the monotone chain with the endpoints named in the English source.

## Scope

Refutes the English source's explicit clique-number-of-the-complement endpoint. It does not refute the standard valid sandwich with the chromatic number of the complement, and does not claim that the rational certificate is optimal or that the exact theta value sqrt(5) is formalized.

## Formalization

Lean defines theta as the actual real supremum over ALL real PSD trace-one edge-zero matrices. It proves this feasible set nonempty and bounds every feasible objective by five via quadratic tests on basis-vector differences. The exact circulant integer Gram factor certifies feasibility and the strict rational lower bound. Actual Mathlib cycleGraph 5, its complement, maximum clique number and independence number are used, with ordinary kernel finite certificates. The supplementary exact-arithmetic script reconstructs the Gram matrix and enumerates graph cliques; it is not a Lean oracle.

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
