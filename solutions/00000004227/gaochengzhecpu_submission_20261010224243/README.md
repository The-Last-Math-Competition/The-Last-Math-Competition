# Disproof of Conjecture 00000004227

The flag complex of K3 is a filled triangle with exactly one spanning 2-tree. Its clique number is 3 and its chromatic polynomial is q(q-1)(q-2), so the specified negative evaluation gives -6, not 1. Absolute-value or parity correction gives 6, and the opposite positive argument gives 0; neither equals the tree count. In fact every negative integer evaluation has absolute value at least 6.

## Scope

This refutes the stated unit conversion from a flag-complex 2-tree count to the chromatic-polynomial evaluation at the negative point determined by clique number minus two. The example has dimension exactly 2. Its unique tree has trivial integral first homology, so ordinary counting and the usual squared torsion-order weighting both give 1. The proof covers sign conventions and all negative integer points; it does not posit an unspecified linear combination of evaluations or a different normalization.

## Formalization

Lean constructs the actual complete SimpleGraph on three vertices, its clique complex and clique number. An equivalence between proper colorings and embeddings proves the polynomial counting property for every natural number of colors, and polynomial uniqueness is also proved. Actual simplicial boundary maps over Q define the supported-chain spanning 2-tree predicate; Lean classifies all face selections and proves its count is 1. It proves the prescribed evaluation is -6, the positive-point and absolute-value comparisons, and the stronger inequality at every negative integer. The direct integer filling establishing trivial torsion is explained on paper, separately from the Q-linear formalization.

The chromatic polynomial is characterized by its exact counting property and
uniqueness; no general graph-polynomial library is asserted to be available.
The chain-level method follows the author's earlier local simplicial-tree
work, with this graph, its flag complex, its matrices and its tree classification
proved afresh in this file. No earlier submission is imported.

## Reproduction

In `lean/`, run `lake exe cache get`, `lake build`, and
`lake env lean -DwarningAsError=true Main.lean`.
Lean 4.19.0 and Mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b`
are pinned in portable public-Git project metadata.
Only official dependency caches are reused; the submitted project is built
in a fresh directory without its own old build outputs.
Run `tectonic main.tex` to regenerate the PDF.

`SOURCE.md` preserves the exact bilingual problem. `verification/` contains
the source provenance, actual build logs, hashes and review records.
No auxiliary numerical script is needed. The author performed a separate
adversarial self-review; no independent reviewer or subagent was used.
