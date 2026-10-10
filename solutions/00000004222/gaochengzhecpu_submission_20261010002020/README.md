# Disproof of Conjecture 00000004222

The tetrahedral boundary has exactly four spanning 2-trees, each obtained by deleting one triangular face. Its actual 4 by 4 top Laplacian is B2 transpose times B2; every monic degree-four characteristic polynomial has fourth derivative 24, so the prescribed value at 1 differs from the count 4. For the alternate 6 by 6 up-down Laplacian B2 times B2 transpose, the paper computes the fourth derivative as 72, also unequal to 4.

## Scope

Disproof of the stated equality between a simplicial spanning-tree count and the ordinary face-count-order derivative at 1 of the characteristic polynomial of the top-dimensional combinatorial Laplacian. The example has dimension 2, four faces, and no torsion weights. A supplementary paper calculation covers the common up-down Laplacian on edges as well; reduced or rescaled formulas are not the stated claim.

## Formal correspondence

Lean constructs the downward-closed tetrahedral face family, enumerates its actual oriented edges and triangles without duplicates, builds their simplicial boundary linear maps over Q, proves the kernel is the full-support fundamental cycle and provides actual fillings of every 1-cycle. Its supported-chain tree predicate is proved equivalent to omitting exactly one face and is counted as 4. The characteristic polynomial is Matrix.charpoly of the actual B2 transpose times B2; its face-count-order derivative at 1 is proved to be 24. The paper separately explains integral fillings and the resulting trivial torsion weights.

The paper includes a direct proof that all four trees have zero integral H1,
so ordinary counting and the usual squared torsion-order weighting agree.

## Reproduce

The project is self-contained and pins Lean 4.19.0 and Mathlib commit
`c44e0c8ee63ca166450922a373c7409c5d26b00b`.
From `lean/` run:

```text
lake exe cache get
lake build
lake env lean -DwarningAsError=true Main.lean
```

The cache command is needed only when official pinned dependencies are absent.
The submission itself is built in a fresh directory without its own old build outputs.
The standard axioms are `propext`, `Classical.choice`, and `Quot.sound` only.
There are no proof placeholders, added axioms, or numerical oracles.
Run `tectonic main.tex` to reproduce the PDF. No auxiliary numerical scripts are required.

`SOURCE.md` is the exact bilingual conjecture. `main.tex` and `main.pdf` contain
the complete paper. `verification/` contains source provenance, actual build
logs and hashes, native compilation evidence, visual PDF review, and author
self-review. The parent agent supplies the final internal adversarial review.
