# Clique-tree embedding product count counterexample

The actual complete graph K2 has two perfect elimination orderings, while its unique maximal-clique tree has one vertex and one combinatorial planar embedding. The source's embedding-count product is therefore 1, contradicting the true count 2. The report states the embedding equivalence convention and does not assume additional vertex-order factors.

Lean verifies actual graph chordality, the successor-neighbor PEO condition and permutation count, unique maximal clique, unique one-vertex clique graph, empty incident-neighbor rotation systems and their count, and the resulting count mismatch.

Reproduce using Lean 4.19.0: lake update then lake build inside lean. Public Mathlib pin: c44e0c8ee63ca166450922a373c7409c5d26b00b. Final theorem audits are printed. No sorry/admit/native_decide/custom axioms/unsafe; ignored local package junctions are conveniences only.
