# Proof of Conjecture 00000002150

For every finite undirected simple graph, the real nullity of the actual signless Laplacian Q=D+A equals the number of bipartite connected components. The proof constructs a basis consisting of one alternating sign vector on each bipartite component, extended by zero elsewhere. Isolated vertices count; the empty graph is covered.

## Source interpretation

“General graphs” is read in the usual finite undirected simple-graph matrix setting. The undefined phrase “the kernel of the count is an arbitrary bipartite base graph” is addressed concretely by the complete alternating-sign kernel basis. No separate base-graph operation is invented or claimed. Infinite graphs, directed graphs, and loop conventions are outside this statement. Both the paper and the formal universal proposition state the basis interpretation explicitly.

## Formal verification

`Signless.conjecture` proves the complete universally quantified real finite-graph proposition, including nullity and the explicit basis. Lean uses Mathlib `SimpleGraph`, `ConnectedComponent`, induced graphs, proper two-colorings, adjacency/degree matrices, `LinearMap.ker`, `Basis`, and `Module.finrank`. All mathematical steps for this theorem are checked. The optional complex-field extension is stated only on paper.

The strict development check is recorded in `verification/STRICT_CHECK.log`. It treats warnings as errors and prints axioms for the principal results; only `propext`, `Classical.choice`, and `Quot.sound` occur. The coordinating agent performs the separate fresh build and PDF verification.

## Reproduction

Lean 4.19.0 and Mathlib commit c44e0c8ee63ca166450922a373c7409c5d26b00b are pinned in `lean/`. From that directory, obtain the pinned Mathlib dependencies/cache, run `lake build`, then `lake env lean -DwarningAsError=true Main.lean`. Compile `main.tex` with Tectonic.

Developed by a delegated AI agent with a self-review; the coordinating agent reviews it separately. No external independent review is claimed.
