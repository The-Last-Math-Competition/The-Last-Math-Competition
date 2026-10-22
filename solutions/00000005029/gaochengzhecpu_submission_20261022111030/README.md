# Disproof of Conjecture 00000005029

For every n=3h>=3, the actual Erdos-Renyi graph G(n,1/n) contains a triangle with probability at least 1/50. Thus its triangle-free first-order forest axiom has probability at most 49/50 along an unbounded sequence and cannot belong to the asserted almost-sure forest limiting theory.

## Scope

Refutes the critical forest-theory clause using a single necessary first-order sentence. No infinite conjunction of cycle exclusions is exchanged with a limit. A separate genuine Mathlib forest-event bound is also proved. No claim is made about the supercritical giant-component clause or nonexistence of a probabilistic first-order convergence law.

## Formalization

The actual graph PMF is a uniform-coordinate pushforward to genuine simple graphs. Every finite actual nonloop present/absent edge pattern is proved to have the independent Bernoulli(1/vertex-count) product mass. Genuine selected triangle events, exact five/six-edge unions and ordered overlap counts give an all-size positive lower bound by a proved ordered-pair Bonferroni inequality. An actual cyclic walk connects triangles to Mathlib non-acyclicity. Vertex counts tend to infinity, while both the literal three-adjacency sentence and actual forest probabilities fail to tend to one. The graph semantics of the displayed first-order sentence are formalized, not separate logical syntax. An independently developed exact verifier enumerates all graphs on three/six vertices with their true masses and all selected overlaps for block sizes one through eight.

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
